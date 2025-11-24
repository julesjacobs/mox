module Solver = struct
  (* ======================================================================= *)
  (* 1. SAFE ARITHMETIC                                                      *)
  (* ======================================================================= *)

  type contradiction =
    { var : string;
      lower : int;
      upper : int;
      lower_repr : string;
      upper_repr : string }
  exception Contradiction of contradiction

  let infinity = max_int
  let safe_max = max_int - (1 lsl 60) 
  let string_of_value v = if v = infinity then "inf" else string_of_int v

  (* Robust Addition: a + b *)
  let safe_add a b =
    if a = infinity || b = infinity then infinity
    else 
      let res = a + b in
      (* Check overflow or safety buffer *)
      if (b > 0 && res < a) || res > safe_max then infinity
      (* Check underflow (domain floor logic not needed inside matrix, 
         matrix stores relative diffs, which can be negative) *)
      else res

  (* ======================================================================= *)
  (* 2. STATE: The Transitive Closure Matrix                                 *)
  (* ======================================================================= *)

  type var_id = int

  (* We use a Hashtbl of Hashtbls for a sparse matrix representation.
     dist[i][j] stores the max weight path from i to j. *)
  type matrix = (var_id, (var_id, int) Hashtbl.t) Hashtbl.t

  type t = {
    dist : matrix;
    uppers : (var_id, int) Hashtbl.t; (* Static Upper Bounds *)
    names : (var_id, string) Hashtbl.t; (* Debugging names *)
    mutable nodes : var_id list;      (* List of all active variable IDs *)
  }

  (* The Global Solver State *)
  let st = {
    dist = Hashtbl.create 16;
    uppers = Hashtbl.create 16;
    names = Hashtbl.create 16;
    nodes = [0]; (* 0 is the Source Node (The Universe Zero) *)
  }

  let reset () =
    Hashtbl.clear st.dist;
    Hashtbl.clear st.uppers;
    Hashtbl.clear st.names;
    st.nodes <- [0];
    (* Initialize Source: Dist[0][0] = 0 *)
    let row0 = Hashtbl.create 16 in
    Hashtbl.add row0 0 0;
    Hashtbl.add st.dist 0 row0

  (* Matrix Accessors *)
  let get_dist u v =
    match Hashtbl.find_opt st.dist u with
    | None -> None
    | Some row -> Hashtbl.find_opt row v

  let set_dist u v w =
    let row = match Hashtbl.find_opt st.dist u with
      | Some r -> r
      | None -> 
          let r = Hashtbl.create 16 in
          Hashtbl.add st.dist u r;
          r
    in
    Hashtbl.replace row v w

  (* ======================================================================= *)
  (* 3. VARIABLE CREATION                                                    *)
  (* ======================================================================= *)

  type var = { id : var_id }
  let next_id = let c = ref 0 in fun () -> incr c; !c

  let var_name v_id =
    match Hashtbl.find_opt st.names v_id with
    | Some n -> n
    | None -> Printf.sprintf "v%d" v_id

  let create_var ?name () =
    let id = next_id () in
    let name = match name with Some n -> n | None -> Printf.sprintf "v%d" id in
    st.nodes <- id :: st.nodes;
    Hashtbl.add st.uppers id infinity;
    Hashtbl.add st.names id name;
    
    (* Initialize Self-Distance to 0 *)
    set_dist id id 0;
    
    (* Implicit: Lower bound 0. Edge Source(0) -> v weight 0 *)
    set_dist 0 id 0; 
    
    { id }

  (* ======================================================================= *)
  (* 4. THE CORE: INCREMENTAL FLOYD-WARSHALL                                 *)
  (* ======================================================================= *)

  (* Check consistency for a specific node 'v' *)
  let check_bounds v_id =
    let lb = match get_dist 0 v_id with Some w -> w | None -> 0 in
    let ub = Hashtbl.find st.uppers v_id in
    if lb > ub then
      raise
        (Contradiction
           { var = var_name v_id;
             lower = lb;
             upper = ub;
             lower_repr = string_of_value lb;
             upper_repr = string_of_value ub })

  (* Add edge u -> v with weight w *)
  (* This implies v >= u + w *)
  let add_constraint u_id v_id w =
    (* 1. Check if this constraint is weaker than what we already know *)
    let current = match get_dist u_id v_id with Some d -> d | None -> min_int in
    
    (* If new weight w is not stronger, do nothing. *)
    if w > current then begin
      
      (* 2. Double Loop Update: O(V^2) *)
      (* For every node i that can reach u... *)
      (* For every node j that is reachable from v... *)
      (* Update i -> j using i -> u -> v -> j *)

      (* Iterate all known start nodes i *)
      List.iter (fun i ->
        match get_dist i u_id with
        | None -> () (* No path i -> u, so u->v doesn't help i *)
        | Some d_iu ->
            (* Iterate all known end nodes j *)
            List.iter (fun j ->
              match get_dist v_id j with
              | None -> () (* No path v -> j *)
              | Some d_vj -> 
                  
                  (* Calculate new path weight: i -> u -> v -> j *)
                  let new_dist = safe_add (safe_add d_iu w) d_vj in
                  
                  (* Existing distance *)
                  let current_dist = match get_dist i j with Some d -> d | None -> min_int in
                  
                  if new_dist > current_dist then begin
                    set_dist i j new_dist;

                    (* 3. Positive Cycle Detection *)
                    (* If we just updated a diagonal d[k][k] > 0, set to Infinity *)
                    if i = j && new_dist > 0 then 
                       set_dist i i infinity;
                       
                    (* 4. Check Consistency (only if we updated a lower bound from 0) *)
                    if i = 0 then check_bounds j;
                  end
            ) st.nodes
      ) st.nodes
    end

  (* ======================================================================= *)
  (* 5. PUBLIC API                                                           *)
  (* ======================================================================= *)

  let assert_leq x y =
    (* x <= y  <==>  y >= x + 0 *)
    add_constraint x.id y.id 0

  let decrease_by x delta y =
    add_constraint x.id y.id delta

  let increase_by x delta y =
    add_constraint x.id y.id (-delta)

  let assert_eq_const x k =
    (* 1. Tighten Static Upper Bound *)
    let current_ub = Hashtbl.find st.uppers x.id in
    if k < current_ub then Hashtbl.replace st.uppers x.id k;
    
    (* Consistency check immediate *)
    check_bounds x.id;

    (* 2. Tighten Lower Bound: Source(0) -> x weight k *)
    add_constraint 0 x.id k

  let assert_predecessor x y =
    
    (* y = x - 1 *)
    
    (* 1. Graph: y >= x - 1 ==> x -> y weight -1 *)
    add_constraint x.id y.id (-1);
    
    (* 2. Graph: x >= y + 1 ==> y -> x weight 1 *)
    add_constraint y.id x.id 1
    
    (* Note: Because we have initial edge 0->x (0) and 0->y (0),
       adding y->x (1) computes 0->y->x = 0+1 = 1.
       So 0->x updates to 1. x>=1 is enforced automatically. *)

  (* Inspection *)
  let get_lower x = 
    match get_dist 0 x.id with Some w -> w | None -> 0

  let implied_upper v_id =
    let base = Hashtbl.find st.uppers v_id in
    match Hashtbl.find_opt st.dist v_id with
    | None -> base
    | Some row ->
        Hashtbl.fold
          (fun target weight acc ->
            let target_upper = Hashtbl.find st.uppers target in
            let candidate =
              if target_upper = infinity then infinity else target_upper - weight
            in
            if candidate < acc then candidate else acc)
          row base

  let get_diff_bounds x y =
    let lower =
      match get_dist x.id y.id with Some w -> w | None -> min_int
    in
    let upper_from_backedge =
      match get_dist y.id x.id with
      | Some w -> Some (-w)
      | None -> None
    in
    let upper_from_global =
      let upper_y = implied_upper y.id in
      if upper_y = infinity then None
      else
        let lower_x = get_lower x in
        Some (upper_y - lower_x)
    in
    let upper =
      match (upper_from_backedge, upper_from_global) with
      | Some u1, Some u2 -> Some (min u1 u2)
      | Some u, None | None, Some u -> Some u
      | None, None -> None
    in
    (lower, upper)

  let get_upper x = 
    implied_upper x.id

  let print_model () =
    Printf.printf "\n--- Transitive Closure Solver ---\n";
    List.iter (fun i ->
      if i <> 0 then
        let lb = match get_dist 0 i with Some w -> if w=infinity then "+oo" else string_of_int w | None -> "0" in
        let ub = let u = implied_upper i in if u=infinity then "+oo" else string_of_int u in
        Printf.printf "%s: [%s, %s]\n" (var_name i) lb ub
    ) (List.rev st.nodes)

end

include Solver
