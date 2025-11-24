(* ========================================================================= *)
(* ROBUST GRAPH-BASED INTEGER SOLVER                                         *)
(* Domain: [0, +infinity]                                                    *)
(* Logic:  Dynamic Lower Bounds (Propagation) + Static Upper Bounds (Checks) *)
(* ========================================================================= *)

type value = int
type contradiction = string
exception Contradiction of contradiction

let infinity = max_int
let zero = 0

(* Safety buffer: operations clamp to infinity before actually overflowing.
   We reserve the top ~10^18 values as the "Gravity Well" of infinity. *)
let safe_max = max_int - (1 lsl 60)

(* Robust Addition: current + weight *)
let safe_add (current : value) (weight : int) : value =
  (* Rule 1: Infinity absorbs everything *)
  if current = infinity then infinity
  (* Rule 2: Adding Infinity yields Infinity *)
  else if weight = infinity then infinity
  else
    let res = current + weight in

    (* Rule 3: Overflow / Safety Cap *)
    (* If adding a positive weight pushes us past safe_max or wraps around *)
    if weight > 0 && (res < current || res > safe_max) then infinity

    (* Rule 4: Domain Floor [0, ...) *)
    (* If adding a negative weight pushes below zero, clamp to zero *)
    else if res < zero then zero

    else res

(* ======================================================================= *)
(* INTERNAL STATE                                                          *)
(* ======================================================================= *)

type var_id = int

type edge = {
  target : var_id;
  weight : int;
}

type var = {
  id : var_id;
  name : string;
  mutable lower : value; (* Dynamic: Pushed UP by propagation *)
  mutable upper : value; (* Static: Pushed DOWN by assertions *)
  mutable edges : edge list; (* Outgoing constraints *)
  mutable in_queue : bool; (* Optimization for SPFA *)
}

(* Global Context *)
let vars : (var_id, var) Hashtbl.t = Hashtbl.create 100
let work_queue : var Queue.t = Queue.create ()

let next_id_counter = ref 0
let next_id () =
  incr next_id_counter;
  !next_id_counter

let reset () =
  Hashtbl.clear vars;
  Queue.clear work_queue;
  next_id_counter := 0

let create_var ?name () =
  let vid = next_id () in
  let vname = match name with Some n -> n | None -> "v" ^ string_of_int vid in
  let v =
    {
      id = vid;
      name = vname;
      lower = zero; (* Starts at 0 (Universe Floor) *)
      upper = infinity; (* Starts at +oo (Unconstrained) *)
      edges = [];
      in_queue = false;
    }
  in
  Hashtbl.add vars v.id v;
  v

(* ======================================================================= *)
(* PROPAGATION ENGINE (SPFA Algorithm)                                     *)
(* ======================================================================= *)

let enqueue v =
  if not v.in_queue then (
    Queue.add v work_queue;
    v.in_queue <- true)

(* Check Consistency: Lower <= Upper *)
let check_bounds v =
  if v.lower > v.upper then
    raise
      (Contradiction
         (Printf.sprintf "Variable '%s' Inconsistent: Lower(%d) > Upper(%d)"
            v.name v.lower v.upper))

let rec propagate () =
  if not (Queue.is_empty work_queue) then begin
    let u = Queue.pop work_queue in
    u.in_queue <- false;

    (* Sanity check source before pushing *)
    check_bounds u;

    List.iter
      (fun edge ->
        let v = Hashtbl.find vars edge.target in

        (* Calculate potential new lower bound for neighbor *)
        let candidate = safe_add u.lower edge.weight in

        (* RELAXATION: If we found a strictly greater lower bound *)
        if candidate > v.lower then begin
          v.lower <- candidate;

          (* Immediate Consistency Check *)
          check_bounds v;

          (* Continue Propagation *)
          enqueue v
        end)
      u.edges;

    propagate ()
  end

(* Helper to add graph edges *)
let add_directed_edge u weight v =
  u.edges <- { target = v.id; weight } :: u.edges;
  (* u might immediately force v higher, so queue u *)
  enqueue u;
  propagate ()

(* ======================================================================= *)
(* PUBLIC CONSTRAINT API                                                   *)
(* ======================================================================= *)

(* Constraint: x <= y *)
(* Logic: y >= x + 0. Edge x -> y (weight 0) *)
let assert_leq x y = add_directed_edge x 0 y

(* Constraint: x = k *)
(* Logic:
   1. Upper Bound := k
   2. Lower Bound := max(Lower, k)
*)
let assert_eq_const x k =
  (* 1. Tighten Upper Bound *)
  if x.lower > k then
    raise
      (Contradiction
         (Printf.sprintf "'%s' lower bound %d exceeds new constant %d" x.name
            x.lower k));

  if k < x.upper then x.upper <- k; (* Only tighten, never loosen *)

  (* 2. Tighten Lower Bound *)
  if k > x.lower then begin
    x.lower <- k;
    enqueue x;
    propagate ()
  end

(* Constraint: y = x - 1 (implies x >= 1) *)
(* Logic:
   1. y >= x - 1  ==> Edge x -> y (weight -1)
   2. x >= y + 1  ==> Edge y -> x (weight +1)

   Note: Domain Constraint (x >= 1) is handled automatically.
   Since y >= 0 (universe floor), y -> x (weight 1) pushes x to 1.
*)
let assert_predecessor x y =
  (* x --(-1)--> y *)
  x.edges <- { target = y.id; weight = -1 } :: x.edges;

  (* y --(+1)--> x *)
  y.edges <- { target = x.id; weight = 1 } :: y.edges;

  (* Trigger propagation from both *)
  enqueue x;
  enqueue y;
  propagate ()

(* ======================================================================= *)
(* INTROSPECTION                                                           *)
(* ======================================================================= *)

let get_lower v = v.lower
let get_upper v = v.upper

let fmt_val n = if n = infinity then "+oo" else string_of_int n

let print_model () =
  Printf.printf "\n--- Solver State ---\n";
  Hashtbl.iter
    (fun _ v ->
      Printf.printf "%s: [%s, %s]\n" v.name (fmt_val v.lower) (fmt_val v.upper))
    vars;
  Printf.printf "--------------------\n"
