open Modes

exception Inconsistent of string

type 'a var = {
  encode : 'a -> int;
  decode : int -> 'a;
  id : Intsolver.var;
  axis_name : string;
}

type 'a mode_var = 'a var

let lift ?context f =
  try f () with
  | Intsolver.Inconsistent msg ->
      let detail =
        match context with
        | Some axis -> Printf.sprintf "%s inconsistency" axis
        | None -> msg
      in
      raise (Inconsistent detail)

let sanitize_domain domain encode =
  domain
  |> List.map encode
  |> List.sort_uniq compare

let new_var_internal ~axis_name ~encode ~decode ~domain =
  let ints = sanitize_domain domain encode in
  if ints = [] then invalid_arg "Modesolver.new_var: empty domain"
  else
    let id = lift ~context:axis_name (fun () -> Intsolver.newvar ints) in
    { encode; decode; id; axis_name }

let encode_relation var_a var_b rel =
  rel
  |> Relations.to_list
  |> List.map (fun (a, b) -> (var_a.encode a, var_b.encode b))
  |> Relations.make

let relation_context var_a var_b =
  if String.equal var_a.axis_name var_b.axis_name then
    var_a.axis_name
  else
    Printf.sprintf "%s/%s" var_a.axis_name var_b.axis_name

let assert_relation_generic rel var_a var_b =
  let encoded = encode_relation var_a var_b rel in
  let context = relation_context var_a var_b in
  lift ~context (fun () -> Intsolver.assert_rel encoded var_a.id var_b.id)

let get_relation_generic var_a var_b =
  lift (fun () -> Intsolver.get_rel var_a.id var_b.id)
  |> Relations.to_list
  |> List.map (fun (a, b) -> (var_a.decode a, var_b.decode b))
  |> Relations.make

let assert_predicate_generic rel var = assert_relation_generic rel var var

let restrict_domain_generic domain var =
  let ints = sanitize_domain domain var.encode in
  if ints = [] then
    raise
      (Inconsistent
         (Printf.sprintf "%s empty domain restriction" var.axis_name));
  let values = List.map var.decode ints in
  let diag =
    values
    |> List.map (fun v -> (v, v))
    |> Relations.make
  in
  assert_predicate_generic diag var

let new_var ~encode ~decode ~domain =
  new_var_internal ~axis_name:"mode" ~encode ~decode ~domain
let id var = var.id
let int_id_tbl : (Intsolver.var, int) Hashtbl.t = Hashtbl.create 32
let int_id_counter = ref 0

let int_id (type a) (var : a mode_var) : int =
  match Hashtbl.find_opt int_id_tbl var.id with
  | Some n -> n
  | None ->
      incr int_id_counter;
      let n = !int_id_counter in
      Hashtbl.add int_id_tbl var.id n;
      n
let assert_relation = assert_relation_generic
let get_relation = get_relation_generic
let assert_predicate = assert_predicate_generic
let restrict_domain = restrict_domain_generic
let get_domain var =
  get_relation_generic var var
  |> Relations.to_list
  |> List.filter_map (fun (a, b) -> if a = b then Some a else None)
  |> List.sort_uniq compare
let describe_var show var =
  let rel = get_relation_generic var var in
  let values =
    rel
    |> Relations.to_list
    |> List.filter_map (fun (a, b) -> if a = b then Some (show a) else None)
    |> List.sort_uniq String.compare
  in
  match values with
  | [] -> "<unsat>"
  | [ single ] -> single
  | vs -> Printf.sprintf "{%s}" (String.concat ", " vs)

let linearity_uniqueness_dagger_relation =
  Relations.make
    [ (Modes.Linearity.many, Modes.Uniqueness.aliased);
      (Modes.Linearity.once, Modes.Uniqueness.unique);
      (Modes.Linearity.once, Modes.Uniqueness.aliased) ]

let portability_contention_dagger_relation =
  Relations.make
    [ (Modes.Portability.nonportable, Modes.Contention.uncontended);
      (Modes.Portability.nonportable, Modes.Contention.shared);
      (Modes.Portability.nonportable, Modes.Contention.contended);
      (Modes.Portability.portable, Modes.Contention.contended) ]

let assert_linearity_dagger lin_var uniq_var =
  assert_relation linearity_uniqueness_dagger_relation lin_var uniq_var

let assert_portability_dagger port_var cont_var =
  assert_relation portability_contention_dagger_relation port_var cont_var

let ref_writable_relation =
  Relations.make
    [ (Modes.Contention.uncontended, Modes.Uniqueness.unique);
      (Modes.Contention.uncontended, Modes.Uniqueness.aliased);
      (Modes.Contention.shared, Modes.Uniqueness.unique);
      (Modes.Contention.contended, Modes.Uniqueness.unique) ]

let ref_readable_relation =
  Relations.make
    [ (Modes.Contention.uncontended, Modes.Uniqueness.unique);
      (Modes.Contention.uncontended, Modes.Uniqueness.aliased);
      (Modes.Contention.shared, Modes.Uniqueness.unique);
      (Modes.Contention.shared, Modes.Uniqueness.aliased);
      (Modes.Contention.contended, Modes.Uniqueness.unique) ]

let assert_ref_writable cont_var uniq_var =
  assert_relation ref_writable_relation cont_var uniq_var

let assert_ref_readable cont_var uniq_var =
  assert_relation ref_readable_relation cont_var uniq_var

let borrow_uniqueness_relation =
  Relations.make
    [ (Modes.Uniqueness.unique, Modes.Uniqueness.aliased);
      (Modes.Uniqueness.aliased, Modes.Uniqueness.aliased) ]

let borrow_uniqueness_areality_relation =
  Relations.make
    [ (Modes.Uniqueness.unique, Modes.Areality.borrowed);
      (Modes.Uniqueness.aliased, Modes.Areality.global);
      (Modes.Uniqueness.aliased, Modes.Areality.borrowed) ]

let assert_borrow_uniqueness src dst =
  assert_relation borrow_uniqueness_relation src dst

let assert_borrow_areality uniq_var are_var =
  assert_relation borrow_uniqueness_areality_relation uniq_var are_var

module type AXIS = sig
  type t

  val axis_name : string
  val all : t list
  val equal : t -> t -> bool
  val leq_to : t -> t -> bool
  val leq_in : t -> t -> bool
  val bottom_in : t
end

let relation_from order predicate =
  order
  |> List.map (fun a ->
         order
         |> List.filter_map (fun b -> if predicate a b then Some (a, b) else None))
  |> List.concat
  |> Relations.make

let codec_from_values values equal =
  let arr = Array.of_list values in
  let encode value =
    let rec loop idx =
      if idx >= Array.length arr then
        invalid_arg "Modesolver.encode: value not found"
      else if equal arr.(idx) value then idx
      else loop (idx + 1)
    in
    loop 0
  in
  let decode idx =
    if idx < 0 || idx >= Array.length arr then
      invalid_arg "Modesolver.decode: index out of bounds"
    else arr.(idx)
  in
  encode, decode

module type AXIS_SOLVER = sig
  type mode
  type var = mode mode_var
  type relation = (mode, mode) Relations.t

  val relation_to : relation
  val relation_in : relation

  val new_var : ?domain:mode list -> unit -> var
  val assert_relation : relation -> var -> var -> unit
  val assert_leq_to : var -> var -> unit
  val assert_leq_in : var -> var -> unit
  val assert_predicate : relation -> var -> unit
  val restrict_domain : mode list -> var -> unit
  val get_relation : var -> var -> relation
  val join_to : var -> var -> var
  val bottom_in : var
end

module Make (A : AXIS) : AXIS_SOLVER with type mode = A.t = struct
  type mode = A.t
  type var = mode mode_var
  type relation = (mode, mode) Relations.t

  let values = A.all
  let encode, decode = codec_from_values values A.equal
  let relation_to = relation_from values A.leq_to
  let relation_in = relation_from values A.leq_in

  let new_var ?domain () =
    let domain = match domain with Some d -> d | None -> values in
    new_var_internal ~axis_name:A.axis_name ~encode ~decode ~domain

  let assert_relation rel v1 v2 = assert_relation_generic rel v1 v2
  let assert_leq_to v1 v2 = assert_relation relation_to v1 v2
  let assert_leq_in v1 v2 = assert_relation relation_in v1 v2
  let assert_predicate rel v = assert_predicate_generic rel v
  let restrict_domain domain v = restrict_domain_generic domain v
  let get_relation v1 v2 = get_relation_generic v1 v2
  let join_to v1 v2 =
    let z = new_var () in
    assert_leq_to v1 z;
    assert_leq_to v2 z;
    z
  let bottom_in = new_var ~domain:[A.bottom_in] ()
end

module Uniqueness = Make (struct
  type t = Modes.Uniqueness.t

  let axis_name = "uniqueness"
  let all = Modes.Uniqueness.all
  let equal = Modes.Uniqueness.equal
  let leq_to = Modes.Uniqueness.leq_to
  let leq_in = Modes.Uniqueness.leq_in
  let bottom_in = Modes.Uniqueness.bottom_in
end)

module Contention = Make (struct
  type t = Modes.Contention.t

  let axis_name = "contention"
  let all = Modes.Contention.all
  let equal = Modes.Contention.equal
  let leq_to = Modes.Contention.leq_to
  let leq_in = Modes.Contention.leq_in
  let bottom_in = Modes.Contention.bottom_in
end)

module Linearity = Make (struct
  type t = Modes.Linearity.t

  let axis_name = "linearity"
  let all = Modes.Linearity.all
  let equal = Modes.Linearity.equal
  let leq_to = Modes.Linearity.leq_to
  let leq_in = Modes.Linearity.leq_in
  let bottom_in = Modes.Linearity.bottom_in
end)

module Portability = Make (struct
  type t = Modes.Portability.t

  let axis_name = "portability"
  let all = Modes.Portability.all
  let equal = Modes.Portability.equal
  let leq_to = Modes.Portability.leq_to
  let leq_in = Modes.Portability.leq_in
  let bottom_in = Modes.Portability.bottom_in
end)

module Areality = Make (struct
  type t = Modes.Areality.t

  let axis_name = "areality"
  let all = Modes.Areality.all
  let equal = Modes.Areality.equal
  let leq_to = Modes.Areality.leq_to
  let leq_in = Modes.Areality.leq_in
  let bottom_in = Modes.Areality.bottom_in
end)

module Regionality = struct
  type mode = Modes.Regionality.t
  type var = Infsolver.var

  let axis_name = "regionality"
  let id_table : (var, int) Hashtbl.t = Hashtbl.create 32
  let id_counter = ref 0
  let to_int = function
    | Modes.Regionality.Infty -> Infsolver.infinity
    | Modes.Regionality.Region n -> n

  let id (v : var) =
    match Hashtbl.find_opt id_table v with
    | Some n -> n
    | None ->
        incr id_counter;
        let n = !id_counter in
        Hashtbl.add id_table v n;
        n

  let lift f =
    try f () with
    | Infsolver.Contradiction { lower_repr; upper_repr; _ } ->
        let detail =
          Printf.sprintf "regionality inconsistency (%s <= %s)"
            lower_repr upper_repr
        in
        raise (Inconsistent detail)

  let restrict_to_single domain v =
    match domain with
    | [] ->
        raise
          (Inconsistent
             (Printf.sprintf "%s empty domain restriction" axis_name))
    | [ value ] -> Infsolver.assert_eq_const v (to_int value)
    | _ ->
        invalid_arg "Regionality only supports singleton domain restrictions"

  let new_var ?domain () =
    let v = Infsolver.create_var ~name:axis_name () in
    (match domain with None -> () | Some d -> lift (fun () -> restrict_to_single d v));
    v

  let restrict_domain domain v = lift (fun () -> restrict_to_single domain v)

  let assert_leq_to v1 v2 =
    (* order is reversed arithmetic: r1 <= r2 iff r1 >= r2 *)
    lift (fun () -> Infsolver.assert_leq v2 v1)

  let assert_leq_in = assert_leq_to

  let decrease_by v1 delta v2 =
    (* numeric constraint: region(v2) >= region(v1) + delta *)
    lift (fun () -> Infsolver.decrease_by v1 delta v2)

  let increase_by v1 delta v2 =
    (* numeric constraint: region(v2) >= region(v1) - delta *)
    lift (fun () -> Infsolver.increase_by v1 delta v2)

  let join_to v1 v2 =
    let z = new_var () in
    assert_leq_to v1 z;
    assert_leq_to v2 z;
    z

  let bottom_in = new_var ~domain:[Modes.Regionality.Infty] ()

  let get_bounds v = lift (fun () -> (Infsolver.get_lower v, Infsolver.get_upper v))

  let get_diff_bounds v1 v2 = lift (fun () -> Infsolver.get_diff_bounds v1 v2)
end
