open Modes

exception Inconsistent of string

type 'a var = {
  encode : 'a -> int;
  decode : int -> 'a;
  id : Intsolver.var;
}

type 'a mode_var = 'a var

let lift f =
  try f () with Intsolver.Inconsistent msg -> raise (Inconsistent msg)

let sanitize_domain domain encode =
  domain
  |> List.map encode
  |> List.sort_uniq compare

let new_var_internal ~encode ~decode ~domain =
  let ints = sanitize_domain domain encode in
  if ints = [] then invalid_arg "Modesolver.new_var: empty domain"
  else
    let id = lift (fun () -> Intsolver.newvar ints) in
    { encode; decode; id }

let encode_relation var_a var_b rel =
  rel
  |> Relations.to_list
  |> List.map (fun (a, b) -> (var_a.encode a, var_b.encode b))
  |> Relations.make

let assert_relation_generic rel var_a var_b =
  let encoded = encode_relation var_a var_b rel in
  lift (fun () -> Intsolver.assert_rel encoded var_a.id var_b.id)

let get_relation_generic var_a var_b =
  lift (fun () -> Intsolver.get_rel var_a.id var_b.id)
  |> Relations.to_list
  |> List.map (fun (a, b) -> (var_a.decode a, var_b.decode b))
  |> Relations.make

let assert_predicate_generic rel var = assert_relation_generic rel var var

let restrict_domain_generic domain var =
  let ints = sanitize_domain domain var.encode in
  if ints = [] then raise (Inconsistent "empty domain restriction");
  let values = List.map var.decode ints in
  let diag =
    values
    |> List.map (fun v -> (v, v))
    |> Relations.make
  in
  assert_predicate_generic diag var

let new_var = new_var_internal
let assert_relation = assert_relation_generic
let get_relation = get_relation_generic
let assert_predicate = assert_predicate_generic
let restrict_domain = restrict_domain_generic

let linearity_uniqueness_dagger_relation =
  Relations.make
    [ (Modes.Linearity.never, Modes.Uniqueness.unique);
      (Modes.Linearity.never, Modes.Uniqueness.aliased);
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

module type AXIS = sig
  type t

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
    new_var_internal ~encode ~decode ~domain

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

  let all = Modes.Uniqueness.all
  let equal = Modes.Uniqueness.equal
  let leq_to = Modes.Uniqueness.leq_to
  let leq_in = Modes.Uniqueness.leq_in
  let bottom_in = Modes.Uniqueness.bottom_in
end)

module Contention = Make (struct
  type t = Modes.Contention.t

  let all = Modes.Contention.all
  let equal = Modes.Contention.equal
  let leq_to = Modes.Contention.leq_to
  let leq_in = Modes.Contention.leq_in
  let bottom_in = Modes.Contention.bottom_in
end)

module Linearity = Make (struct
  type t = Modes.Linearity.t

  let all = Modes.Linearity.all
  let equal = Modes.Linearity.equal
  let leq_to = Modes.Linearity.leq_to
  let leq_in = Modes.Linearity.leq_in
  let bottom_in = Modes.Linearity.bottom_in
end)

module Portability = Make (struct
  type t = Modes.Portability.t

  let all = Modes.Portability.all
  let equal = Modes.Portability.equal
  let leq_to = Modes.Portability.leq_to
  let leq_in = Modes.Portability.leq_in
  let bottom_in = Modes.Portability.bottom_in
end)

module Areality = Make (struct
  type t = Modes.Areality.t

  let all = Modes.Areality.all
  let equal = Modes.Areality.equal
  let leq_to = Modes.Areality.leq_to
  let leq_in = Modes.Areality.leq_in
  let bottom_in = Modes.Areality.bottom_in
end)
