(** Mode lattice as described in tex/mox.tex, factored through reusable axis helpers. *)

module type AXIS_SPEC = sig
  type t

  val order_to : t list
  (** Increasing order for the conversion relation [\leqto]. *)

  val order_in : t list
  (** Increasing order for the in-placement relation [\leqin]. *)

  val default : t
  val show : t -> string
  val equal : t -> t -> bool
end

module Make_axis (Spec : AXIS_SPEC) = struct
  type t = Spec.t

  let all = Spec.order_to
  let default = Spec.default
  let equal = Spec.equal

  let rank order value =
    let rec loop idx = function
      | [] -> invalid_arg "Make_axis.rank: value not found in axis"
      | x :: xs -> if Spec.equal value x then idx else loop (idx + 1) xs
    in
    loop 0 order

  let leq order a b = rank order a <= rank order b
  let join order a b = if rank order a >= rank order b then a else b
  let meet order a b = if rank order a <= rank order b then a else b

  let leq_to = leq Spec.order_to
  let leq_in = leq Spec.order_in

  let join_to = join Spec.order_to
  let meet_to = meet Spec.order_to

  let join_in = join Spec.order_in
  let meet_in = meet Spec.order_in

  let to_string = Spec.show
  let to_short_string value = if Spec.equal value Spec.default then "" else Spec.show value

  let of_string name =
    List.find_opt (fun v -> String.equal (Spec.show v) name) Spec.order_to

  let extract names =
    let rec aux seen acc = function
      | [] -> (seen, List.rev acc)
      | candidate :: rest -> (
          match of_string candidate with
          | Some value ->
              if Option.is_some seen then
                invalid_arg
                  (Printf.sprintf "Mode %s provided multiple times" (Spec.show value));
              aux (Some value) acc rest
          | None -> aux seen (candidate :: acc) rest)
    in
    match aux None [] names with
    | Some value, remaining -> (value, remaining)
    | None, remaining -> (Spec.default, remaining)
end

module Uniqueness_spec = struct
  type t = Unique | Aliased

  let order_to = [ Unique; Aliased ]
  let order_in = [ Aliased; Unique ]
  let default = Aliased
  let show = function Unique -> "unique" | Aliased -> "aliased"
  let equal = ( = )
end

module Uniqueness = Make_axis (Uniqueness_spec)

module Contention_spec = struct
  type t = Uncontended | Shared | Contended

  let order_to = [ Uncontended; Shared; Contended ]
  let order_in = [ Contended; Shared; Uncontended ]
  let default = Uncontended
  let show = function
    | Uncontended -> "uncontended"
    | Shared -> "shared"
    | Contended -> "contended"
  let equal = ( = )
end

module Contention = Make_axis (Contention_spec)

module Linearity_spec = struct
  type t = Many | Once

  let order_to = [ Many; Once ]
  let order_in = order_to
  let default = Many
  let show = function Many -> "many" | Once -> "once"
  let equal = ( = )
end

module Linearity = Make_axis (Linearity_spec)

module Portability_spec = struct
  type t = Portable | NonPortable

  let order_to = [ Portable; NonPortable ]
  let order_in = order_to
  let default = NonPortable
  let show = function Portable -> "portable" | NonPortable -> "non-portable"
  let equal = ( = )
end

module Portability = Make_axis (Portability_spec)

module Areality_spec = struct
  type t = Global | Regional | Local

  let order_to = [ Global; Regional; Local ]
  let order_in = order_to
  let default = Global
  let show = function Global -> "global" | Regional -> "regional" | Local -> "local"
  let equal = ( = )
end

module Areality = Make_axis (Areality_spec)

let concat parts =
  parts |> List.filter (fun s -> s <> "") |> String.concat " "

module Past = struct
  type t = { uniqueness : Uniqueness.t; contention : Contention.t }

  let default =
    { uniqueness = Uniqueness.default; contention = Contention.default }

  let make ~uniqueness ~contention = { uniqueness; contention }

  let leq_to a b =
    Uniqueness.leq_to a.uniqueness b.uniqueness
    && Contention.leq_to a.contention b.contention

  let leq_in a b =
    Uniqueness.leq_in a.uniqueness b.uniqueness
    && Contention.leq_in a.contention b.contention

  let join_to a b =
    { uniqueness = Uniqueness.join_to a.uniqueness b.uniqueness;
      contention = Contention.join_to a.contention b.contention }

  let meet_to a b =
    { uniqueness = Uniqueness.meet_to a.uniqueness b.uniqueness;
      contention = Contention.meet_to a.contention b.contention }

  let meet_in a b =
    { uniqueness = Uniqueness.meet_in a.uniqueness b.uniqueness;
      contention = Contention.meet_in a.contention b.contention }

  let join_in a b =
    { uniqueness = Uniqueness.join_in a.uniqueness b.uniqueness;
      contention = Contention.join_in a.contention b.contention }

  let extract names =
    let uniqueness, names = Uniqueness.extract names in
    let contention, names = Contention.extract names in
    ({ uniqueness; contention }, names)

  let to_string t =
    concat
      [ Uniqueness.to_short_string t.uniqueness;
        Contention.to_short_string t.contention ]
end

module Future = struct
  type t =
    { linearity : Linearity.t;
      portability : Portability.t;
      areality : Areality.t }

  let default =
    { linearity = Linearity.default;
      portability = Portability.default;
      areality = Areality.default }

  let make ~linearity ~portability ~areality = { linearity; portability; areality }

  let leq_to a b =
    Linearity.leq_to a.linearity b.linearity
    && Portability.leq_to a.portability b.portability
    && Areality.leq_to a.areality b.areality

  let leq_in = leq_to

  let join_to a b =
    { linearity = Linearity.join_to a.linearity b.linearity;
      portability = Portability.join_to a.portability b.portability;
      areality = Areality.join_to a.areality b.areality }

  let meet_to a b =
    { linearity = Linearity.meet_to a.linearity b.linearity;
      portability = Portability.meet_to a.portability b.portability;
      areality = Areality.meet_to a.areality b.areality }

  let meet_in a b =
    { linearity = Linearity.meet_in a.linearity b.linearity;
      portability = Portability.meet_in a.portability b.portability;
      areality = Areality.meet_in a.areality b.areality }

  let join_in a b =
    { linearity = Linearity.join_in a.linearity b.linearity;
      portability = Portability.join_in a.portability b.portability;
      areality = Areality.join_in a.areality b.areality }

  let extract names =
    let areality, names = Areality.extract names in
    let linearity, names = Linearity.extract names in
    let portability, names = Portability.extract names in
    ({ areality; linearity; portability }, names)

  let to_string t =
    concat
      [ Areality.to_short_string t.areality;
        Linearity.to_short_string t.linearity;
        Portability.to_short_string t.portability ]
end

module Mode = struct
  type t = { past : Past.t; future : Future.t }

  let default = { past = Past.default; future = Future.default }

  let make ~past ~future = { past; future }

  let leq_to a b = Past.leq_to a.past b.past && Future.leq_to a.future b.future
  let leq_in a b = Past.leq_in a.past b.past && Future.leq_in a.future b.future

  let join_to a b =
    { past = Past.join_to a.past b.past; future = Future.join_to a.future b.future }

  let meet_to a b =
    { past = Past.meet_to a.past b.past; future = Future.meet_to a.future b.future }

  let meet_in a b =
    { past = Past.meet_in a.past b.past; future = Future.meet_in a.future b.future }

  let join_in a b =
    { past = Past.join_in a.past b.past; future = Future.join_in a.future b.future }

  let extract names =
    let past, names = Past.extract names in
    let future, names = Future.extract names in
    ({ past; future }, names)

  let of_strings names =
    let mode, remaining = extract names in
    if remaining = [] then mode
    else
      invalid_arg
        (Printf.sprintf "Unrecognised mode names: %s"
           (String.concat ", " remaining))
  let to_string t = concat [ Past.to_string t.past; Future.to_string t.future ]
end
