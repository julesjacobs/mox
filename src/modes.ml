(** Mode lattice as described in tex/mox.tex, factored through reusable axis helpers. *)

module type AXIS_SPEC = sig
  type t

  val order_to : t list
  (** Total order for the conversion relation [\leqto]. *)

  val order_in : (t * t) list
  (** Hasse diagram for the in-placement relation [\leqin]. *)

  val default : t
  val show : t -> string
  val equal : t -> t -> bool
end

let linear_order values =
  let rec aux acc = function
    | [] | [ _ ] -> List.rev acc
    | x :: (y :: _ as rest) -> aux ((x, y) :: acc) rest
  in
  aux [] values

module Make_axis (Spec : AXIS_SPEC) = struct
  type t = Spec.t

  let all = Spec.order_to
  let default = Spec.default
  let equal = Spec.equal

  let dedup list =
    let rec aux acc = function
      | [] -> List.rev acc
      | x :: xs ->
          if List.exists (fun y -> Spec.equal x y) acc then aux acc xs
          else aux (x :: acc) xs
    in
    aux [] list

  let add_reflexive relation values =
    List.fold_left
      (fun acc value -> if List.exists (fun (x, y) -> Spec.equal x value && Spec.equal y value) acc then acc else (value, value) :: acc)
      relation values

  let rec reachable relation visited src dst =
    if Spec.equal src dst then true
    else
      let neighbors =
        relation
        |> List.filter_map (fun (a, b) -> if Spec.equal a src then Some b else None)
      in
      List.exists
        (fun next ->
          let already = List.exists (fun v -> Spec.equal v next) visited in
          (not already) && reachable relation (next :: visited) next dst)
        neighbors

  let topo_linear_order values relation =
    let relation = add_reflexive relation values in
    let preds value =
      relation
      |> List.fold_left
           (fun acc (src, dst) -> if Spec.equal dst value && not (Spec.equal src value) then src :: acc else acc)
           []
      |> dedup
    in
    let rec loop acc remaining =
      match remaining with
      | [] -> List.rev acc
      | _ ->
          let rec choose prefix = function
            | [] -> invalid_arg "Make_axis.linear_order: cyclic relation"
            | v :: rest ->
                let all_preds_scheduled =
                  preds v
                  |> List.for_all (fun p -> List.exists (fun scheduled -> Spec.equal scheduled p) acc)
                in
                if all_preds_scheduled then
                  let remaining' = List.rev_append prefix rest in
                  loop (v :: acc) remaining'
                else
                  choose (v :: prefix) rest
          in
          choose [] remaining
    in
    loop [] (dedup values)

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

  let order_in_relation = add_reflexive Spec.order_in all
  let order_in_linear = topo_linear_order all Spec.order_in

  let leq_in a b = reachable order_in_relation [] a b

  let join_to = join Spec.order_to
  let meet_to = meet Spec.order_to

  let join_in = join order_in_linear
  let meet_in = meet order_in_linear

  let bottom order =
    match order with
    | x :: _ -> x
    | [] -> invalid_arg "Make_axis.bottom: empty order"

  let top order =
    let rec last = function
      | [] -> invalid_arg "Make_axis.top: empty order"
      | [ x ] -> x
      | _ :: xs -> last xs
    in
    last order

  let bottom_to = bottom Spec.order_to
  let top_to = top Spec.order_to

  let bottom_in = bottom order_in_linear
  let top_in = top order_in_linear

  let to_string = Spec.show
  let to_short_string value = if Spec.equal value Spec.default then "" else Spec.show value

  let of_string name =
    List.find_opt (fun v -> String.equal (Spec.show v) name) all

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
  let order_in = linear_order [ Aliased; Unique ]
  let default = Aliased
  let show = function Unique -> "unique" | Aliased -> "aliased"
  let equal = ( = )
end

module Uniqueness = struct
  include Make_axis (Uniqueness_spec)
  type nonrec t = Uniqueness_spec.t = Unique | Aliased

  let unique = Unique
  let aliased = Aliased
end

module Contention_spec = struct
  type t = Uncontended | Shared | Contended

  let order_to = [ Uncontended; Shared; Contended ]
  let order_in = linear_order [ Contended; Shared; Uncontended ]
  let default = Uncontended
  let show = function
    | Uncontended -> "uncontended"
    | Shared -> "shared"
    | Contended -> "contended"
  let equal = ( = )
end

module Contention = struct
  include Make_axis (Contention_spec)
  type nonrec t = Contention_spec.t = Uncontended | Shared | Contended

  let uncontended = Uncontended
  let shared = Shared
  let contended = Contended
end

module Linearity_spec = struct
  type t = Many | Once | Never

  let order_to = [ Many; Once; Never ]
  let order_in = linear_order [ Many; Once; Never ]
  let default = Many
  let show = function Many -> "many" | Once -> "once" | Never -> "never"
  let equal = ( = )
end

module Linearity = struct
  include Make_axis (Linearity_spec)
  type nonrec t = Linearity_spec.t = Many | Once | Never

  let many = Many
  let once = Once
  let never = Never
end

module Portability_spec = struct
  type t = Portable | NonPortable

  let order_to = [ Portable; NonPortable ]
  let order_in = linear_order [ Portable; NonPortable ]
  let default = NonPortable
  let show = function Portable -> "portable" | NonPortable -> "nonportable"
  let equal = ( = )
end

module Portability = struct
  include Make_axis (Portability_spec)
  type nonrec t = Portability_spec.t = Portable | NonPortable

  let portable = Portable
  let nonportable = NonPortable
end

module Areality_spec = struct
  type t = Global | Borrowed

  let order_to = [ Global; Borrowed ]
  let order_in = linear_order [ Global; Borrowed ]
  let default = Global
  let show = function
    | Global -> "global"
    | Borrowed -> "borrowed"
  let equal = ( = )
end

module Areality = struct
  include Make_axis (Areality_spec)
  type nonrec t = Areality_spec.t = Global | Borrowed

  let global = Global
  let borrowed = Borrowed
end

module Regionality = struct
  type t = Infty | Region of int

  let default = Infty

  let equal a b =
    match (a, b) with
    | Infty, Infty -> true
    | Region x, Region y -> x = y
    | _ -> false

  let to_string = function Infty -> "inf" | Region n -> string_of_int n
  let to_short_string v = if equal v default then "" else to_string v

  let to_int = function Infty -> max_int | Region n -> n

  (* Reverse arithmetic order: higher numeric regions are "smaller" *)
  let leq_to a b = to_int a >= to_int b
  let leq_in = leq_to

  let heap = Infty
  let stack = Region 0
  let of_int n = Region n

  let of_string name =
    match name with
    | "inf" -> Some Infty
    | _ -> (
        match int_of_string_opt name with
        | Some n when n >= 0 -> Some (Region n)
        | _ -> None)

  let extract names =
    let rec aux seen acc = function
      | [] -> (match seen with Some v -> v | None -> default), List.rev acc
      | candidate :: rest -> (
          match of_string candidate with
          | Some value ->
              if Option.is_some seen then
                invalid_arg
                  (Printf.sprintf "Mode %s provided multiple times" (to_string value));
              aux (Some value) acc rest
          | None -> aux seen (candidate :: acc) rest)
    in
    aux None [] names
end

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
      areality : Areality.t;
      regionality : Regionality.t }

  let default =
    { linearity = Linearity.default;
      portability = Portability.default;
      areality = Areality.default;
      regionality = Regionality.default }

  let make ~linearity ~portability ~areality ~regionality =
    { linearity; portability; areality; regionality }

  let leq_to a b =
    Linearity.leq_to a.linearity b.linearity
    && Portability.leq_to a.portability b.portability
    && Areality.leq_to a.areality b.areality
    && Regionality.leq_to a.regionality b.regionality

  let leq_in = leq_to

  let extract names =
    let areality, names = Areality.extract names in
    let regionality, names = Regionality.extract names in
    let linearity, names = Linearity.extract names in
    let portability, names = Portability.extract names in
    ({ areality; linearity; portability; regionality }, names)

  let to_string t =
    concat
      [ Areality.to_short_string t.areality;
        Regionality.to_short_string t.regionality;
        Linearity.to_short_string t.linearity;
        Portability.to_short_string t.portability ]
end

module Mode = struct
  type t = { past : Past.t; future : Future.t }

  let default = { past = Past.default; future = Future.default }

  let make ~past ~future = { past; future }

  let leq_to a b = Past.leq_to a.past b.past && Future.leq_to a.future b.future
  let leq_in a b = Past.leq_in a.past b.past && Future.leq_in a.future b.future

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
