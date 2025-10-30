(** Mode lattice as described in tex/mox.tex. *)

module Uniqueness = struct
  type t = Unique | Aliased

  let all = [ Unique; Aliased ]
  let default = Aliased

  let rank_to = function Unique -> 0 | Aliased -> 1
  let rank_in = function Aliased -> 0 | Unique -> 1

  let leq_to a b = rank_to a <= rank_to b
  let leq_in a b = rank_in a <= rank_in b

  let join_to a b = if rank_to a >= rank_to b then a else b
  let meet_in a b = if rank_in a <= rank_in b then a else b

  let to_string = function Unique -> "unique" | Aliased -> "aliased"
  let to_short_string = function Unique -> "unique" | Aliased -> ""
end

module Contention = struct
  type t = Uncontended | Shared | Contended

  let all = [ Uncontended; Shared; Contended ]
  let default = Uncontended

  let rank_to = function Uncontended -> 0 | Shared -> 1 | Contended -> 2
  let rank_in = function Contended -> 0 | Shared -> 1 | Uncontended -> 2

  let leq_to a b = rank_to a <= rank_to b
  let leq_in a b = rank_in a <= rank_in b

  let join_to a b = if rank_to a >= rank_to b then a else b
  let meet_in a b = if rank_in a <= rank_in b then a else b

  let to_string = function
    | Uncontended -> "uncontended"
    | Shared -> "shared"
    | Contended -> "contended"
  let to_short_string = function
    | Uncontended -> ""
    | Shared -> "shared"
    | Contended -> "contended"
end

module Linearity = struct
  type t = Many | Once

  let all = [ Many; Once ]
  let default = Many

  let rank = function Many -> 0 | Once -> 1

  let leq_to a b = rank a <= rank b
  let leq_in = leq_to

  let join_to a b = if rank a >= rank b then a else b
  let meet_to a b = if rank a <= rank b then a else b

  let to_string = function Many -> "many" | Once -> "once"
  let to_short_string = function Many -> "" | Once -> "once"
end

module Portability = struct
  type t = Portable | NonPortable

  let all = [ Portable; NonPortable ]
  let default = NonPortable

  let rank = function Portable -> 0 | NonPortable -> 1

  let leq_to a b = rank a <= rank b
  let leq_in = leq_to

  let join_to a b = if rank a >= rank b then a else b
  let meet_to a b = if rank a <= rank b then a else b

  let to_string = function Portable -> "portable" | NonPortable -> "non-portable"
  let to_short_string = function Portable -> "portable" | NonPortable -> ""
end

module Areality = struct
  type t = Global | Regional | Local

  let all = [ Global; Regional; Local ]
  let default = Global

  let rank = function Global -> 0 | Regional -> 1 | Local -> 2

  let leq_to a b = rank a <= rank b
  let leq_in = leq_to

  let join_to a b = if rank a >= rank b then a else b
  let meet_to a b = if rank a <= rank b then a else b

  let to_string = function Global -> "global" | Regional -> "regional" | Local -> "local"
  let to_short_string = function
    | Global -> ""
    | Regional -> "regional"
    | Local -> "local"
end

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

  let meet_in a b =
    { uniqueness = Uniqueness.meet_in a.uniqueness b.uniqueness;
      contention = Contention.meet_in a.contention b.contention }
  let to_string t =
    [ Uniqueness.to_short_string t.uniqueness;
      Contention.to_short_string t.contention ]
    |> List.filter (fun s -> String.length s > 0)
    |> String.concat " "
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
  let to_string t =
    [ Areality.to_short_string t.areality;
      Linearity.to_short_string t.linearity;
      Portability.to_short_string t.portability ]
    |> List.filter (fun s -> String.length s > 0)
    |> String.concat " "
end

module Mode = struct
  type t = { past : Past.t; future : Future.t }

  let default = { past = Past.default; future = Future.default }

  let make ~past ~future = { past; future }

  let leq_to a b = Past.leq_to a.past b.past && Future.leq_to a.future b.future
  let leq_in a b = Past.leq_in a.past b.past && Future.leq_in a.future b.future

  let join_to a b =
    { past = Past.join_to a.past b.past; future = Future.join_to a.future b.future }

  let meet_in a b =
    { past = Past.meet_in a.past b.past; future = Future.meet_to a.future b.future }
  let to_string t =
    let parts =
      [ Past.to_string t.past; Future.to_string t.future ]
      |> List.filter (fun s -> String.length s > 0)
    in
    String.concat " " parts
end
