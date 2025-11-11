open Modes

exception Inconsistent of string

type 'a var
type 'a mode_var = 'a var

val new_var : encode:('a -> int) -> decode:(int -> 'a) -> domain:'a list -> 'a var
val assert_relation : ('a, 'b) Relations.t -> 'a var -> 'b var -> unit
val get_relation : 'a var -> 'b var -> ('a, 'b) Relations.t
val assert_predicate : ('a, 'a) Relations.t -> 'a var -> unit
val restrict_domain : 'a list -> 'a var -> unit
val assert_linearity_dagger :
  Modes.Linearity.t mode_var -> Modes.Uniqueness.t mode_var -> unit
val assert_portability_dagger :
  Modes.Portability.t mode_var -> Modes.Contention.t mode_var -> unit

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

module Uniqueness : AXIS_SOLVER with type mode = Modes.Uniqueness.t
module Contention : AXIS_SOLVER with type mode = Modes.Contention.t
module Linearity : AXIS_SOLVER with type mode = Modes.Linearity.t
module Portability : AXIS_SOLVER with type mode = Modes.Portability.t
module Areality : AXIS_SOLVER with type mode = Modes.Areality.t
