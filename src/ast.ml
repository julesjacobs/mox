(** Abstract syntax tree definitions for the Mox language. *)

type ident = string

(** Function mode annotations for arrows. *)
type arrow_mode = Modes.Future.t

(** Types as described in tex/mox.tex. *)
type ty =
  | TyUnit
  | TyEmpty
  | TyArrow of ty * Modes.Future.t * ty
  | TyPair of ty * Modes.Past.t * Modes.Future.t * ty
  | TySum of ty * Modes.Past.t * Modes.Future.t * ty

(** Expressions as described in tex/mox.tex. *)
type expr =
  | Var of ident
  | Let of ident * expr * expr
  | Unit
  | Absurd of expr
  | Fun of ident * expr
  | App of expr * expr
  | Pair of expr * expr
  | LetPair of ident * ident * expr * expr
  | Inl of expr
  | Inr of expr
  | Match of expr * ident * expr * ident * expr
  | Annot of expr * ty
