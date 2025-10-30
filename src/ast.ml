(** Abstract syntax tree definitions for the Mox language. *)

type ident = string

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

(** Types as described in tex/mox.tex. *)
and ty =
  | TyUnit
  | TyEmpty
  | TyArrow of ty * ty
  | TyPair of ty * ty
  | TySum of ty * ty
