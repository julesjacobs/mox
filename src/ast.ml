(** Abstract syntax tree definitions for the Mox language. *)

type ident = string

(** Function mode annotations for arrows. *)
type arrow_mode = Modes.Future.t

(** Types as described in tex/mox.tex. *)
type storage_mode =
  { uniqueness : Modes.Uniqueness.t;
    areality : Modes.Areality.t }

type ty =
  | TyUnit
  | TyEmpty
  | TyArrow of ty * Modes.Future.t * ty
  | TyPair of ty * storage_mode * ty
  | TySum of ty * storage_mode * ty

(** Expressions as described in tex/mox.tex. *)
type alloc =
  | Stack
  | Heap

type expr =
  | Var of ident
  | Let of ident * expr * expr
  | Unit
  | Hole
  | Absurd of expr
  | Fun of alloc * ident * expr
  | App of expr * expr
  | Pair of alloc * expr * expr
  | LetPair of ident * ident * expr * expr
  | Inl of alloc * expr
  | Inr of alloc * expr
  | Region of expr
  | Match of expr * ident * expr * ident * expr
  | Annot of expr * ty
