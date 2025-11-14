(** Abstract syntax tree definitions for the Mox language. *)

type ident = string

(** Function mode annotations for arrows. *)
type arrow_mode = Modes.Future.t

(** Types as described in tex/mox.tex. *)
type storage_mode =
  { uniqueness : Modes.Uniqueness.t;
    areality : Modes.Areality.t }

type ref_mode =
  { contention : Modes.Contention.t }

type ty =
  | TyUnit
  | TyEmpty
  | TyInt
  | TyBool
  | TyList of ty * storage_mode
  | TyArrow of ty * Modes.Future.t * ty
  | TyPair of ty * storage_mode * ty
  | TySum of ty * storage_mode * ty
  | TyRef of ty * ref_mode

(** Expressions as described in tex/mox.tex. *)
type alloc =
  | Stack
  | Heap

type bind_kind =
  | Regular
  | Destructive

type expr =
  | Var of ident
  | Borrow of ident * expr * ident * expr * expr
  | Let of bind_kind * ident * expr * expr
  | FunRec of alloc * ident * ident * expr
  | Unit
  | Bool of bool
  | If of expr * expr * expr
  | ListNil
  | ListCons of alloc * expr * expr
  | MatchList of bind_kind * expr * expr * ident * ident * expr
  | Int of int
  | IntAdd of expr * expr
  | IntSub of expr * expr
  | IntMul of expr * expr
  | IntNeg of expr
  | IntEq of expr * expr
  | IntLt of expr * expr
  | IntLe of expr * expr
  | IntGt of expr * expr
  | IntGe of expr * expr
  | BoolAnd of expr * expr
  | BoolOr of expr * expr
  | BoolNot of expr
  | Hole
  | Absurd of expr
  | Fun of alloc * ident * expr
  | App of expr * expr
  | Pair of alloc * expr * expr
  | LetPair of bind_kind * ident * ident * expr * expr
  | Inl of alloc * expr
  | Inr of alloc * expr
  | Region of expr
  | Match of bind_kind * expr * ident * expr * ident * expr
  | Ref of expr
  | Deref of expr
  | Assign of expr * expr
  | Fork of expr
  | Annot of expr * ty
