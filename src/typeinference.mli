type error = string

exception Error of error

type ty

val infer : Ast.expr -> ty
val string_of_ty : ty -> string
val string_of_error : error -> string
