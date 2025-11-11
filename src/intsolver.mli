type var

type relation = (int, int) Relations.t

exception Inconsistent of string

val newvar : int list -> var
val assert_rel : relation -> var -> var -> unit
val get_rel : var -> var -> relation
