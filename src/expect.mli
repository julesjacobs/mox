exception Error of string

type chunk =
  | Blank of string
  | Expr of { start_line : int; lines : string list }

type expectation =
  | Type of string
  | Error of string

type processed =
  | PBlank of string
  | PExpr of string list * expectation

type infer = Ast.expr -> (string, string) result

val default_infer : infer
val process_lines : ?filename:string -> ?infer:infer -> string list -> string list
val process_file : ?infer:infer -> string -> unit
val process_path : ?infer:infer -> string -> unit
