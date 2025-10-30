{
open Parser

exception Lexing_error of string

let location lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.sprintf "%s:%d:%d" pos.Lexing.pos_fname pos.Lexing.pos_lnum
    (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)
}

let whitespace = [' ' '\t' '\r' '\n']+
let ident_start = ['a'-'z' 'A'-'Z' '_' '\'']
let ident_continue = ident_start | ['0'-'9']

rule token = parse
  | whitespace           { token lexbuf }
  | "(*"                 { comment lexbuf; token lexbuf }
  | "let"                { LET }
  | "in"                 { IN }
  | "fun"                { FUN }
  | "match"              { MATCH }
  | "with"               { WITH }
  | "left"               { LEFT }
  | "right"              { RIGHT }
  | "absurd"             { ABSURD }
  | "unit"               { UNIT }
  | "empty"              { EMPTY }
  | "("                  { LPAREN }
  | ")"                  { RPAREN }
  | ","                  { COMMA }
  | "="                  { EQUAL }
  | "|"                  { BAR }
  | ":"                  { COLON }
  | "=>"                 { FATARROW }
  | "->"                 { ARROW }
  | "+"                  { PLUS }
  | "*"                  { TIMES }
  | ident_start ident_continue* as id { IDENT id }
  | eof                  { EOF }
  | _ as c               { raise (Lexing_error (Printf.sprintf "unexpected character %c at %s" c (location lexbuf))) }

and comment = parse
  | "(*"                 { comment lexbuf; comment lexbuf }
  | "*)"                 { () }
  | eof                  { raise (Lexing_error "unterminated comment") }
  | _                    { comment lexbuf }
