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
  | whitespace           {
      let lexeme = Lexing.lexeme lexbuf in
      String.iter (fun c -> if Char.equal c '\n' then Lexing.new_line lexbuf) lexeme;
      token lexbuf
    }
  | "(*"                 { comment lexbuf; token lexbuf }
  | "let!"               { LETBANG }
  | "let"                { LET }
  | "in"                 { IN }
  | "fun"                { FUN }
  | "match!"             { MATCHBANG }
  | "match"              { MATCH }
  | "with"               { WITH }
  | "ref"                { REF }
  | "fork"               { FORK }
  | "left"               { LEFT }
  | "right"              { RIGHT }
  | "absurd"             { ABSURD }
  | "region"             { REGION }
  | "unit"               { UNIT }
  | "empty"              { EMPTY }
  | "("                  { LPAREN }
  | ")"                  { RPAREN }
  | ","                  { COMMA }
  | "="                  { EQUAL }
  | "|"                  { BAR }
  | "$"                  { STACK }
  | "["                  { LBRACKET }
  | "]"                  { RBRACKET }
  | ":"                  { COLON }
  | "=>"                 { FATARROW }
  | "->"                 { ARROW }
  | ":="                 { ASSIGN }
  | "+"                  { PLUS }
  | "*"                  { TIMES }
  | "?"                  { QUESTION }
  | "!"                  { BANG }
  | ident_start ident_continue* as id { IDENT id }
  | eof                  { EOF }
  | _ as c               { raise (Lexing_error (Printf.sprintf "unexpected character %c at %s" c (location lexbuf))) }

and comment = parse
  | "(*"                 { comment lexbuf; comment lexbuf }
  | "*)"                 { () }
  | '\n'                 { Lexing.new_line lexbuf; comment lexbuf }
  | eof                  { raise (Lexing_error "unterminated comment") }
  | _                    { comment lexbuf }
