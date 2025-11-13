%{
open Ast

let default_storage_mode =
  { uniqueness = Modes.Uniqueness.default; areality = Modes.Areality.default }

let storage_mode_from_list names =
  let uniqueness, remaining = Modes.Uniqueness.extract names in
  let areality, remaining = Modes.Areality.extract remaining in
  if remaining <> [] then
    invalid_arg
      (Printf.sprintf "Modes [%s] not allowed on products/sums"
         (String.concat ", " remaining));
  { uniqueness; areality }
%}

%token LET LETBANG IN FUN MATCH MATCHBANG WITH LEFT RIGHT ABSURD UNIT EMPTY QUESTION STACK REGION
%token LPAREN RPAREN LBRACKET RBRACKET COMMA EQUAL BAR ARROW FATARROW PLUS TIMES COLON
%token <string> IDENT
%token EOF

%start <Ast.expr> expr_eof
%start <Ast.ty> ty_eof
%start <string list> modes_eof

%left BAR
%left PLUS
%left TIMES
%right ARROW

%%

expr_eof:
  | expr EOF { $1 }

expr:
  | expr_base { $1 }
  | expr_base COLON ty { Annot ($1, $3) }

expr_base:
  | bind_prefix IDENT EQUAL expr IN expr { Let ($1, $2, $4, $6) }
  | bind_prefix LPAREN IDENT COMMA IDENT RPAREN EQUAL expr IN expr
      { LetPair ($1, $3, $5, $8, $10) }
  | stack_prefix FUN IDENT FATARROW expr { Fun ($1, $3, $5) }
  | match_prefix expr WITH LEFT LPAREN IDENT RPAREN FATARROW expr
      BAR RIGHT LPAREN IDENT RPAREN FATARROW expr
      { Match ($1, $2, $6, $9, $13, $16) }
  | expr_app { $1 }

expr_app:
  | expr_app expr_atom { App ($1, $2) }
  | expr_atom { $1 }

expr_atom:
  | IDENT { Var $1 }
  | UNIT { Unit }
  | QUESTION { Hole }
  | ABSURD expr { Absurd $2 }
  | REGION expr { Region $2 }
  | LEFT LPAREN expr RPAREN { Inl (Heap, $3) }
  | STACK LEFT LPAREN expr RPAREN { Inl (Stack, $4) }
  | RIGHT LPAREN expr RPAREN { Inr (Heap, $3) }
  | STACK RIGHT LPAREN expr RPAREN { Inr (Stack, $4) }
  | LPAREN expr COMMA expr RPAREN { Pair (Heap, $2, $4) }
  | STACK LPAREN expr COMMA expr RPAREN { Pair (Stack, $3, $5) }
  | LPAREN expr RPAREN { $2 }

stack_prefix:
  | STACK { Stack }
  | /* empty */ { Heap }

bind_prefix:
  | LET { Regular }
  | LETBANG { Destructive }

match_prefix:
  | MATCH { Regular }
  | MATCHBANG { Destructive }

(* Type grammar *)

ty_eof:
  | ty EOF { $1 }

modes_eof:
  | mode_list EOF { $1 }

mode_list:
  | LBRACKET mode_items RBRACKET { $2 }

mode_items:
  | /* empty */ { [] }
  | IDENT mode_items { $1 :: $2 }

ty:
  | ty_sum { $1 }
  | ty_sum arrow_tail { $2 $1 }

arrow_tail:
  | ARROW ty { fun lhs -> TyArrow (lhs, Modes.Future.default, $2) }
  | ARROW mode_list ty { fun lhs ->
        let future, leftover = Modes.Future.extract $2 in
        if leftover <> [] then
          invalid_arg
            (Printf.sprintf "Modes [%s] not allowed on functions"
               (String.concat ", " leftover));
        TyArrow (lhs, future, $3)
    }

ty_sum:
  | ty_sum PLUS ty_prod { TySum ($1, default_storage_mode, $3) }
  | ty_sum PLUS mode_list ty_prod { TySum ($1, storage_mode_from_list $3, $4) }
  | ty_prod { $1 }

ty_prod:
  | ty_prod TIMES ty_atom { TyPair ($1, default_storage_mode, $3) }
  | ty_prod TIMES mode_list ty_atom { TyPair ($1, storage_mode_from_list $3, $4) }
  | ty_atom { $1 }

ty_atom:
  | UNIT { TyUnit }
  | EMPTY { TyEmpty }
  | LPAREN ty RPAREN { $2 }
