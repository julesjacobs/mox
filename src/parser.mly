%{
open Ast
%}

%token LET IN FUN MATCH WITH LEFT RIGHT ABSURD UNIT EMPTY
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
  | LET IDENT EQUAL expr IN expr { Let ($2, $4, $6) }
  | LET LPAREN IDENT COMMA IDENT RPAREN EQUAL expr IN expr
      { LetPair ($3, $5, $8, $10) }
  | FUN IDENT FATARROW expr { Fun ($2, $4) }
  | MATCH expr WITH LEFT LPAREN IDENT RPAREN FATARROW expr
      BAR RIGHT LPAREN IDENT RPAREN FATARROW expr
      { Match ($2, $6, $9, $13, $16) }
  | expr_app { $1 }

expr_app:
  | expr_app expr_atom { App ($1, $2) }
  | expr_atom { $1 }

expr_atom:
  | IDENT { Var $1 }
  | UNIT { Unit }
  | ABSURD expr { Absurd $2 }
  | LEFT LPAREN expr RPAREN { Inl $3 }
  | RIGHT LPAREN expr RPAREN { Inr $3 }
  | LPAREN expr COMMA expr RPAREN { Pair ($2, $4) }
  | LPAREN expr RPAREN { $2 }

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
  | ty_sum PLUS ty_prod { TySum ($1, $3) }
  | ty_prod { $1 }

ty_prod:
  | ty_prod TIMES ty_atom { TyPair ($1, $3) }
  | ty_atom { $1 }

ty_atom:
  | UNIT { TyUnit }
  | EMPTY { TyEmpty }
  | LPAREN ty RPAREN { $2 }
