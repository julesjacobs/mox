%{
open Ast

let default_storage_mode =
  { uniqueness = Modes.Uniqueness.default; areality = Modes.Areality.default }

let default_ref_mode =
  { contention = Modes.Contention.default }

let storage_mode_from_list names =
  let uniqueness, remaining = Modes.Uniqueness.extract names in
  let areality, remaining = Modes.Areality.extract remaining in
  if remaining <> [] then
    invalid_arg
      (Printf.sprintf "Modes [%s] not allowed on products/sums"
         (String.concat ", " remaining));
  { uniqueness; areality }

let ref_mode_from_list names =
  let contention, remaining = Modes.Contention.extract names in
  if remaining <> [] then
    invalid_arg
      (Printf.sprintf "Only contention modes are allowed on references, but saw [%s]"
         (String.concat ", " remaining));
  { contention }

let rec list_literal alloc elems =
  List.fold_right
    (fun elem acc -> ListCons (alloc, elem, acc))
    elems
    ListNil
%}

%token LET LETBANG IN BORROW FUN MATCH MATCHBANG WITH LEFT RIGHT ABSURD UNIT EMPTY INT BOOL TRUE FALSE QUESTION STACK REGION FOR REC IF THEN ELSE
%token LIST
%token REF FORK BANG ASSIGN NOT AND OR
%token LPAREN RPAREN LBRACKET RBRACKET COMMA EQUAL BAR ARROW FATARROW PLUS MINUS TIMES CONS COLON
%token EQ LT GT LE GE
%token <string> IDENT
%token <int> INT_LITERAL
%token EOF

%start <Ast.expr> expr_eof
%start <Ast.ty> ty_eof
%start <string list> modes_eof
%type <Ast.bind_kind> bind_prefix
%type <Ast.bind_kind> match_prefix
%left OR
%left AND
%nonassoc EQ LT GT LE GE
%left PLUS MINUS
%left TIMES

%%

%inline open_lbracket:
  | LBRACKET { () }

%inline open_lparen:
  | LPAREN { () }

%inline open_inl:
  | LEFT LPAREN { () }

%inline open_inr:
  | RIGHT LPAREN { () }

%inline with_opt_stack(Open):
  | Open       { Heap }
  | STACK Open { Stack }

%inline kw_with_opt_stack(Kw):
  | Kw         { Heap }
  | STACK Kw   { Stack }

expr_eof:
  | expr EOF { $1 }

expr:
  | expr_base { $1 }
  | expr_base COLON ty { Annot ($1, $3) }

expr_base:
  | BORROW IDENT EQUAL expr FOR IDENT EQUAL expr IN expr { Borrow ($2, $4, $6, $8, $10) }
  | bind_prefix IDENT EQUAL expr IN expr { Let ($1, $2, $4, $6) }
  | bind_prefix LPAREN IDENT COMMA IDENT RPAREN EQUAL expr IN expr
      { LetPair ($1, $3, $5, $8, $10) }
  | kw_with_opt_stack(FUN) IDENT FATARROW expr { Fun ($1, $2, $4) }
  | kw_with_opt_stack(REC) IDENT IDENT FATARROW expr { FunRec ($1, $2, $3, $5) }
  | match_prefix expr WITH LEFT LPAREN IDENT RPAREN FATARROW expr
      BAR RIGHT LPAREN IDENT RPAREN FATARROW expr
      { Match ($1, $2, $6, $9, $13, $16) }
  | match_prefix expr WITH LBRACKET RBRACKET FATARROW expr
      BAR IDENT CONS IDENT FATARROW expr
      { MatchList ($1, $2, $7, $9, $11, $13) }
  | REF expr_base { Ref $2 }
  | FORK expr { Fork $2 }
  | expr_assign { $1 }

expr_assign:
  | expr_assign ASSIGN expr_cons { Assign ($1, $3) }
  | expr_cons { $1 }

expr_cons:
  | expr_or CONS expr_cons { ListCons (Heap, $1, $3) }
  | expr_or { $1 }

expr_or:
  | expr_or OR expr_and { BinOp ($1, Or, $3) }
  | expr_and { $1 }

expr_and:
  | expr_and AND expr_cmp { BinOp ($1, And, $3) }
  | expr_cmp { $1 }

expr_cmp:
  | expr_cmp EQ expr_sum { BinOp ($1, Eq, $3) }
  | expr_cmp LT expr_sum { BinOp ($1, Lt, $3) }
  | expr_cmp LE expr_sum { BinOp ($1, Le, $3) }
  | expr_cmp GT expr_sum { BinOp ($1, Gt, $3) }
  | expr_cmp GE expr_sum { BinOp ($1, Ge, $3) }
  | expr_sum { $1 }

expr_sum:
  | expr_sum PLUS expr_mul { BinOp ($1, Add, $3) }
  | expr_sum MINUS expr_mul { BinOp ($1, Sub, $3) }
  | expr_mul { $1 }

expr_mul:
  | expr_mul TIMES expr_unary { BinOp ($1, Mul, $3) }
  | expr_unary { $1 }

expr_unary:
  | MINUS expr_unary { IntNeg $2 }
  | NOT expr_unary { BoolNot $2 }
  | expr_app { $1 }

expr_app:
  | expr_app expr_atom { App ($1, $2) }
  | expr_atom { $1 }

expr_atom:
  | BANG expr_atom { Deref $2 }
  | IDENT { Var $1 }
  | UNIT { Unit }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | with_opt_stack(open_lbracket) list_items_opt RBRACKET { list_literal $1 $2 }
  | INT_LITERAL { Int $1 }
  | QUESTION { Hole }
  | IF expr THEN expr ELSE expr { If ($2, $4, $6) }
  | ABSURD expr { Absurd $2 }
  | REGION expr { Region $2 }
  | with_opt_stack(open_inl) expr RPAREN { Inl ($1, $2) }
  | with_opt_stack(open_inr) expr RPAREN { Inr ($1, $2) }
  | with_opt_stack(open_lparen) expr COMMA expr RPAREN { Pair ($1, $2, $4) }
  | LPAREN expr RPAREN { $2 }

list_items_opt:
  | list_items { $1 }
  | /* empty */ { [] }

list_items:
  | expr { [ $1 ] }
  | expr COMMA list_items { $1 :: $3 }

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
  | BOOL { TyBool }
  | LIST ty_atom { TyList ($2, default_storage_mode) }
  | LIST mode_list ty_atom { TyList ($3, storage_mode_from_list $2) }
  | INT { TyInt }
  | REF ty_atom { TyRef ($2, default_ref_mode) }
  | REF mode_list ty_atom { TyRef ($3, ref_mode_from_list $2) }
  | LPAREN ty RPAREN { $2 }
