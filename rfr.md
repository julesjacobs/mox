Please advise on eliminating Menhir shift/reduce and reduce/reduce conflicts in an expression grammar that has optional `STACK` prefixes for certain atoms. Current grammar snippet:

```
expr_eof:
  | expr EOF { $1 }

expr:
  | expr_base { $1 }
  | expr_base COLON ty { Annot ($1, $3) }

expr_base:
  | BORROW IDENT EQUAL expr FOR IDENT EQUAL expr IN expr { Borrow ($2,$4,$6,$8,$10) }
  | bind_prefix IDENT EQUAL expr IN expr { Let ($1,$2,$4,$6) }
  | bind_prefix LPAREN IDENT COMMA IDENT RPAREN EQUAL expr IN expr { LetPair ($1,$3,$5,$8,$10) }
  | stack_prefix FUN IDENT FATARROW expr { Fun ($1,$3,$5) }
  | stack_prefix REC IDENT IDENT FATARROW expr { FunRec ($1,$3,$4,$6) }
  | match_prefix expr WITH LEFT LPAREN IDENT RPAREN FATARROW expr
      BAR RIGHT LPAREN IDENT RPAREN FATARROW expr { Match ($1,$2,$6,$9,$13,$16) }
  | match_prefix expr WITH LBRACKET RBRACKET FATARROW expr
      BAR IDENT CONS IDENT FATARROW expr { MatchList ($1,$2,$7,$9,$11,$13) }
  | REF expr_base { Ref $2 }
  | FORK expr { Fork $2 }
  | expr_assign { $1 }

expr_assign:
  | expr_assign ASSIGN expr_cons { Assign ($1,$3) }
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
  | expr_app expr_atom { App ($1,$2) }
  | expr_atom { $1 }

expr_atom:
  | BANG expr_atom { Deref $2 }
  | IDENT { Var $1 }
  | UNIT { Unit }
  | TRUE { Bool true }
  | FALSE { Bool false }
  | stack_prefix LBRACKET list_items_opt RBRACKET { list_literal $1 $3 }
  | INT_LITERAL { Int $1 }
  | QUESTION { Hole }
  | IF expr THEN expr ELSE expr { If ($2,$4,$6) }
  | ABSURD expr { Absurd $2 }
  | REGION expr { Region $2 }
  | stack_prefix LEFT LPAREN expr RPAREN { Inl ($1,$4) }
  | stack_prefix RIGHT LPAREN expr RPAREN { Inr ($1,$4) }
  | stack_prefix LPAREN expr COMMA expr RPAREN { Pair ($1,$3,$5) }
  | LPAREN expr RPAREN { $2 }

list_items_opt:
  | list_items { $1 }
  | /* empty */ { [] }

list_items:
  | expr { [ $1 ] }
  | expr COMMA list_items { $1 :: $3 }

stack_prefix:
  | STACK { Stack }
  | /* empty */ { Heap }
```

Menhir reports reduce/reduce conflicts between stack vs heap variants (e.g., `STACK LBRACKET ...` vs `LBRACKET ...`) because `stack_prefix` is nullable, plus many shift/reduce conflicts. Looking for best-practice Menhir guidance: precedence declarations vs grammar refactor to remove these conflicts without changing language behavior. Ideally, eliminate ambiguity while keeping stackable constructs (lists, pairs, sum injections) selectable by `STACK` vs default.
