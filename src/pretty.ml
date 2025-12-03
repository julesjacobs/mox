open Ast

let stack_prefix = function
  | Stack region -> String.make (region + 1) '$'
  | Heap -> ""

let bind_prefix = function
  | Regular -> "let"
  | Destructive -> "let!"

let match_prefix = function
  | Regular -> "match"
  | Destructive -> "match!"

let rec string_of_expr = function
  | Var x -> x
  | Borrow (x, e1, y, e2, e3) ->
      Printf.sprintf "(borrow %s = %s for %s = %s in %s)"
        x (string_of_expr e1) y (string_of_expr e2) (string_of_expr e3)
  | Let (kind, x, e1, e2) ->
        Printf.sprintf "(%s %s = %s in %s)"
        (bind_prefix kind) x (string_of_expr e1) (string_of_expr e2)
  | Unit -> "unit"
  | Bool true -> "true"
  | Bool false -> "false"
  | If (cond, t_branch, e_branch) ->
      Printf.sprintf "(if %s then %s else %s)"
        (string_of_expr cond) (string_of_expr t_branch) (string_of_expr e_branch)
  | BinOp (lhs, op, rhs) ->
      let sym =
        match op with
        | Add -> "+" | Sub -> "-" | Mul -> "*" | Eq -> "==" | Lt -> "<"
        | Le -> "<=" | Gt -> ">" | Ge -> ">=" | And -> "and" | Or -> "or"
      in
      Printf.sprintf "(%s %s %s)" (string_of_expr lhs) sym (string_of_expr rhs)
  | ListNil -> "[]"
  | ListCons (alloc, head, tail) ->
      let cons =
        let prefix = stack_prefix alloc in
        if prefix = "" then "::" else prefix ^ "::"
      in
      Printf.sprintf "(%s %s %s)"
        (string_of_expr head) cons (string_of_expr tail)
  | MatchList (kind, scrutinee, nil_branch, x, xs, cons_branch) ->
      Printf.sprintf "(%s %s with [] => %s | %s :: %s => %s)"
        (match_prefix kind) (string_of_expr scrutinee)
        (string_of_expr nil_branch) x xs (string_of_expr cons_branch)
  | Int n -> string_of_int n
  | IntNeg e -> Printf.sprintf "(-%s)" (string_of_expr e)
  | BoolNot e -> Printf.sprintf "(not %s)" (string_of_expr e)
  | Hole -> "?"
  | Absurd e -> Printf.sprintf "(absurd %s)" (string_of_expr e)
  | Fun (stack, x, e) ->
      Printf.sprintf "(%sfun %s => %s)" (stack_prefix stack) x (string_of_expr e)
  | FunRec (stack, f, x, e) ->
      Printf.sprintf "(%srec %s %s => %s)" (stack_prefix stack) f x (string_of_expr e)
  | App (e1, e2) -> Printf.sprintf "(%s %s)" (string_of_expr e1) (string_of_expr e2)
  | Pair (stack, e1, e2) ->
      Printf.sprintf "%s(%s, %s)" (stack_prefix stack) (string_of_expr e1) (string_of_expr e2)
  | LetPair (kind, x1, x2, e1, e2) ->
      Printf.sprintf "(%s (%s, %s) = %s in %s)"
        (bind_prefix kind) x1 x2 (string_of_expr e1) (string_of_expr e2)
  | Inl (stack, e) -> Printf.sprintf "%sleft(%s)" (stack_prefix stack) (string_of_expr e)
  | Inr (stack, e) -> Printf.sprintf "%sright(%s)" (stack_prefix stack) (string_of_expr e)
  | Region e -> Printf.sprintf "(region %s)" (string_of_expr e)
  | Match (kind, scrutinee, x1, e1, x2, e2) ->
      Printf.sprintf "(%s %s with left(%s) => %s | right(%s) => %s)"
        (match_prefix kind) (string_of_expr scrutinee)
        x1 (string_of_expr e1) x2 (string_of_expr e2)
  | Ref e -> Printf.sprintf "(ref %s)" (string_of_expr e)
  | Deref e -> Printf.sprintf "(!%s)" (string_of_expr e)
  | Assign (lhs, rhs) ->
      Printf.sprintf "(%s := %s)" (string_of_expr lhs) (string_of_expr rhs)
  | Fork e -> Printf.sprintf "(fork %s)" (string_of_expr e)
  | Annot (e, ty) -> Printf.sprintf "(%s : %s)" (string_of_expr e) (string_of_ty ty)

and string_of_ty = function
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
  | TyBool -> "bool"
  | TyInt -> "int"
  | TyArrow (t1, modes, t2) ->
      let parts =
        [ Modes.Areality.to_short_string modes.Modes.Future.areality;
          Modes.Regionality.to_short_string modes.Modes.Future.regionality;
          Modes.Linearity.to_short_string modes.Modes.Future.linearity;
          Modes.Portability.to_short_string modes.Modes.Future.portability ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let arrow =
        match parts with
        | [] -> "->"
        | _ -> Printf.sprintf "->[%s]" (String.concat " " parts)
      in
      Printf.sprintf "(%s %s %s)" (string_of_ty t1) arrow (string_of_ty t2)
  | TyPair (t1, mode, t2) ->
      let parts =
        [ Modes.Uniqueness.to_short_string mode.uniqueness;
          Modes.Areality.to_short_string mode.areality;
          Modes.Regionality.to_short_string mode.regionality ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let sep =
        match parts with
        | [] -> " * "
        | _ -> Printf.sprintf " *[%s] " (String.concat " " parts)
      in
      Printf.sprintf "(%s%s%s)" (string_of_ty t1) sep (string_of_ty t2)
  | TySum (t1, mode, t2) ->
      let parts =
        [ Modes.Uniqueness.to_short_string mode.uniqueness;
          Modes.Areality.to_short_string mode.areality;
          Modes.Regionality.to_short_string mode.regionality ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let sep =
        match parts with
        | [] -> " + "
        | _ -> Printf.sprintf " +[%s] " (String.concat " " parts)
      in
      Printf.sprintf "(%s%s%s)" (string_of_ty t1) sep (string_of_ty t2)
  | TyList (elem, mode) ->
      let parts =
        [ Modes.Uniqueness.to_short_string mode.uniqueness;
          Modes.Areality.to_short_string mode.areality;
          Modes.Regionality.to_short_string mode.regionality ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let prefix =
        match parts with
        | [] -> "list "
        | _ -> Printf.sprintf "list[%s] " (String.concat " " parts)
      in
      Printf.sprintf "(%s%s)" prefix (string_of_ty elem)
  | TyRef (payload, mode) ->
      let parts =
        [ Modes.Contention.to_short_string mode.contention;
          Modes.Uniqueness.to_short_string mode.uniqueness ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let suffix =
        match parts with
        | [] -> "ref "
        | _ -> Printf.sprintf "ref[%s] " (String.concat " " parts)
      in
      Printf.sprintf "(%s%s)" suffix (string_of_ty payload)
