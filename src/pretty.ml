open Ast

let rec string_of_expr = function
  | Var x -> x
  | Let (x, e1, e2) -> Printf.sprintf "(let %s = %s in %s)" x (string_of_expr e1) (string_of_expr e2)
  | Unit -> "unit"
  | Absurd e -> Printf.sprintf "(absurd %s)" (string_of_expr e)
  | Fun (x, e) -> Printf.sprintf "(fun %s => %s)" x (string_of_expr e)
  | App (e1, e2) -> Printf.sprintf "(%s %s)" (string_of_expr e1) (string_of_expr e2)
  | Pair (e1, e2) -> Printf.sprintf "(%s, %s)" (string_of_expr e1) (string_of_expr e2)
  | LetPair (x1, x2, e1, e2) ->
      Printf.sprintf "(let (%s, %s) = %s in %s)" x1 x2 (string_of_expr e1) (string_of_expr e2)
  | Inl e -> Printf.sprintf "left(%s)" (string_of_expr e)
  | Inr e -> Printf.sprintf "right(%s)" (string_of_expr e)
  | Match (scrutinee, x1, e1, x2, e2) ->
      Printf.sprintf "(match %s with left(%s) => %s | right(%s) => %s)"
        (string_of_expr scrutinee) x1 (string_of_expr e1) x2 (string_of_expr e2)
  | Annot (e, ty) -> Printf.sprintf "(%s : %s)" (string_of_expr e) (string_of_ty ty)

and string_of_ty = function
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
  | TyArrow (t1, t2) -> Printf.sprintf "(%s -> %s)" (string_of_ty t1) (string_of_ty t2)
  | TyPair (t1, t2) -> Printf.sprintf "(%s * %s)" (string_of_ty t1) (string_of_ty t2)
  | TySum (t1, t2) -> Printf.sprintf "(%s + %s)" (string_of_ty t1) (string_of_ty t2)
