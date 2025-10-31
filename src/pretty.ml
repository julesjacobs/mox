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
  | TyArrow (t1, modes, t2) ->
      let parts =
        [ Modes.Areality.to_short_string modes.Modes.Future.areality;
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
          Modes.Areality.to_short_string mode.areality ]
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
          Modes.Areality.to_short_string mode.areality ]
        |> List.filter (fun s -> String.trim s <> "")
      in
      let sep =
        match parts with
        | [] -> " + "
        | _ -> Printf.sprintf " +[%s] " (String.concat " " parts)
      in
      Printf.sprintf "(%s%s%s)" (string_of_ty t1) sep (string_of_ty t2)
