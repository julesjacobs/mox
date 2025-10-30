open Ast

type type_error =
  | Unbound_variable of ident
  | Type_mismatch of ty * ty
  | Expected_function of ty
  | Expected_pair of ty
  | Expected_sum of ty
  | Cannot_infer of string

exception Error of type_error

let rec equal_ty t1 t2 =
  match (t1, t2) with
  | TyUnit, TyUnit -> true
  | TyEmpty, TyEmpty -> true
  | TyArrow (a1, b1), TyArrow (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | TyPair (a1, b1), TyPair (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | TySum (a1, b1), TySum (a2, b2) -> equal_ty a1 a2 && equal_ty b1 b2
  | _ -> false

let ensure_equal expected actual =
  if equal_ty expected actual then ()
  else raise (Error (Type_mismatch (expected, actual)))

let lookup env x =
  let rec aux = function
    | [] -> raise (Error (Unbound_variable x))
    | (y, ty) :: rest -> if String.equal x y then ty else aux rest
  in
  aux env

let string_of_ty = Pretty.string_of_ty

let string_of_error = function
  | Unbound_variable x -> Printf.sprintf "Unbound variable %s" x
  | Type_mismatch (expected, actual) ->
      Printf.sprintf "Type mismatch: expected %s, found %s"
        (string_of_ty expected) (string_of_ty actual)
  | Expected_function ty ->
      Printf.sprintf "Expected a function type, found %s" (string_of_ty ty)
  | Expected_pair ty ->
      Printf.sprintf "Expected a pair type, found %s" (string_of_ty ty)
  | Expected_sum ty ->
      Printf.sprintf "Expected a sum type, found %s" (string_of_ty ty)
  | Cannot_infer what ->
      Printf.sprintf "Cannot infer the type of %s; add a type annotation" what

let rec synth env expr =
  match expr with
  | Var x -> lookup env x
  | Unit -> TyUnit
  | Absurd _ -> raise (Error (Cannot_infer "absurd"))
  | Fun _ -> raise (Error (Cannot_infer "function"))
  | App (e1, e2) ->
      let tf = synth env e1 in
      (match tf with
      | TyArrow (targ, tres) ->
          check env e2 targ;
          tres
      | _ -> raise (Error (Expected_function tf)))
  | Pair (e1, e2) ->
      let t1 = synth env e1 in
      let t2 = synth env e2 in
      TyPair (t1, t2)
  | Let (x, e1, e2) ->
      let t1 = synth env e1 in
      synth ((x, t1) :: env) e2
  | LetPair (x1, x2, e1, e2) ->
      let t = synth env e1 in
      (match t with
      | TyPair (t1, t2) -> synth ((x2, t2) :: (x1, t1) :: env) e2
      | _ -> raise (Error (Expected_pair t)))
  | Inl _ -> raise (Error (Cannot_infer "left"))
  | Inr _ -> raise (Error (Cannot_infer "right"))
  | Match (scrut, x1, e1, x2, e2) ->
      let scrut_ty = synth env scrut in
      (match scrut_ty with
      | TySum (t_left, t_right) ->
          let t_branch = synth ((x1, t_left) :: env) e1 in
          check ((x2, t_right) :: env) e2 t_branch;
          t_branch
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (e, ty) ->
      check env e ty;
      ty

and check env expr ty =
  match expr with
  | Unit -> ensure_equal ty TyUnit
  | Absurd e -> check env e TyEmpty
  | Fun (x, body) ->
      (match ty with
      | TyArrow (t_arg, t_res) -> check ((x, t_arg) :: env) body t_res
      | _ -> raise (Error (Expected_function ty)))
  | Inl e ->
      (match ty with
      | TySum (t_left, _) -> check env e t_left
      | _ -> raise (Error (Expected_sum ty)))
  | Inr e ->
      (match ty with
      | TySum (_, t_right) -> check env e t_right
      | _ -> raise (Error (Expected_sum ty)))
  | Pair (e1, e2) ->
      (match ty with
      | TyPair (t1, t2) ->
          check env e1 t1;
          check env e2 t2
      | _ -> raise (Error (Expected_pair ty)))
  | Let (x, e1, e2) ->
      let t1 = synth env e1 in
      check ((x, t1) :: env) e2 ty
  | LetPair (x1, x2, e1, e2) ->
      let t = synth env e1 in
      (match t with
      | TyPair (t1, t2) -> check ((x2, t2) :: (x1, t1) :: env) e2 ty
      | _ -> raise (Error (Expected_pair t)))
  | Match (scrut, x1, e1, x2, e2) ->
      let scrut_ty = synth env scrut in
      (match scrut_ty with
      | TySum (t_left, t_right) ->
          check ((x1, t_left) :: env) e1 ty;
          check ((x2, t_right) :: env) e2 ty
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (e, ty') ->
      check env e ty';
      ensure_equal ty ty'
  | _ ->
      let inferred = synth env expr in
      ensure_equal ty inferred

let infer expr = synth [] expr

let check_top expr ty = check [] expr ty
