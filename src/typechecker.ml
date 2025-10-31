open Ast

module StringSet = Set.Make (String)

(* -------------------------------------------------------------------------- *)
(* Error reporting                                                             *)
(* -------------------------------------------------------------------------- *)

type type_error =
  | Unbound_variable of ident
  | Expected_function of ty
  | Expected_pair of ty
  | Expected_sum of ty
  | Cannot_infer of string
  | Not_a_subtype of ty * ty

exception Error of type_error
exception Mode_error of string

let string_of_ty = Pretty.string_of_ty

let string_of_error = function
  | Unbound_variable x -> Printf.sprintf "Unbound variable %s" x
  | Expected_function ty ->
      Printf.sprintf "Expected a function type, found %s" (string_of_ty ty)
  | Expected_pair ty ->
      Printf.sprintf "Expected a pair type, found %s" (string_of_ty ty)
  | Expected_sum ty ->
      Printf.sprintf "Expected a sum type, found %s" (string_of_ty ty)
  | Cannot_infer what ->
      Printf.sprintf "Cannot infer the type of %s; add a type annotation" what
  | Not_a_subtype (t1, t2) ->
      Printf.sprintf "%s is not a subtype of %s"
        (string_of_ty t1) (string_of_ty t2)

let string_of_mode = Modes.Mode.to_string

let rec free_vars expr =
  match expr with
  | Var x -> StringSet.singleton x
  | Unit -> StringSet.empty
  | Absurd e -> free_vars e
  | Annot (e, _) -> free_vars e
  | Fun (x, body) -> StringSet.remove x (free_vars body)
  | App (fn, arg) -> StringSet.union (free_vars fn) (free_vars arg)
  | Let (x, e1, e2) ->
      StringSet.union (free_vars e1) (StringSet.remove x (free_vars e2))
  | LetPair (x1, x2, e1, e2) ->
      StringSet.union
        (free_vars e1)
        (free_vars e2 |> StringSet.remove x1 |> StringSet.remove x2)
  | Pair (left, right) ->
      StringSet.union (free_vars left) (free_vars right)
  | Inl e -> free_vars e
  | Inr e -> free_vars e
  | Match (scrut, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrut in
      let fv_e1 = StringSet.remove x1 (free_vars e1) in
      let fv_e2 = StringSet.remove x2 (free_vars e2) in
      StringSet.union fv_scrut (StringSet.union fv_e1 fv_e2)

(* -------------------------------------------------------------------------- *)
(* Modes and well-formedness                                                   *)
(* -------------------------------------------------------------------------- *)

let bottom_mode =
  { Modes.Mode.past = Modes.Past.bottom_in; future = Modes.Future.bottom_in }

let mode_of_storage { uniqueness; areality } =
  { Modes.Mode.past = { Modes.Past.bottom_in with uniqueness };
    future = { Modes.Future.bottom_in with areality } }

let rec mode_of_type ty =
  match ty with
  | TyUnit | TyEmpty -> bottom_mode
  | TyArrow (domain, arrow_mode, codomain) ->
      ignore (mode_of_type domain);
      ignore (mode_of_type codomain);
      { Modes.Mode.past = Modes.Past.bottom_in; future = arrow_mode }
  | TyPair (left, storage, right)
  | TySum (left, storage, right) ->
      let left_mode = mode_of_type left in
      let right_mode = mode_of_type right in
      let combined = Modes.Mode.join_in left_mode right_mode in
      let combined_uniqueness = combined.Modes.Mode.past.Modes.Past.uniqueness in
      let combined_areality = combined.Modes.Mode.future.Modes.Future.areality in
      if not (Modes.Uniqueness.leq_in combined_uniqueness storage.uniqueness) then
        raise
          (Mode_error
             (Printf.sprintf
                "Component uniqueness %s exceeds annotation %s"
                (Modes.Uniqueness.to_string combined_uniqueness)
                (Modes.Uniqueness.to_string storage.uniqueness)));
      if not (Modes.Areality.leq_in combined_areality storage.areality) then
        raise
          (Mode_error
             (Printf.sprintf
                "Component areality %s exceeds annotation %s"
                (Modes.Areality.to_string combined_areality)
                (Modes.Areality.to_string storage.areality)));
      Modes.Mode.join_in combined (mode_of_storage storage)

let ensure_well_formed ty =
  ignore (mode_of_type ty);
  ty

(* -------------------------------------------------------------------------- *)
(* Subtyping                                                                   *)
(* -------------------------------------------------------------------------- *)

let rec subtype t1 t2 =
  match (t1, t2) with
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyArrow (arg1, mode1, res1), TyArrow (arg2, mode2, res2) ->
      subtype arg2 arg1;
      subtype res1 res2;
      if not (Modes.Future.leq_to mode1 mode2) then
        raise (Error (Not_a_subtype (t1, t2)))
  | TyPair (l1, mode1, r1), TyPair (l2, mode2, r2)
  | TySum (l1, mode1, r1), TySum (l2, mode2, r2) ->
      subtype l1 l2;
      subtype r1 r2;
      if not (Modes.Uniqueness.leq_to mode1.uniqueness mode2.uniqueness)
         || not (Modes.Areality.leq_to mode1.areality mode2.areality)
      then raise (Error (Not_a_subtype (t1, t2)))
  | _ -> raise (Error (Not_a_subtype (t1, t2)))

(* -------------------------------------------------------------------------- *)
(* Core type checking                                                          *)
(* -------------------------------------------------------------------------- *)

let lookup env x =
  match List.assoc_opt x env with
  | Some ty -> ty
  | None -> raise (Error (Unbound_variable x))

let default_storage_mode =
  { uniqueness = Modes.Uniqueness.default; areality = Modes.Areality.default }

let make_pair_ty left storage right =
  let ty = TyPair (left, storage, right) in
  ignore (ensure_well_formed ty);
  ty

let make_sum_ty left storage right =
  let ty = TySum (left, storage, right) in
  ignore (ensure_well_formed ty);
  ty

let rec alias_type ty =
  match ty with
  | TyUnit | TyEmpty -> ty
  | TyArrow (domain, mode, codomain) ->
      ignore (ensure_well_formed domain);
      ignore (ensure_well_formed codomain);
      let linearity = mode.Modes.Future.linearity in
      if not (Modes.Linearity.leq_to linearity Modes.Linearity.default) then
        raise (Mode_error "Cannot alias a once-qualified function");
      TyArrow (domain, mode, codomain)
  | TyPair (left, storage, right) ->
      let left' = alias_type left in
      let right' = alias_type right in
      let storage' = { storage with uniqueness = Modes.Uniqueness.default } in
      make_pair_ty left' storage' right'
  | TySum (left, storage, right) ->
      let left' = alias_type left in
      let right' = alias_type right in
      let storage' = { storage with uniqueness = Modes.Uniqueness.default } in
      make_sum_ty left' storage' right'

let alias_env_for env vars =
  List.map
    (fun (x, ty) -> if StringSet.mem x vars then (x, alias_type ty) else (x, ty))
    env

let rec infer_expr env expr =
  match expr with
  | Var x -> lookup env x
  | Unit -> TyUnit
  | Absurd _ -> raise (Error (Cannot_infer "absurd"))
  | Fun _ -> raise (Error (Cannot_infer "function"))
  | App (fn, arg) ->
      let shared = StringSet.inter (free_vars fn) (free_vars arg) in
      let fn_ty = infer_expr env fn in
      (match fn_ty with
      | TyArrow (param, _, result) ->
          let arg_env = alias_env_for env shared in
          check_expr arg_env arg param;
          result
      | _ -> raise (Error (Expected_function fn_ty)))
  | Pair (left, right) ->
      let shared = StringSet.inter (free_vars left) (free_vars right) in
      let left_ty = infer_expr env left in
      let right_env = alias_env_for env shared in
      let right_ty = infer_expr right_env right in
      make_pair_ty left_ty default_storage_mode right_ty
  | Let (x, e1, e2) ->
      let shared =
        StringSet.inter (free_vars e1) (StringSet.remove x (free_vars e2))
      in
      let t1 = infer_expr env e1 in
      let env_e2 = alias_env_for env shared in
      infer_expr ((x, t1) :: env_e2) e2
  | LetPair (x1, x2, e1, e2) ->
      let shared =
        StringSet.inter (free_vars e1)
          (free_vars e2 |> StringSet.remove x1 |> StringSet.remove x2)
      in
      let t = infer_expr env e1 in
      (match t with
      | TyPair (t_left, _, t_right) ->
          let env_e2 = alias_env_for env shared in
          infer_expr ((x2, t_right) :: (x1, t_left) :: env_e2) e2
      | _ -> raise (Error (Expected_pair t)))
  | Inl _ -> raise (Error (Cannot_infer "left"))
  | Inr _ -> raise (Error (Cannot_infer "right"))
  | Match (scrutinee, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrutinee in
      let scrut_ty = infer_expr env scrutinee in
      (match scrut_ty with
      | TySum (left_ty, storage, right_ty) ->
          let fv_e1 = StringSet.remove x1 (free_vars e1) in
          let env_e1 = alias_env_for env (StringSet.inter fv_scrut fv_e1) in
          let branch_ty = infer_expr ((x1, left_ty) :: env_e1) e1 in
          ignore (ensure_well_formed branch_ty);
          let used = StringSet.union fv_scrut fv_e1 in
          let fv_e2 = StringSet.remove x2 (free_vars e2) in
          let env_e2 = alias_env_for env (StringSet.inter used fv_e2) in
          check_expr ((x2, right_ty) :: env_e2) e2 branch_ty;
          branch_ty
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (expr, ty) ->
      check_expr env expr ty;
      ty

and check_expr env expr ty =
  ignore (ensure_well_formed ty);
  match expr with
  | Unit -> subtype TyUnit ty
  | Absurd e -> check_expr env e TyEmpty
  | Fun (x, body) ->
      (match ty with
      | TyArrow (param, _, result) -> check_expr ((x, param) :: env) body result
      | _ -> raise (Error (Expected_function ty)))
  | Inl e ->
      (match ty with
      | TySum (left_ty, _, _) -> check_expr env e left_ty
      | _ -> raise (Error (Expected_sum ty)))
  | Inr e ->
      (match ty with
      | TySum (_, _, right_ty) -> check_expr env e right_ty
      | _ -> raise (Error (Expected_sum ty)))
  | Pair (left, right) ->
      (match ty with
      | TyPair (left_ty, _, right_ty) ->
          let shared = StringSet.inter (free_vars left) (free_vars right) in
          check_expr env left left_ty;
          let env_right = alias_env_for env shared in
          check_expr env_right right right_ty
      | _ -> raise (Error (Expected_pair ty)))
  | Let (x, e1, e2) ->
      let shared =
        StringSet.inter (free_vars e1) (StringSet.remove x (free_vars e2))
      in
      let t1 = infer_expr env e1 in
      let env_e2 = alias_env_for env shared in
      check_expr ((x, t1) :: env_e2) e2 ty
  | LetPair (x1, x2, e1, e2) ->
      let shared =
        StringSet.inter (free_vars e1)
          (free_vars e2 |> StringSet.remove x1 |> StringSet.remove x2)
      in
      let t = infer_expr env e1 in
      (match t with
      | TyPair (t_left, _, t_right) ->
          let env_e2 = alias_env_for env shared in
          check_expr ((x2, t_right) :: (x1, t_left) :: env_e2) e2 ty
      | _ -> raise (Error (Expected_pair t)))
  | Match (scrutinee, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrutinee in
      let scrut_ty = infer_expr env scrutinee in
      (match scrut_ty with
      | TySum (left_ty, _, right_ty) ->
          let fv_e1 = StringSet.remove x1 (free_vars e1) in
          let env_e1 = alias_env_for env (StringSet.inter fv_scrut fv_e1) in
          check_expr ((x1, left_ty) :: env_e1) e1 ty;
          let used = StringSet.union fv_scrut fv_e1 in
          let fv_e2 = StringSet.remove x2 (free_vars e2) in
          let env_e2 = alias_env_for env (StringSet.inter used fv_e2) in
          check_expr ((x2, right_ty) :: env_e2) e2 ty
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (expr, ty') ->
      check_expr env expr ty';
      subtype ty' ty
  | _ ->
      let inferred = infer_expr env expr in
      subtype inferred ty

(* -------------------------------------------------------------------------- *)
(* Public entry points                                                         *)
(* -------------------------------------------------------------------------- *)

let infer expr = infer_expr [] expr

let check_top expr ty = check_expr [] expr ty
