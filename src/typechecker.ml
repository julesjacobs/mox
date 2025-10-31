open Ast

type type_error =
  | Unbound_variable of ident
  | Expected_function of ty
  | Expected_pair of ty
  | Expected_sum of ty
  | Cannot_infer of string
  | Not_a_subtype of ty * ty

exception Error of type_error
exception Mode_error of string

let lookup env x =
  let rec aux = function
    | [] -> raise (Error (Unbound_variable x))
    | (y, ty) :: rest -> if String.equal x y then ty else aux rest
  in
  aux env

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

let string_of_mode mode = Modes.Mode.to_string mode

let rec synth env expr =
  match expr with
  | Var x -> lookup env x
  | Unit -> TyUnit
  | Absurd _ -> raise (Error (Cannot_infer "absurd"))
  | Fun _ -> raise (Error (Cannot_infer "function"))
  | App (e1, e2) ->
      let tf = synth env e1 in
      (match tf with
      | TyArrow (targ, _, tres) ->
          check env e2 targ;
          tres
      | _ -> raise (Error (Expected_function tf)))
  | Pair (e1, e2) ->
      let t1 = synth env e1 in
      let t2 = synth env e2 in
      let mode =
        { uniqueness = Modes.Uniqueness.default; areality = Modes.Areality.default }
      in
      TyPair (t1, mode, t2)
  | Let (x, e1, e2) ->
      let t1 = synth env e1 in
      synth ((x, t1) :: env) e2
  | LetPair (x1, x2, e1, e2) ->
      let t = synth env e1 in
      (match t with
      | TyPair (t1, _, t2) -> synth ((x2, t2) :: (x1, t1) :: env) e2
      | _ -> raise (Error (Expected_pair t)))
  | Inl e ->
      ignore e;
      raise (Error (Cannot_infer "left"))
  | Inr e -> raise (Error (Cannot_infer "right"))
  | Match (scrut, x1, e1, x2, e2) ->
      let scrut_ty = synth env scrut in
      (match scrut_ty with
      | TySum (t_left, _, t_right) ->
          let t_branch = synth ((x1, t_left) :: env) e1 in
          check ((x2, t_right) :: env) e2 t_branch;
          t_branch
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (e, ty) ->
      check env e ty;
      ty

and mode_of_type ty =
  let bottom_mode = { Modes.Mode.past = Modes.Past.bottom_in; future = Modes.Future.bottom_in } in
  match ty with
  | TyUnit | TyEmpty -> bottom_mode
  | TyArrow (t1, arrow_mode, t2) ->
      ignore (mode_of_type t1);
      ignore (mode_of_type t2);
      { Modes.Mode.past = Modes.Past.bottom_in;
        future = Modes.Future.join_in arrow_mode Modes.Future.bottom_in }
  | TyPair (t1, annotation, t2) ->
      let mode_left = mode_of_type t1 in
      let mode_right = mode_of_type t2 in
      let combined = Modes.Mode.join_in mode_left mode_right in
      let { Modes.Mode.past = combined_past; future = combined_future } = combined in
      let combined_uniqueness = combined_past.uniqueness in
      let combined_areality = combined_future.areality in
      if not (Modes.Uniqueness.leq_in combined_uniqueness annotation.uniqueness) then
        raise
          (Mode_error
             (Printf.sprintf
                "Pair uniqueness %s exceeds annotation %s"
                (Modes.Uniqueness.to_string combined_uniqueness)
                (Modes.Uniqueness.to_string annotation.uniqueness)));
      if not (Modes.Areality.leq_in combined_areality annotation.areality) then
        raise
          (Mode_error
             (Printf.sprintf
                "Pair areality %s exceeds annotation %s"
                (Modes.Areality.to_string combined_areality)
                (Modes.Areality.to_string annotation.areality)));
      let annotation_mode =
        { Modes.Mode.past =
            { Modes.Past.bottom_in with uniqueness = annotation.uniqueness };
          future = { Modes.Future.bottom_in with areality = annotation.areality } }
      in
      Modes.Mode.join_in combined annotation_mode
  | TySum (t1, annotation, t2) ->
      let mode_left = mode_of_type t1 in
      let mode_right = mode_of_type t2 in
      let combined = Modes.Mode.join_in mode_left mode_right in
      let { Modes.Mode.past = combined_past; future = combined_future } = combined in
      let combined_uniqueness = combined_past.uniqueness in
      let combined_areality = combined_future.areality in
      if not (Modes.Uniqueness.leq_in combined_uniqueness annotation.uniqueness) then
        raise
          (Mode_error
             (Printf.sprintf
                "Sum uniqueness %s exceeds annotation %s"
                (Modes.Uniqueness.to_string combined_uniqueness)
                (Modes.Uniqueness.to_string annotation.uniqueness)));
      if not (Modes.Areality.leq_in combined_areality annotation.areality) then
        raise
          (Mode_error
             (Printf.sprintf
                "Sum areality %s exceeds annotation %s"
                (Modes.Areality.to_string combined_areality)
                (Modes.Areality.to_string annotation.areality)));
      let annotation_mode =
        { Modes.Mode.past =
            { Modes.Past.bottom_in with uniqueness = annotation.uniqueness };
          future = { Modes.Future.bottom_in with areality = annotation.areality } }
      in
      Modes.Mode.join_in combined annotation_mode

and subtype t1 t2 =
  match (t1, t2) with
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyArrow (a1, m1, b1), TyArrow (a2, m2, b2) ->
      subtype a2 a1;
      subtype b1 b2;
      if not (Modes.Future.leq_to m1 m2) then raise (Error (Not_a_subtype (t1, t2)))
  | TyPair (a1, m1, b1), TyPair (a2, m2, b2) ->
      subtype a1 a2;
      subtype b1 b2;
      if not (Modes.Uniqueness.leq_to m1.uniqueness m2.uniqueness)
         || not (Modes.Areality.leq_to m1.areality m2.areality)
      then raise (Error (Not_a_subtype (t1, t2)))
  | TySum (a1, m1, b1), TySum (a2, m2, b2) ->
      subtype a1 a2;
      subtype b1 b2;
      if not (Modes.Uniqueness.leq_to m1.uniqueness m2.uniqueness)
         || not (Modes.Areality.leq_to m1.areality m2.areality)
      then raise (Error (Not_a_subtype (t1, t2)))
  | _ -> raise (Error (Not_a_subtype (t1, t2)))

and check env expr ty =
  match expr with
  | Unit -> subtype TyUnit ty
  | Absurd e -> check env e TyEmpty
  | Fun (x, body) ->
      (match ty with
      | TyArrow (t_arg, _, t_res) -> check ((x, t_arg) :: env) body t_res
      | _ -> raise (Error (Expected_function ty)))
  | Inl e ->
      (match ty with
      | TySum (t_left, _, _) -> check env e t_left
      | _ -> raise (Error (Expected_sum ty)))
  | Inr e ->
      (match ty with
      | TySum (_, _, t_right) -> check env e t_right
      | _ -> raise (Error (Expected_sum ty)))
  | Pair (e1, e2) ->
      (match ty with
      | TyPair (t1, _, t2) ->
          check env e1 t1;
          check env e2 t2
      | _ -> raise (Error (Expected_pair ty)))
  | Let (x, e1, e2) ->
      let t1 = synth env e1 in
      check ((x, t1) :: env) e2 ty
  | LetPair (x1, x2, e1, e2) ->
      let t = synth env e1 in
      (match t with
      | TyPair (t1, _, t2) -> check ((x2, t2) :: (x1, t1) :: env) e2 ty
      | _ -> raise (Error (Expected_pair t)))
  | Match (scrut, x1, e1, x2, e2) ->
      let scrut_ty = synth env scrut in
      (match scrut_ty with
      | TySum (t_left, _, t_right) ->
          check ((x1, t_left) :: env) e1 ty;
          check ((x2, t_right) :: env) e2 ty
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (e, ty') ->
      check env e ty';
      subtype ty' ty
  | _ ->
      let inferred = synth env expr in
      subtype inferred ty

let infer expr = synth [] expr

let check_top expr ty = check [] expr ty
