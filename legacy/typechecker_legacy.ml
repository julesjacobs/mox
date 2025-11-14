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
  | Expected_ref of ty
  | Cannot_infer of string
  | Not_a_subtype of ty * ty

exception Error of type_error
exception Mode_error of string

let string_of_ty = Pretty.string_of_ty
let string_of_mode = Modes.Mode.to_string
let string_of_future = Modes.Future.to_string

type lock_failure =
  { path : string list;
    message : string }

type tombstone =
  { original : ty;
    function_mode : Modes.Future.t;
    failure : lock_failure }

type binding =
  | Available of ty
  | Tombstone of tombstone

type env = (ident * binding) list

let empty_lock_failure message = { path = []; message }

let push_lock_path segment failure =
  { failure with path = segment :: failure.path }

let render_lock_failure failure =
  match List.rev failure.path with
  | [] -> failure.message
  | segments ->
      Printf.sprintf "%s (via %s)" failure.message (String.concat " -> " segments)

let mode_error_for_tombstone name tombstone =
  let reason = render_lock_failure tombstone.failure in
  let message =
    Printf.sprintf
      "Variable %s is unavailable inside a %s closure: %s. Captured value had \
       type %s."
      name (string_of_future tombstone.function_mode) reason
      (string_of_ty tombstone.original)
  in
  raise (Mode_error message)

let string_of_error = function
  | Unbound_variable x -> Printf.sprintf "Unbound variable %s" x
  | Expected_function ty ->
      Printf.sprintf "Expected a function type, found %s" (string_of_ty ty)
  | Expected_pair ty ->
      Printf.sprintf "Expected a pair type, found %s" (string_of_ty ty)
  | Expected_sum ty ->
      Printf.sprintf "Expected a sum type, found %s" (string_of_ty ty)
  | Expected_ref ty ->
      Printf.sprintf "Expected a reference type, found %s" (string_of_ty ty)
  | Cannot_infer what ->
      Printf.sprintf "Cannot infer the type of %s; add a type annotation" what
  | Not_a_subtype (t1, t2) ->
      Printf.sprintf "%s is not a subtype of %s"
        (string_of_ty t1) (string_of_ty t2)

let remove_vars vars set =
  List.fold_left (fun acc var -> StringSet.remove var acc) set vars

let rec free_vars expr =
  match expr with
  | Var x -> StringSet.singleton x
  | Unit -> StringSet.empty
  | Int _ -> StringSet.empty
  | IntAdd (lhs, rhs)
  | IntSub (lhs, rhs)
  | IntMul (lhs, rhs) ->
      StringSet.union (free_vars lhs) (free_vars rhs)
  | IntNeg e -> free_vars e
  | Hole -> StringSet.empty
  | Absurd e -> free_vars e
  | Annot (e, _) -> free_vars e
  | Fun (_, x, body) -> free_vars_without body [ x ]
  | App (fn, arg) -> StringSet.union (free_vars fn) (free_vars arg)
  | Let (_, x, e1, e2) ->
      StringSet.union (free_vars e1) (free_vars_without e2 [ x ])
  | LetPair (_, x1, x2, e1, e2) ->
      StringSet.union (free_vars e1) (free_vars_without e2 [ x1; x2 ])
  | Pair (_, left, right) ->
      StringSet.union (free_vars left) (free_vars right)
  | Inl (_, e) -> free_vars e
  | Inr (_, e) -> free_vars e
  | Region e -> free_vars e
  | Ref e -> free_vars e
  | Deref e -> free_vars e
  | Assign (lhs, rhs) -> StringSet.union (free_vars lhs) (free_vars rhs)
  | Fork e -> free_vars e
  | Match (_, scrut, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrut in
      let fv_e1 = free_vars_without e1 [ x1 ] in
      let fv_e2 = free_vars_without e2 [ x2 ] in
      StringSet.union fv_scrut (StringSet.union fv_e1 fv_e2)

and free_vars_without expr vars = remove_vars vars (free_vars expr)

(* -------------------------------------------------------------------------- *)
(* Modes and well-formedness                                                   *)
(* -------------------------------------------------------------------------- *)

let mode_of_storage ({ uniqueness; areality } : storage_mode) =
  let past = { Modes.Past.bottom_in with uniqueness } in
  let future = { Modes.Future.bottom_in with areality } in
  Modes.Mode.make ~past ~future

let mode_of_ref ({ contention } : ref_mode) =
  let past =
    Modes.Past.make
      ~uniqueness:Modes.Uniqueness.bottom_in
      ~contention
  in
  let bottom_future = Modes.Future.bottom_in in
  let future =
    Modes.Future.make
      ~linearity:bottom_future.Modes.Future.linearity
      ~portability:bottom_future.Modes.Future.portability
      ~areality:bottom_future.Modes.Future.areality
  in
  Modes.Mode.make ~past ~future

let mode_violation actual expected =
  Mode_error
    (Printf.sprintf "Mode %s exceeds allowed %s"
       (string_of_mode actual) (string_of_mode expected))

let ensure_mode_within actual expected =
  if Modes.Mode.leq_in actual expected then () else raise (mode_violation actual expected)

let component_expectation (storage : storage_mode) expected =
  let storage_mode = mode_of_storage storage in
  ensure_mode_within storage_mode expected;
  let open Modes in
  let { Mode.past = expected_past; future = expected_future } = expected in
  let component_past =
    Past.make
      ~uniqueness:(Uniqueness.meet_in expected_past.Past.uniqueness storage.uniqueness)
      ~contention:expected_past.Past.contention
  in
  let component_future =
    Future.make
      ~linearity:expected_future.Future.linearity
      ~portability:expected_future.Future.portability
      ~areality:(Areality.meet_in expected_future.Future.areality storage.areality)
  in
  Mode.make ~past:component_past ~future:component_future

let reference_expectation (ref_mode : ref_mode) expected =
  let ref_mode_as_mode = mode_of_ref ref_mode in
  ensure_mode_within ref_mode_as_mode expected;
  let open Modes in
  let { Mode.past = expected_past; future = expected_future } = expected in
  let payload_past =
    Past.make
      ~uniqueness:Uniqueness.aliased
      ~contention:(Contention.meet_in expected_past.Past.contention ref_mode.contention)
  in
  let payload_future =
    Future.make
      ~linearity:expected_future.Future.linearity
      ~portability:expected_future.Future.portability
      ~areality:Areality.global
  in
  Mode.make ~past:payload_past ~future:payload_future

let rec check_mode ty expected =
  match ty with
  | TyUnit | TyEmpty | TyInt -> ()
  | TyArrow (domain, arrow_mode, codomain) ->
      (* Check that the arrow mode does not exceed the expected mode *)
      let actual = Modes.Mode.make ~past:Modes.Past.bottom_in ~future:arrow_mode in
      ensure_mode_within actual expected;
      (* Check the domain and codomain at the top mode *)
      check_mode domain Modes.Mode.top_in;
      check_mode codomain Modes.Mode.top_in;
  | TyPair (left, storage, right) | TySum (left, storage, right) ->
      (* Check that the storage mode does not exceed the expected mode *)
      (* Check the components at the expected mode extended with the storage mode *)
      let component_expected = component_expectation storage expected in
      check_mode left component_expected;
      check_mode right component_expected
  | TyRef (payload, mode) ->
      let payload_expected = reference_expectation mode expected in
      check_mode payload payload_expected

let ensure_well_formed ty =
  check_mode ty Modes.Mode.top_in

let ensure_global_return ty =
  let open Modes in
  let top = Mode.top_in in
  let global_future =
    Future.make
      ~linearity:top.future.Future.linearity
      ~portability:top.future.Future.portability
      ~areality:Areality.global
  in
  let expected = Mode.make ~past:top.past ~future:global_future in
  check_mode ty expected

(* -------------------------------------------------------------------------- *)
(* Subtyping                                                                   *)
(* -------------------------------------------------------------------------- *)

let rec subtype t1 t2 =
  match (t1, t2) with
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyInt, TyInt -> ()
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
  | TyRef (payload1, mode1), TyRef (payload2, mode2) ->
      subtype payload1 payload2;
      if not (Modes.Contention.leq_to mode1.contention mode2.contention)
      then raise (Error (Not_a_subtype (t1, t2)))
  | _ -> raise (Error (Not_a_subtype (t1, t2)))

(* -------------------------------------------------------------------------- *)
(* Core type checking                                                          *)
(* -------------------------------------------------------------------------- *)

let lookup env x =
  match List.assoc_opt x env with
  | Some (Available ty) -> ty
  | Some (Tombstone tombstone) -> mode_error_for_tombstone x tombstone
  | None -> raise (Error (Unbound_variable x))

let default_storage_mode =
  { uniqueness = Unique; areality = Modes.Areality.default }

let stack_storage_mode =
  { uniqueness = Unique; areality = Modes.Areality.local }

let precise_ref_mode =
  { contention = Modes.Contention.uncontended }

let make_pair_ty left storage right =
  let ty = TyPair (left, storage, right) in
  ensure_well_formed ty;
  ty

let make_sum_ty left storage right =
  let ty = TySum (left, storage, right) in
  ensure_well_formed ty;
  ty

let make_ref_ty payload mode =
  let ty = TyRef (payload, mode) in
  ensure_well_formed ty;
  ty

let rec alias_type ty =
  match ty with
  | TyUnit | TyEmpty | TyInt -> ty
  | TyArrow (domain, mode, codomain) ->
      ensure_well_formed domain;
      ensure_well_formed codomain;
      let linearity = mode.Modes.Future.linearity in
      let mode =
        if Modes.Linearity.leq_to linearity Modes.Linearity.default then mode
        else
          { mode with Modes.Future.linearity = Modes.Linearity.top_to }
      in
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
  | TyRef (payload, mode) ->
      let payload' = alias_type payload in
      let mode' = { contention = Modes.Contention.contended } in
      make_ref_ty payload' mode'

let alias_env_for env vars =
  List.map
    (fun (x, binding) ->
      if StringSet.mem x vars then
        match binding with
        | Available ty -> (x, Available (alias_type ty))
        | Tombstone _ -> (x, binding)
      else (x, binding))
    env

let restrict_env env vars =
  if StringSet.is_empty vars then []
  else List.filter (fun (name, _) -> StringSet.mem name vars) env

let split_env env fv1 fv2 =
  let shared = StringSet.inter fv1 fv2 in
  let aliased_env = alias_env_for env shared in
  (restrict_env aliased_env fv1, restrict_env aliased_env fv2)

let linearity_dagger linearity =
  if Modes.Linearity.leq_to linearity Modes.Linearity.default then
    Modes.Uniqueness.default
  else
    Modes.Uniqueness.top_in

let portability_dagger portability =
  if Modes.Portability.equal portability Modes.Portability.portable then
    Modes.Contention.contended
  else
    Modes.Contention.uncontended

let rec lock_type mode ty =
  let linearity =
    let open Modes.Future in
    mode.linearity
  in
  let portability =
    let open Modes.Future in
    mode.portability
  in
  let mode_areality =
    let open Modes.Future in
    mode.areality
  in
  let ensure_storage_supported (storage : storage_mode) context =
    if Modes.Areality.leq_to storage.areality mode_areality then
      Ok ()
    else
      let storage_str = Modes.Areality.to_string storage.areality in
      let future_str = Modes.Areality.to_string mode_areality in
      Error
        (empty_lock_failure
           (Printf.sprintf
              "captured %s with %s areality cannot escape a closure whose future areality is %s"
              context storage_str future_str))
  in
  match ty with
  | TyUnit -> Ok TyUnit
  | TyEmpty -> Ok TyEmpty
  | TyInt -> Ok TyInt
  | TyArrow (_, arrow_mode, _) ->
      if Modes.Future.leq_to mode arrow_mode then Ok ty
      else
        Error
          (empty_lock_failure
             (Printf.sprintf
                "captured function expects mode %s, but closure runs at %s"
                (string_of_future arrow_mode) (string_of_future mode)))
  | TyPair (left, storage, right) ->
      let open Result in
      (match ensure_storage_supported storage "pair" with
      | Error failure -> Error failure
      | Ok () -> (
          match lock_type mode left with
          | Ok left_locked -> (
              match lock_type mode right with
              | Ok right_locked ->
                  let uniqueness =
                    Modes.Uniqueness.join_to storage.uniqueness
                      (linearity_dagger linearity)
                  in
                  let storage' = { storage with uniqueness } in
                  Ok (TyPair (left_locked, storage', right_locked))
              | Error failure -> Error (push_lock_path "pair.right" failure))
          | Error failure -> Error (push_lock_path "pair.left" failure)))
  | TySum (left, storage, right) ->
      let open Result in
      (match ensure_storage_supported storage "sum" with
      | Error failure -> Error failure
      | Ok () -> (
          match lock_type mode left with
          | Ok left_locked -> (
              match lock_type mode right with
              | Ok right_locked ->
                  let uniqueness =
                    Modes.Uniqueness.join_to storage.uniqueness
                      (linearity_dagger linearity)
                  in
                  let storage' = { storage with uniqueness } in
                  Ok (TySum (left_locked, storage', right_locked))
              | Error failure -> Error (push_lock_path "sum.right" failure))
          | Error failure -> Error (push_lock_path "sum.left" failure)))
  | TyRef (payload, ref_mode) ->
      let open Result in
      (match lock_type mode payload with
      | Ok locked_payload ->
          let contention =
            Modes.Contention.join_to ref_mode.contention
              (portability_dagger portability)
          in
          let ref_mode' = { contention } in
          Ok (TyRef (locked_payload, ref_mode'))
      | Error failure -> Error (push_lock_path "ref.payload" failure))

let lock_env mode env =
  List.map (fun (name, binding) ->
      match binding with
      | Available ty -> (
          match lock_type mode ty with
          | Ok locked_ty -> (name, Available locked_ty)
          | Error failure ->
              ( name,
                Tombstone
                  { original = ty; function_mode = mode; failure } ))
      | Tombstone _ -> (name, binding))
    env

let require_local_storage alloc context (storage : storage_mode) =
  match alloc with
  | Stack ->
      if not (Modes.Areality.equal storage.areality Modes.Areality.local) then
        raise
          (Mode_error
             (Printf.sprintf "Stack-allocated %s must have local storage" context))
  | Heap -> ()

let require_local_future alloc context future =
  match alloc with
  | Stack ->
      if not
           (Modes.Areality.equal future.Modes.Future.areality
              Modes.Areality.local)
      then
        raise
          (Mode_error
             (Printf.sprintf "Stack-allocated %s must have local areality" context))
  | Heap -> ()

let require_unique_storage_kind kind (storage : storage_mode) context =
  match kind with
  | Destructive ->
      if not (Modes.Uniqueness.equal storage.uniqueness Modes.Uniqueness.unique)
      then
        raise
          (Mode_error
             (Printf.sprintf "Destructive %s requires unique storage" context))
  | Regular -> ()

let rec infer_expr env expr =
  match expr with
  | Var x -> lookup env x
  | Unit -> TyUnit
  | Int _ -> TyInt
  | IntAdd (lhs, rhs)
  | IntSub (lhs, rhs)
  | IntMul (lhs, rhs) ->
      let fv_lhs = free_vars lhs in
      let fv_rhs = free_vars rhs in
      let env_lhs, env_rhs = split_env env fv_lhs fv_rhs in
      check_expr env_lhs lhs TyInt;
      check_expr env_rhs rhs TyInt;
      TyInt
  | IntNeg e ->
      check_expr env e TyInt;
      TyInt
  | Hole -> raise (Error (Cannot_infer "hole"))
  | Absurd _ -> raise (Error (Cannot_infer "absurd"))
  | Fun _ -> raise (Error (Cannot_infer "function"))
  | App (fn, arg) ->
      let fn_fv = free_vars fn in
      let arg_fv = free_vars arg in
      let env_fn, env_arg = split_env env fn_fv arg_fv in
      let fn_ty = infer_expr env_fn fn in
      (match fn_ty with
      | TyArrow (param, future, result) ->
          let linearity = future.Modes.Future.linearity in
          if Modes.Linearity.equal linearity Modes.Linearity.top_to then
            raise (Mode_error "Cannot call a never-qualified function");
          check_expr env_arg arg param;
          result
      | _ -> raise (Error (Expected_function fn_ty)))
  | Pair (alloc, left, right) ->
      let left_fv = free_vars left in
      let right_fv = free_vars right in
      let env_left, env_right = split_env env left_fv right_fv in
      let left_ty = infer_expr env_left left in
      let right_ty = infer_expr env_right right in
      let storage =
        match alloc with Stack -> stack_storage_mode | Heap -> default_storage_mode
      in
      make_pair_ty left_ty storage right_ty
  | Let (_, x, e1, e2) ->
      let fv_e1 = free_vars e1 in
      let fv_e2 = free_vars_without e2 [ x ] in
      let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
      let t1 = infer_expr env_e1 e1 in
      infer_expr ((x, Available t1) :: env_e2) e2
  | LetPair (kind, x1, x2, e1, e2) ->
      let fv_e1 = free_vars e1 in
      let fv_e2 = free_vars_without e2 [ x1; x2 ] in
      let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
      let t = infer_expr env_e1 e1 in
      (match t with
      | TyPair (t_left, storage, t_right) ->
          require_unique_storage_kind kind storage "pair binding";
          infer_expr
            ((x2, Available t_right) :: (x1, Available t_left) :: env_e2)
            e2
      | _ -> raise (Error (Expected_pair t)))
  | Inl _ -> raise (Error (Cannot_infer "left"))
  | Inr _ -> raise (Error (Cannot_infer "right"))
  | Region e ->
      let ty = infer_expr env e in
      ensure_global_return ty;
      ty
  | Ref e ->
      let payload = infer_expr env e in
      make_ref_ty payload precise_ref_mode
  | Deref e ->
      let ref_ty = infer_expr env e in
      (match ref_ty with
      | TyRef (payload, mode) ->
          if Modes.Contention.leq_to mode.contention Modes.Contention.shared then
            payload
          else
            raise
              (Mode_error
                 "Cannot read from a contended reference; capability must be shared or uncontended")
      | _ -> raise (Error (Expected_ref ref_ty)))
  | Assign (lhs, rhs) ->
      let fv_lhs = free_vars lhs in
      let fv_rhs = free_vars rhs in
      let env_lhs, env_rhs = split_env env fv_lhs fv_rhs in
      let lhs_ty = infer_expr env_lhs lhs in
      (match lhs_ty with
      | TyRef (payload, mode) ->
          if Modes.Contention.equal mode.contention Modes.Contention.uncontended then (
            check_expr env_rhs rhs payload;
            TyUnit)
          else
            raise
              (Mode_error
                 "Cannot write through a shared/contended reference; handle must be uncontended")
      | _ -> raise (Error (Expected_ref lhs_ty)))
  | Fork e ->
      let fv = free_vars e in
      let captured_env = restrict_env env fv in
      let rest_env =
        List.filter (fun (name, _) -> not (StringSet.mem name fv)) env
      in
      let port_mode =
        Modes.Future.make
          ~linearity:Modes.Linearity.many
          ~portability:Modes.Portability.portable
          ~areality:Modes.Areality.global
      in
      let locked_env = lock_env port_mode captured_env in
      let env' = locked_env @ rest_env in
      check_expr env' e TyUnit;
      TyUnit
  | Match (kind, scrutinee, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrutinee in
      let fv_e1 = free_vars_without e1 [ x1 ] in
      let fv_e2 = free_vars_without e2 [ x2 ] in
      let branches_fv = StringSet.union fv_e1 fv_e2 in
      let env_scrut, env_rest = split_env env fv_scrut branches_fv in
      let scrut_ty = infer_expr env_scrut scrutinee in
      (match scrut_ty with
      | TySum (left_ty, storage, right_ty) ->
          require_unique_storage_kind kind storage "match scrutinee";
          let env_branch1, env_branch2 = split_env env_rest fv_e1 fv_e2 in
          let branch_ty =
            infer_expr ((x1, Available left_ty) :: env_branch1) e1 in
          ensure_well_formed branch_ty;
          check_expr ((x2, Available right_ty) :: env_branch2) e2 branch_ty;
          branch_ty
      | _ -> raise (Error (Expected_sum scrut_ty)))
  | Annot (expr, ty) ->
      check_expr env expr ty;
      ty

and check_expr env expr ty =
  ensure_well_formed ty;
  match expr with
  | Unit -> subtype TyUnit ty
  | Int _ -> subtype TyInt ty
  | Hole -> ()
  | Absurd e -> check_expr env e TyEmpty
  | Fun (alloc, x, body) ->
      (match ty with
      | TyArrow (param, mode, result) ->
          let captured_vars = free_vars_without body [ x ] in
          let captured_env = restrict_env env captured_vars in
          require_local_future alloc "function" mode;
          let locked_env = lock_env mode captured_env in
          check_expr ((x, Available param) :: locked_env) body result
      | _ -> raise (Error (Expected_function ty)))
  | Inl (alloc, e) ->
      (match ty with
      | TySum (left_ty, storage, _) ->
          require_local_storage alloc "sum" storage;
          check_expr env e left_ty
      | _ -> raise (Error (Expected_sum ty)))
  | Inr (alloc, e) ->
      (match ty with
      | TySum (_, storage, right_ty) ->
          require_local_storage alloc "sum" storage;
          check_expr env e right_ty
      | _ -> raise (Error (Expected_sum ty)))
  | Pair (alloc, left, right) ->
      (match ty with
      | TyPair (left_ty, storage, right_ty) ->
          require_local_storage alloc "pair" storage;
          let left_fv = free_vars left in
          let right_fv = free_vars right in
          let env_left, env_right = split_env env left_fv right_fv in
          check_expr env_left left left_ty;
          check_expr env_right right right_ty
      | _ -> raise (Error (Expected_pair ty)))
  | Region e ->
      ensure_global_return ty;
      check_expr env e ty
  | Let (_, x, e1, e2) ->
      let fv_e1 = free_vars e1 in
      let fv_e2 = free_vars_without e2 [ x ] in
      let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
      let t1 = infer_expr env_e1 e1 in
      check_expr ((x, Available t1) :: env_e2) e2 ty
  | LetPair (kind, x1, x2, e1, e2) ->
      let fv_e1 = free_vars e1 in
      let fv_e2 = free_vars_without e2 [ x1; x2 ] in
      let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
      let t = infer_expr env_e1 e1 in
      (match t with
      | TyPair (t_left, storage, t_right) ->
          require_unique_storage_kind kind storage "pair binding";
          check_expr
            ((x2, Available t_right) :: (x1, Available t_left) :: env_e2)
            e2 ty
      | _ -> raise (Error (Expected_pair t)))
  | Match (kind, scrutinee, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrutinee in
      let fv_e1 = free_vars_without e1 [ x1 ] in
      let fv_e2 = free_vars_without e2 [ x2 ] in
      let branches_fv = StringSet.union fv_e1 fv_e2 in
      let env_scrut, env_rest = split_env env fv_scrut branches_fv in
      let scrut_ty = infer_expr env_scrut scrutinee in
      (match scrut_ty with
      | TySum (left_ty, storage, right_ty) ->
          require_unique_storage_kind kind storage "match scrutinee";
          let env_e1, env_e2 = split_env env_rest fv_e1 fv_e2 in
          check_expr ((x1, Available left_ty) :: env_e1) e1 ty;
          check_expr ((x2, Available right_ty) :: env_e2) e2 ty
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
exception Type_error of string
