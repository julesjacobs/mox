open Modes

(* -------------------------------------------------------------------------- *)
(* Mode descriptions shared by types and constraints. *)

(* Used on data types such as pairs and sums. *)
type storage_mode =
  { uniqueness : Modesolver.Uniqueness.var;
    areality : Modesolver.Areality.var }

(* Used on function types and lock constraints. *)
type future_mode =
  { linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

(* Used on meta-variables to constrain contents via the <=in relation. *)
type mode_vars =
  { uniqueness : Modesolver.Uniqueness.var;
    contention : Modesolver.Contention.var;
    linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

(* -------------------------------------------------------------------------- *)
(* Types and metas. *)

type ty =
  | TyUnit
  | TyEmpty
  | TyArrow of ty * future_mode * ty
  | TyPair of ty * storage_mode * ty
  | TySum of ty * storage_mode * ty
  | TyMeta of meta

and meta =
  { id : int;
    mutable solution : ty option;
    mutable constraints : constraint_record list }

and constraint_ =
  | Sub of
      { lower : meta;
        upper : meta }
  | Alias of
      { source : meta;
        target : meta }
  | Lock of
      { original : meta;
        locked : meta;
        future : future_mode }
  | In of 
      { target : meta;
        mode_vars : mode_vars }

and constraint_record =
  { constraint_ : constraint_;
    mutable fired : bool }

let mk_constraint constraint_ =
  { constraint_; fired = false }

(* -------------------------------------------------------------------------- *)
(* Fresh variable helpers. *)

let fresh_storage_mode () : storage_mode =
  { uniqueness = Modesolver.Uniqueness.new_var ();
    areality = Modesolver.Areality.new_var () }

let fresh_future_mode () : future_mode =
  { linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var () }

let fresh_mode_vars () : mode_vars =
  { uniqueness = Modesolver.Uniqueness.new_var ();
    contention = Modesolver.Contention.new_var ();
    linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var () }

let fresh_meta_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

let fresh_meta ?solution ?(constraints = []) () : meta =
  { id = fresh_meta_id ();
    solution;
    constraints }

(* -------------------------------------------------------------------------- *)
(* Constraint management. *)

let add_constraint meta constraint_ =
  if List.exists (fun existing -> existing = constraint_) meta.constraints then ()
  else meta.constraints <- constraint_ :: meta.constraints

let add_constraints meta constraints =
  List.iter (add_constraint meta) constraints

(* -------------------------------------------------------------------------- *)
(* Mode helpers                                                               *)

let assert_storage_leq_to (lower : storage_mode) (upper : storage_mode) =
  Modesolver.Uniqueness.assert_leq_to lower.uniqueness upper.uniqueness;
  Modesolver.Areality.assert_leq_to lower.areality upper.areality

let assert_future_leq_to (lower : future_mode) (upper : future_mode) =
  Modesolver.Linearity.assert_leq_to lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_to lower.portability upper.portability;
  Modesolver.Areality.assert_leq_to lower.areality upper.areality

let assert_aliased (uniqueness : Modesolver.Uniqueness.var) =
  Modesolver.Uniqueness.restrict_domain [Uniqueness.aliased] uniqueness

let assert_equal_areality (left : Modesolver.Areality.var) (right : Modesolver.Areality.var) =
  Modesolver.Areality.assert_leq_to left right;
  Modesolver.Areality.assert_leq_to right left

let assert_equal_portability (left : Modesolver.Portability.var) (right : Modesolver.Portability.var) =
  Modesolver.Portability.assert_leq_to left right;
  Modesolver.Portability.assert_leq_to right left

let assert_many (linearity : Modesolver.Linearity.var) =
  Modesolver.Linearity.restrict_domain [Linearity.many] linearity

(* -------------------------------------------------------------------------- *)
(* Error reporting.                                                           *)

type error = string

exception Error of error

let string_of_error err = err

let type_error message = raise (Error message)

(* -------------------------------------------------------------------------- *)


let rec zonk ty =
  match ty with
  | TyMeta meta ->
    (match meta.solution with
    | Some solution -> zonk solution
    | None -> ty)
  | _ -> ty

let rec assert_in ty mode_vars =
  match zonk ty with
  | TyMeta meta ->
    (* Add constraint to meta *)
    add_constraint meta (mk_constraint (In { target = meta; mode_vars = mode_vars }))
  | TyUnit -> ()
  | TyEmpty -> ()
  | TyPair (left, storage, right) ->
    failwith "TODO"
  | TySum (left, storage, right) ->
    failwith "TODO"
  | TyArrow (domain, future, codomain) ->
    failwith "TODO"

(* Makes the outer type constructors equivalent. *)
let outer_equiv ty1 ty2 =
  match (zonk ty1, zonk ty2) with
  | TyMeta meta1, TyMeta meta2 -> ()
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair _, TyPair _ -> ()
  | TySum _, TySum _ -> ()
  | TyArrow _, TyArrow _ -> ()
  | TyUnit, TyMeta meta | TyMeta meta, TyUnit ->
    meta.solution <- Some TyUnit
  | TyEmpty, TyMeta meta | TyMeta meta, TyEmpty ->
    meta.solution <- Some TyEmpty
  | TyPair _, TyMeta meta | TyMeta meta, TyPair _ ->
    let storage = fresh_storage_mode () in
    let left = fresh_meta () in
    let right = fresh_meta () in
    meta.solution <- Some (TyPair (TyMeta left, storage, TyMeta right))
  | TySum _, TyMeta meta | TyMeta meta, TySum _ ->
    let storage = fresh_storage_mode () in
    let left = fresh_meta () in
    let right = fresh_meta () in
    meta.solution <- Some (TySum (TyMeta left, storage, TyMeta right))
  | TyArrow _, TyMeta meta | TyMeta meta, TyArrow _ ->
    let future = fresh_future_mode () in
    let domain = fresh_meta () in
    let codomain = fresh_meta () in
    meta.solution <- Some (TyArrow (TyMeta domain, future, TyMeta codomain))
  | _ ->
    type_error "outer_equiv: not equivalent"

let rec assert_subtype lower upper =
  outer_equiv lower upper;
  match (zonk lower, zonk upper) with
  | TyMeta lower_meta, TyMeta upper_meta ->
    let constraint_ = mk_constraint (Sub { lower = lower_meta; upper = upper_meta }) in
    add_constraint lower_meta constraint_;
    add_constraint upper_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair (lower_left, lower_storage, lower_right), TyPair (upper_left, upper_storage, upper_right) ->
    assert_subtype lower_left upper_left;
    assert_subtype lower_right upper_right;
    assert_storage_leq_to lower_storage upper_storage
  | TySum (lower_left, lower_storage, lower_right), TySum (upper_left, upper_storage, upper_right) ->
    assert_subtype lower_left upper_left;
    assert_subtype lower_right upper_right;
    assert_storage_leq_to lower_storage upper_storage
  | TyArrow (lower_domain, lower_future, lower_codomain), TyArrow (upper_domain, upper_future, upper_codomain) ->
    assert_subtype upper_domain lower_domain;
    assert_subtype lower_codomain upper_codomain;
    assert_future_leq_to lower_future upper_future
  | _ ->
    type_error "assert_subtype: not a subtype"

let rec assert_alias source target = 
  outer_equiv source target;
  match (zonk source, zonk target) with
  | TyMeta source_meta, TyMeta target_meta ->
    let constraint_ = mk_constraint (Alias { source = source_meta; target = target_meta }) in
    add_constraint source_meta constraint_;
    add_constraint target_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair (source_left, source_storage, source_right), TyPair (target_left, target_storage, target_right) ->
    (* Make sure target_storage is aliased, areality is copied. *)
    assert_aliased target_storage.uniqueness;
    assert_equal_areality source_storage.areality target_storage.areality;
    assert_alias source_left target_left;
    assert_alias source_right target_right;
  | TySum (source_left, source_storage, source_right), TySum (target_left, target_storage, target_right) ->
    (* Similar to pair. *)
    assert_aliased target_storage.uniqueness;
    assert_equal_areality source_storage.areality target_storage.areality;
    assert_alias source_left target_left;
    assert_alias source_right target_right;
  | TyArrow (source_domain, source_future, source_codomain), TyArrow (target_domain, target_future, target_codomain) ->
    (* Make sure that source_future is many. *)
    assert_many source_future.linearity;
    assert_equal_areality source_future.areality target_future.areality;
    assert_equal_portability source_future.portability target_future.portability;
  | _ ->
    type_error "assert_alias: not equivalent"

let assert_lock original locked future =
  outer_equiv original locked;
  match (zonk original, zonk locked) with
  | TyMeta original_meta, TyMeta locked_meta ->
    let constraint_ = mk_constraint (Lock { original = original_meta; locked = locked_meta; future = future }) in
    add_constraint original_meta constraint_;
    add_constraint locked_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair (original_left, original_storage, original_right), TyPair (locked_left, locked_storage, locked_right) ->
    failwith "TODO"
  | TySum (original_left, original_storage, original_right), TySum (locked_left, locked_storage, locked_right) ->
    failwith "TODO"
  | TyArrow (original_domain, original_future, original_codomain), TyArrow (locked_domain, locked_future, locked_codomain) ->
    failwith "TODO"
  | _ ->
    type_error "assert_lock: not equivalent"

(* -------------------------------------------------------------------------- *)
(* Converting annotated syntax *)

let const_uniqueness_var value =
  Modesolver.Uniqueness.new_var ~domain:[value] ()

let const_areality_var value =
  Modesolver.Areality.new_var ~domain:[value] ()

let const_linearity_var value =
  Modesolver.Linearity.new_var ~domain:[value] ()

let const_portability_var value =
  Modesolver.Portability.new_var ~domain:[value] ()

let storage_mode_of_ast (storage : Ast.storage_mode) : storage_mode =
  { uniqueness = const_uniqueness_var storage.uniqueness;
    areality = const_areality_var storage.areality }

let future_mode_of_ast (future : Future.t) : future_mode =
  { linearity = const_linearity_var future.linearity;
    portability = const_portability_var future.portability;
    areality = const_areality_var future.areality }

let rec ty_of_ast (ty_syntax : Ast.ty) : ty =
  match ty_syntax with
  | Ast.TyUnit -> TyUnit
  | Ast.TyEmpty -> TyEmpty
  | Ast.TyPair (left, storage, right) ->
      let left' = ty_of_ast left in
      let right' = ty_of_ast right in
      let storage' = storage_mode_of_ast storage in
      TyPair (left', storage', right')
  | Ast.TySum (left, storage, right) ->
      let left' = ty_of_ast left in
      let right' = ty_of_ast right in
      let storage' = storage_mode_of_ast storage in
      TySum (left', storage', right')
  | Ast.TyArrow (domain, future, codomain) ->
      let domain' = ty_of_ast domain in
      let codomain' = ty_of_ast codomain in
      let future' = future_mode_of_ast future in
      TyArrow (domain', future', codomain')

(* -------------------------------------------------------------------------- *)
(* Pretty-printing inference types.                                           *)

let rec string_of_ty ty =
  match zonk ty with
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
  | TyArrow (domain, _, codomain) ->
      Printf.sprintf "(%s -> %s)" (string_of_ty domain) (string_of_ty codomain)
  | TyPair (left, _, right) ->
      Printf.sprintf "(%s * %s)" (string_of_ty left) (string_of_ty right)
  | TySum (left, _, right) ->
      Printf.sprintf "(%s + %s)" (string_of_ty left) (string_of_ty right)
  | TyMeta meta ->
      (match meta.solution with
      | Some solution -> string_of_ty solution
      | None -> Printf.sprintf "?%d" meta.id)

(* -------------------------------------------------------------------------- *)
(* Environments                                                               *)

let rec lookup env name =
  match env with
  | [] -> None
  | (bound, ty) :: rest -> if String.equal bound name then Some ty else lookup rest name


let rec infer_with_env env expr = 
  match expr with
  | Ast.Var x ->
    (match lookup env x with
    | Some ty -> ty
    | None -> type_error (Printf.sprintf "Unbound variable %s" x))
  | Ast.Unit -> TyUnit
  | Ast.Pair (e1, e2) ->
    let ty1 = infer_with_env env e1 in
    let ty2 = infer_with_env env e2 in
    let storage = fresh_storage_mode () in
    let ty = TyPair (ty1, storage, ty2) in
    ty
  | Ast.Inl e ->
    let ty_left = infer_with_env env e in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let ty = TySum (ty_left, storage, ty_right) in
    ty
  | Ast.Inr e ->
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = infer_with_env env e in
    let storage = fresh_storage_mode () in
    let ty = TySum (ty_left, storage, ty_right) in
    ty
  | Ast.Hole -> TyMeta (fresh_meta ())
  | Ast.Absurd e ->
    let ty = infer_with_env env e in
    assert_subtype ty TyEmpty;
    TyMeta (fresh_meta ())
  | Ast.Let (x, e1, e2) ->
    let ty1 = infer_with_env env e1 in
    let env' = (x, ty1) :: env in
    infer_with_env env' e2
    (* TODO: aliasing *)
  | Ast.LetPair (x1, x2, e1, e2) ->
    let ty1 = infer_with_env env e1 in
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let ty_pair = TyPair (ty_left, storage, ty_right) in
    assert_subtype ty1 ty_pair;
    let env' = (x1, ty_left) :: (x2, ty_right) :: env in
    infer_with_env env' e2
    (* TODO: aliasing *)
  | Ast.Match (e, x1, e1, x2, e2) ->
    let ty_scrut = infer_with_env env e in
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let ty_sum = TySum (ty_left, storage, ty_right) in
    assert_subtype ty_scrut ty_sum;
    let env1 = (x1, ty_left) :: env in
    let env2 = (x2, ty_right) :: env in
    let ty1 = infer_with_env env1 e1 in
    let ty2 = infer_with_env env2 e2 in
    let ty_join = TyMeta (fresh_meta ()) in
    assert_subtype ty1 ty_join;
    assert_subtype ty2 ty_join;
    ty_join
    (* TODO: aliasing *)
  | Ast.App (e1, e2) ->
    let ty1 = infer_with_env env e1 in
    let ty2 = infer_with_env env e2 in
    let ty_dom = TyMeta (fresh_meta ()) in
    let ty_cod = TyMeta (fresh_meta ()) in
    let future = fresh_future_mode () in
    let ty_f = TyArrow (ty_dom, future, ty_cod) in
    assert_subtype ty1 ty_f;
    assert_subtype ty2 ty_dom;
    ty_cod
  | Ast.Fun (x, e) ->
    let ty_param = TyMeta (fresh_meta ()) in
    let env' = (x, ty_param) :: env in
    let ty_body = infer_with_env env' e in
    let future = fresh_future_mode () in
    let ty_arrow = TyArrow (ty_param, future, ty_body) in
    ty_arrow
    (* TODO: aliasing + locking *)
  | Ast.Annot (e, ty_syntax) ->
    let ty = ty_of_ast ty_syntax in
    let ty' = infer_with_env env e in
    assert_subtype ty' ty;
    ty'

let infer expr =
  try infer_with_env [] expr with
  | Modesolver.Inconsistent msg -> type_error msg
