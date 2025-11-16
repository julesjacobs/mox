open Modes

module StringSet = Set.Make (String)
let remove_vars vars set =
  List.fold_left (fun acc var -> StringSet.remove var acc) set vars

let rec free_vars expr =
  match expr with
  | Ast.Var x -> StringSet.singleton x
  | Ast.Borrow (x, e1, y, e2, e3) ->
      let fv_e1 = free_vars e1 in
      let fv_e2 = free_vars_without e2 [ x ] in
      let fv_e3 = free_vars_without e3 [ x; y ] in
      let fv_rest = StringSet.union fv_e2 fv_e3 in
      StringSet.union fv_e1 fv_rest
  | Ast.Unit -> StringSet.empty
  | Ast.Bool _ -> StringSet.empty
  | Ast.If (cond, t_branch, e_branch) ->
      let fv_cond = free_vars cond in
      let fv_t = free_vars t_branch in
      let fv_e = free_vars e_branch in
      StringSet.union fv_cond (StringSet.union fv_t fv_e)
  | Ast.BinOp (lhs, _, rhs) ->
      StringSet.union (free_vars lhs) (free_vars rhs)
  | Ast.ListNil -> StringSet.empty
  | Ast.ListCons (_, head, tail) ->
      StringSet.union (free_vars head) (free_vars tail)
  | Ast.MatchList (_, scrut, nil_branch, x, xs, cons_branch) ->
      let fv_scrut = free_vars scrut in
      let fv_nil = free_vars nil_branch in
      let fv_cons = free_vars_without cons_branch [ x; xs ] in
      StringSet.union fv_scrut (StringSet.union fv_nil fv_cons)
  | Ast.Int _ -> StringSet.empty
  | Ast.IntNeg e -> free_vars e
  | Ast.BoolNot e -> free_vars e
  | Ast.Hole -> StringSet.empty
  | Ast.Absurd e -> free_vars e
  | Ast.Annot (e, _) -> free_vars e
  | Ast.Fun (_, x, body) -> free_vars_without body [ x ]
  | Ast.FunRec (_, f, x, body) -> free_vars_without body [ f; x ]
  | Ast.App (fn, arg) -> StringSet.union (free_vars fn) (free_vars arg)
  | Ast.Let (_, x, e1, e2) ->
      StringSet.union (free_vars e1) (free_vars_without e2 [ x ])
  | Ast.LetPair (_, x1, x2, e1, e2) ->
      StringSet.union (free_vars e1) (free_vars_without e2 [ x1; x2 ])
  | Ast.Pair (_, left, right) ->
      StringSet.union (free_vars left) (free_vars right)
  | Ast.Inl (_, e) -> free_vars e
  | Ast.Inr (_, e) -> free_vars e
  | Ast.Region e -> free_vars e
  | Ast.Ref e -> free_vars e
  | Ast.Deref e -> free_vars e
  | Ast.Assign (lhs, rhs) -> StringSet.union (free_vars lhs) (free_vars rhs)
  | Ast.Fork e -> free_vars e
  | Ast.Match (_, scrut, x1, e1, x2, e2) ->
      let fv_scrut = free_vars scrut in
      let fv_e1 = free_vars_without e1 [ x1 ] in
      let fv_e2 = free_vars_without e2 [ x2 ] in
      StringSet.union fv_scrut (StringSet.union fv_e1 fv_e2)

and free_vars_without expr vars = remove_vars vars (free_vars expr)

(* -------------------------------------------------------------------------- *)
(* Mode descriptions shared by types and constraints. *)

(* Used on data types such as pairs and sums. *)
type storage_mode =
  { uniqueness : Modesolver.Uniqueness.var;
    areality : Modesolver.Areality.var }

type ref_mode =
  { contention : Modesolver.Contention.var }

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
  | TyInt
  | TyBool
  | TyList of ty * storage_mode
  | TyArrow of ty * future_mode * ty
  | TyPair of ty * storage_mode * ty
  | TySum of ty * storage_mode * ty
  | TyRef of ty * ref_mode
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

let fresh_ref_mode () : ref_mode =
  { contention = Modesolver.Contention.new_var () }

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

let force_storage_local (storage : storage_mode) =
  Modesolver.Areality.restrict_domain [Areality.local] storage.areality

let force_future_local (future : future_mode) =
  Modesolver.Areality.restrict_domain [Areality.local] future.areality

let force_storage_unique (storage : storage_mode) =
  Modesolver.Uniqueness.restrict_domain [Uniqueness.unique] storage.uniqueness
module Mode_consts = struct
  let uniqueness value = Modesolver.Uniqueness.new_var ~domain:[value] ()
  let contention value = Modesolver.Contention.new_var ~domain:[value] ()
  let areality value = Modesolver.Areality.new_var ~domain:[value] ()
  let linearity value = Modesolver.Linearity.new_var ~domain:[value] ()
  let portability value = Modesolver.Portability.new_var ~domain:[value] ()
end

let const_ref_mode ~contention : ref_mode =
  { contention = Mode_consts.contention contention }

let precise_ref_mode () =
  const_ref_mode ~contention:Contention.uncontended

let nonborrowed_arealities =
  [ Areality.global; Areality.regional; Areality.local ]

let nonborrowed_mode_vars () : mode_vars =
  let mode = fresh_mode_vars () in
  Modesolver.Areality.restrict_domain nonborrowed_arealities mode.areality;
  mode

let borrowed_mode_vars () : mode_vars =
  let mode = fresh_mode_vars () in
  Modesolver.Areality.restrict_domain [Areality.borrowed] mode.areality;
  mode

let many_mode_vars () : mode_vars =
  let mode = fresh_mode_vars () in
  Modesolver.Linearity.restrict_domain [Linearity.many] mode.linearity;
  mode

let global_mode_vars () : mode_vars =
  let mode = fresh_mode_vars () in
  { mode with areality = Mode_consts.areality Areality.global }

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
  meta.constraints <- constraint_ :: meta.constraints

(* -------------------------------------------------------------------------- *)
(* Mode helpers                                                               *)

let assert_storage_leq_to (lower : storage_mode) (upper : storage_mode) =
  Modesolver.Uniqueness.assert_leq_to lower.uniqueness upper.uniqueness;
  Modesolver.Areality.assert_leq_to lower.areality upper.areality

let assert_ref_leq_to (lower : ref_mode) (upper : ref_mode) =
  Modesolver.Contention.assert_leq_to lower.contention upper.contention

let assert_future_leq_to (lower : future_mode) (upper : future_mode) =
  Modesolver.Linearity.assert_leq_to lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_to lower.portability upper.portability;
  Modesolver.Areality.assert_leq_to lower.areality upper.areality

let assert_aliased (uniqueness : Modesolver.Uniqueness.var) =
  Modesolver.Uniqueness.restrict_domain [Uniqueness.aliased] uniqueness

let assert_equal_in assert_leq var1 var2 =
  assert_leq var1 var2;
  assert_leq var2 var1

(* -------------------------------------------------------------------------- *)
(* Error reporting.                                                           *)

type error = string

exception Error of error

let string_of_error err = err

let type_error message = raise (Error message)

(* Probe for unused-value warnings; intentionally unused. *)
let rec zonk ty =
  match ty with
  | TyMeta meta ->
    (match meta.solution with
    | Some solution -> zonk solution
    | None -> ty)
  | _ -> ty

let assert_storage_within (storage : storage_mode) (mode_vars : mode_vars) =
  (* Enforce ŝ ≤₍in₎ m, where ŝ embeds the storage annotation. *)
  Modesolver.Uniqueness.assert_leq_in storage.uniqueness mode_vars.uniqueness;
  Modesolver.Areality.assert_leq_in storage.areality mode_vars.areality

let push_storage_to_components (storage : storage_mode) (container_mode : mode_vars) =
  (* Computes m ∧ ŝ: components inherit the container's ambient constraints and
     meet them with the storage annotation (see tex/mox.tex §Kinding). *)
  let component_mode = fresh_mode_vars () in
  Modesolver.Uniqueness.assert_leq_in component_mode.uniqueness storage.uniqueness;
  Modesolver.Uniqueness.assert_leq_in component_mode.uniqueness container_mode.uniqueness;
  Modesolver.Areality.assert_leq_in component_mode.areality storage.areality;
  Modesolver.Areality.assert_leq_in component_mode.areality container_mode.areality;
  assert_equal_in Modesolver.Contention.assert_leq_in component_mode.contention container_mode.contention;
  assert_equal_in Modesolver.Linearity.assert_leq_in component_mode.linearity container_mode.linearity;
  assert_equal_in Modesolver.Portability.assert_leq_in component_mode.portability container_mode.portability;
  component_mode

let assert_ref_within (ref_mode : ref_mode) (mode_vars : mode_vars) =
  Modesolver.Contention.assert_leq_in ref_mode.contention mode_vars.contention

let push_ref_to_payload (ref_mode : ref_mode) (container_mode : mode_vars) =
  let payload_mode = fresh_mode_vars () in
  Modesolver.Contention.assert_leq_in payload_mode.contention ref_mode.contention;
  Modesolver.Contention.assert_leq_in payload_mode.contention container_mode.contention;
  Modesolver.Uniqueness.restrict_domain [Uniqueness.aliased] payload_mode.uniqueness;
  Modesolver.Areality.restrict_domain [Areality.global] payload_mode.areality;
  Modesolver.Linearity.restrict_domain [Linearity.many] payload_mode.linearity;
  assert_equal_in Modesolver.Portability.assert_leq_in payload_mode.portability container_mode.portability;
  payload_mode

let rec assert_in ty mode_vars =
  match zonk ty with
  | TyMeta meta ->
    (* Record α : m by attaching an in-placement constraint to the meta. *)
    add_constraint meta (mk_constraint (In { target = meta; mode_vars }))
  | TyUnit -> ()
  | TyEmpty -> ()
  | TyInt -> ()
  | TyBool -> ()
  | TyPair (left, storage, right)
  | TySum (left, storage, right) ->
    assert_storage_within storage mode_vars;
    let component_mode = push_storage_to_components storage mode_vars in
    assert_in left component_mode;
    assert_in right component_mode
  | TyList (elem, storage) ->
    assert_storage_within storage mode_vars;
    let component_mode = push_storage_to_components storage mode_vars in
    assert_in elem component_mode
  | TyRef (payload, ref_mode) ->
    assert_ref_within ref_mode mode_vars;
    let payload_mode = push_ref_to_payload ref_mode mode_vars in
    assert_in payload payload_mode
  | TyArrow (domain, future, codomain) ->
    (* \hat{f} ≤₍in₎ m *)
    Modesolver.Areality.assert_leq_in future.areality mode_vars.areality;
    Modesolver.Linearity.assert_leq_in future.linearity mode_vars.linearity;
    Modesolver.Portability.assert_leq_in future.portability mode_vars.portability

let mk_pair left storage right =
  let ty = TyPair (left, storage, right) in
  assert_in ty (fresh_mode_vars ());
  ty

let mk_sum left storage right =
  let ty = TySum (left, storage, right) in
  assert_in ty (fresh_mode_vars ());
  ty

let mk_list elem storage =
  let ty = TyList (elem, storage) in
  assert_in ty (fresh_mode_vars ());
  ty

let mk_ref payload ref_mode =
  let ty = TyRef (payload, ref_mode) in
  assert_in ty (fresh_mode_vars ());
  ty

let debug_lock_enabled =
  match Sys.getenv_opt "MOX_DEBUG_LOCK" with
  | Some ("0" | "" ) -> false
  | Some _ -> true
  | None -> false

let log_lock fmt =
  if debug_lock_enabled then
    Printf.ksprintf (fun s -> prerr_endline ("[lock] " ^ s)) fmt
  else
    Printf.ksprintf (fun _ -> ()) fmt

let rec string_of_ty_shallow ty =
  match zonk ty with
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyArrow (domain, _, codomain) ->
      Printf.sprintf "(%s -> %s)" (string_of_ty_shallow domain) (string_of_ty_shallow codomain)
  | TyPair (left, _, right) ->
      Printf.sprintf "(%s * %s)" (string_of_ty_shallow left) (string_of_ty_shallow right)
  | TySum (left, _, right) ->
      Printf.sprintf "(%s + %s)" (string_of_ty_shallow left) (string_of_ty_shallow right)
  | TyList (elem, _) ->
      Printf.sprintf "(list %s)" (string_of_ty_shallow elem)
  | TyRef (payload, _) ->
      Printf.sprintf "(ref %s)" (string_of_ty_shallow payload)
  | TyMeta meta ->
      (match meta.solution with
      | Some solution -> string_of_ty_shallow solution
      | None -> Printf.sprintf "?%d" meta.id)

(* Core constraint propagation and meta assignment. *)
let rec outer_equiv ty1 ty2 =
  match (zonk ty1, zonk ty2) with
  | TyMeta meta1, TyMeta meta2 -> ()
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyInt, TyInt -> ()
  | TyBool, TyBool -> ()
  | TyList _, TyList _ -> ()
  | TyPair _, TyPair _ -> ()
  | TySum _, TySum _ -> ()
  | TyRef _, TyRef _ -> ()
  | TyArrow _, TyArrow _ -> ()
  | TyUnit, TyMeta meta | TyMeta meta, TyUnit ->
      set_meta_solution meta TyUnit
  | TyEmpty, TyMeta meta | TyMeta meta, TyEmpty ->
      set_meta_solution meta TyEmpty
  | TyInt, TyMeta meta | TyMeta meta, TyInt ->
      set_meta_solution meta TyInt
  | TyBool, TyMeta meta | TyMeta meta, TyBool ->
      set_meta_solution meta TyBool
  | TyList _, TyMeta meta | TyMeta meta, TyList _ ->
      let elem = fresh_meta () in
      let storage = fresh_storage_mode () in
      set_meta_solution meta (mk_list (TyMeta elem) storage)
  | TyPair _, TyMeta meta | TyMeta meta, TyPair _ ->
      let storage = fresh_storage_mode () in
      let left = fresh_meta () in
      let right = fresh_meta () in
      set_meta_solution meta (mk_pair (TyMeta left) storage (TyMeta right))
  | TySum _, TyMeta meta | TyMeta meta, TySum _ ->
      let storage = fresh_storage_mode () in
      let left = fresh_meta () in
      let right = fresh_meta () in
      set_meta_solution meta (mk_sum (TyMeta left) storage (TyMeta right))
  | TyRef _, TyMeta meta | TyMeta meta, TyRef _ ->
      let payload = fresh_meta () in
      let ref_mode = fresh_ref_mode () in
      set_meta_solution meta (mk_ref (TyMeta payload) ref_mode)
  | TyArrow _, TyMeta meta | TyMeta meta, TyArrow _ ->
      let future = fresh_future_mode () in
      let domain = fresh_meta () in
      let codomain = fresh_meta () in
      set_meta_solution meta (TyArrow (TyMeta domain, future, TyMeta codomain))
  | ty_left, ty_right ->
      let left = string_of_ty_shallow ty_left in
      let right = string_of_ty_shallow ty_right in
      type_error (Printf.sprintf "type mismatch between %s and %s" left right)

and assert_subtype lower upper =
  outer_equiv lower upper;
  match (zonk lower, zonk upper) with
  | TyMeta lower_meta, TyMeta upper_meta ->
      let constraint_ = mk_constraint (Sub { lower = lower_meta; upper = upper_meta }) in
      add_constraint lower_meta constraint_;
      add_constraint upper_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyInt, TyInt -> ()
  | TyBool, TyBool -> ()
  | TyList (lower_elem, lower_storage), TyList (upper_elem, upper_storage) ->
      assert_subtype lower_elem upper_elem;
      assert_storage_leq_to lower_storage upper_storage
  | TyPair (lower_left, lower_storage, lower_right), TyPair (upper_left, upper_storage, upper_right) ->
      assert_subtype lower_left upper_left;
      assert_subtype lower_right upper_right;
      assert_storage_leq_to lower_storage upper_storage
  | TySum (lower_left, lower_storage, lower_right), TySum (upper_left, upper_storage, upper_right) ->
      assert_subtype lower_left upper_left;
      assert_subtype lower_right upper_right;
      assert_storage_leq_to lower_storage upper_storage
  | TyRef (lower_payload, lower_mode), TyRef (upper_payload, upper_mode) ->
      assert_subtype lower_payload upper_payload;
      assert_subtype upper_payload lower_payload;
      assert_ref_leq_to lower_mode upper_mode
  | TyArrow (lower_domain, lower_future, lower_codomain), TyArrow (upper_domain, upper_future, upper_codomain) ->
      assert_subtype upper_domain lower_domain;
      assert_subtype lower_codomain upper_codomain;
      assert_future_leq_to lower_future upper_future
  | _ ->
      type_error "assert_subtype: not a subtype"

and assert_alias source target =
  outer_equiv source target;
  match (zonk source, zonk target) with
  | TyMeta source_meta, TyMeta target_meta ->
      let constraint_ = mk_constraint (Alias { source = source_meta; target = target_meta }) in
      add_constraint source_meta constraint_;
      add_constraint target_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyInt, TyInt -> ()
  | TyBool, TyBool -> ()
  | TyList (source_elem, source_storage), TyList (target_elem, target_storage) ->
      assert_aliased target_storage.uniqueness;
      Modesolver.Areality.assert_leq_to source_storage.areality target_storage.areality;
      assert_alias source_elem target_elem
  | TyPair (source_left, source_storage, source_right), TyPair (target_left, target_storage, target_right) 
  | TySum (source_left, source_storage, source_right), TySum (target_left, target_storage, target_right) ->
      (* Make sure target_storage is aliased, areality is copied. *)
      assert_aliased target_storage.uniqueness;
      Modesolver.Areality.assert_leq_to source_storage.areality target_storage.areality;
      assert_alias source_left target_left;
      assert_alias source_right target_right;
  | TyRef (source_payload, source_mode), TyRef (target_payload, target_mode) ->
      assert_alias source_payload target_payload;
      assert_equal_in Modesolver.Contention.assert_leq_to source_mode.contention target_mode.contention;
  | TyArrow (_source_domain, source_future, _source_codomain), TyArrow (_target_domain, target_future, _target_codomain) ->
      (* Assert that linearity is many for aliased functions.*)
      Modesolver.Linearity.restrict_domain [Linearity.many] source_future.linearity;
      Modesolver.Areality.assert_leq_to source_future.areality target_future.areality;
      Modesolver.Portability.assert_leq_to source_future.portability target_future.portability;
  | _ ->
      type_error "assert_alias: not equivalent"

and assert_lock original locked future =
  log_lock "lock %s into %s"
    (string_of_ty_shallow original) (string_of_ty_shallow locked);
  outer_equiv original locked;
  match (zonk original, zonk locked) with
  | TyMeta original_meta, TyMeta locked_meta ->
      log_lock "record meta constraint original=?%d locked=?%d" original_meta.id locked_meta.id;
      let constraint_ = mk_constraint (Lock { original = original_meta; locked = locked_meta; future = future }) in
      add_constraint original_meta constraint_;
      add_constraint locked_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyBool, TyBool -> ()
  | TyInt, TyInt -> ()
  | TyPair (original_left, original_storage, original_right), TyPair (locked_left, locked_storage, locked_right) 
  | TySum (original_left, original_storage, original_right), TySum (locked_left, locked_storage, locked_right) ->
      log_lock "pair/sum storage lock";
      (* Unique component joins with dagger(future), areality unchanged. *)
      Modesolver.Uniqueness.assert_leq_to original_storage.uniqueness locked_storage.uniqueness;
      Modesolver.assert_linearity_dagger future.linearity locked_storage.uniqueness;
      Modesolver.Areality.assert_leq_to original_storage.areality locked_storage.areality;
      Modesolver.Areality.assert_leq_to original_storage.areality future.areality;
      assert_lock original_left locked_left future;
      assert_lock original_right locked_right future
  | TyList (original_elem, original_storage), TyList (locked_elem, locked_storage) ->
      log_lock "list storage lock";
      Modesolver.Uniqueness.assert_leq_to original_storage.uniqueness locked_storage.uniqueness;
      Modesolver.assert_linearity_dagger future.linearity locked_storage.uniqueness;
      Modesolver.Areality.assert_leq_to original_storage.areality locked_storage.areality;
      Modesolver.Areality.assert_leq_to original_storage.areality future.areality;
      assert_lock original_elem locked_elem future
  | TyRef (original_payload, original_mode), TyRef (locked_payload, locked_mode) ->
      log_lock "ref lock enforcement";
      Modesolver.Contention.assert_leq_to original_mode.contention locked_mode.contention;
      Modesolver.assert_portability_dagger future.portability locked_mode.contention;
      assert_lock original_payload locked_payload future
  | TyArrow (original_domain, original_future, original_codomain), TyArrow (locked_domain, locked_future, locked_codomain) ->
      log_lock "arrow lock enforcement";
      (* Locking leaves functions untouched provided ambient future ≤ function future. *)
      assert_future_leq_to original_future future;
      assert_future_leq_to original_future locked_future;
      assert_subtype locked_domain original_domain;
      assert_subtype original_codomain locked_codomain
  | _ ->
      type_error "assert_lock: not equivalent"

and fire_constraint constraint_record =
  if constraint_record.fired then ()
  else (
    constraint_record.fired <- true;
    match constraint_record.constraint_ with
    | Sub { lower; upper } ->
        assert_subtype (TyMeta lower) (TyMeta upper)
    | Alias { source; target } ->
        assert_alias (TyMeta source) (TyMeta target)
    | Lock { original; locked; future } ->
        assert_lock (TyMeta original) (TyMeta locked) future
    | In { target; mode_vars } ->
        assert_in (TyMeta target) mode_vars )

and set_meta_solution meta ty =
  match meta.solution with
  | Some _ ->
      type_error (Printf.sprintf "meta %d already solved" meta.id)
  | None ->
      meta.solution <- Some ty;
      List.iter fire_constraint meta.constraints

(* -------------------------------------------------------------------------- *)
(* Converting annotated syntax *)

let storage_mode_of_ast (storage : Ast.storage_mode) : storage_mode =
  { uniqueness = Mode_consts.uniqueness storage.uniqueness;
    areality = Mode_consts.areality storage.areality }

let ref_mode_of_ast (mode : Ast.ref_mode) : ref_mode =
  { contention = Mode_consts.contention mode.contention }

let future_mode_of_ast (future : Future.t) : future_mode =
  { linearity = Mode_consts.linearity future.linearity;
    portability = Mode_consts.portability future.portability;
    areality = Mode_consts.areality future.areality }

let rec ty_of_ast (ty_syntax : Ast.ty) : ty =
  match ty_syntax with
  | Ast.TyUnit -> TyUnit
  | Ast.TyEmpty -> TyEmpty
  | Ast.TyInt -> TyInt
  | Ast.TyBool -> TyBool
  | Ast.TyList (elem, storage) ->
      let elem' = ty_of_ast elem in
      let storage' = storage_mode_of_ast storage in
      mk_list elem' storage'
  | Ast.TyPair (left, storage, right) ->
      let left' = ty_of_ast left in
      let right' = ty_of_ast right in
      let storage' = storage_mode_of_ast storage in
      mk_pair left' storage' right'
  | Ast.TySum (left, storage, right) ->
      let left' = ty_of_ast left in
      let right' = ty_of_ast right in
      let storage' = storage_mode_of_ast storage in
      mk_sum left' storage' right'
  | Ast.TyRef (payload, mode) ->
      let payload' = ty_of_ast payload in
      let mode' = ref_mode_of_ast mode in
      mk_ref payload' mode'
  | Ast.TyArrow (domain, future, codomain) ->
      let domain' = ty_of_ast domain in
      let codomain' = ty_of_ast codomain in
      let future' = future_mode_of_ast future in
      TyArrow (domain', future', codomain')

(* -------------------------------------------------------------------------- *)
(* Pretty-printing inference types.                                           *)

module Printing = struct

module ModeInfoSet = Set.Make (String)

module ModeName = struct
  type t =
    { tbl : (Intsolver.var, string) Hashtbl.t;
      mutable counter : int;
      prefix : string }

  let create prefix =
    { tbl = Hashtbl.create 16; counter = 0; prefix }

  let name t var =
    let key = Modesolver.id var in
    match Hashtbl.find_opt t.tbl key with
    | Some n -> n
    | None ->
        t.counter <- t.counter + 1;
        let n = Printf.sprintf "%s%d" t.prefix t.counter in
        Hashtbl.add t.tbl key n;
        n
end

module MetaNames = struct
  type t =
    { tbl : (int, string) Hashtbl.t;
      mutable counter : int }

  let create () =
    { tbl = Hashtbl.create 16; counter = 0 }

  let rec label_of_index index =
    let letter = Char.chr (Char.code 'a' + (index mod 26)) in
    let next = (index / 26) - 1 in
    let suffix = String.make 1 letter in
    if next >= 0 then (label_of_index next) ^ suffix else suffix

  let fresh_name t =
    let name = "'" ^ label_of_index t.counter in
    t.counter <- t.counter + 1;
    name

  let name t meta_id =
    match Hashtbl.find_opt t.tbl meta_id with
    | Some n -> n
    | None ->
        let n = fresh_name t in
        Hashtbl.add t.tbl meta_id n;
        n
end

type mode_print_state =
  { u : ModeName.t;
    a : ModeName.t;
    l : ModeName.t;
    p : ModeName.t;
    c : ModeName.t;
    meta_names : MetaNames.t;
    mutable u_vars : Modesolver.Uniqueness.var list;
    mutable a_vars : Modesolver.Areality.var list;
    mutable l_vars : Modesolver.Linearity.var list;
    mutable p_vars : Modesolver.Portability.var list;
    mutable c_vars : Modesolver.Contention.var list;
    mutable info_set : ModeInfoSet.t;
    mutable infos : string list }

let make_mode_print_state () =
  { u = ModeName.create "u";
    a = ModeName.create "a";
    l = ModeName.create "l";
    p = ModeName.create "p";
    c = ModeName.create "c";
    meta_names = MetaNames.create ();
    u_vars = [];
    a_vars = [];
    l_vars = [];
    p_vars = [];
    c_vars = [];
    info_set = ModeInfoSet.empty;
    infos = [] }

let register_mode_info state line =
  if ModeInfoSet.mem line state.info_set then ()
  else (
    state.info_set <- ModeInfoSet.add line state.info_set;
    state.infos <- line :: state.infos)

let remember_uni_var state var =
  if List.exists (fun existing -> existing == var) state.u_vars then ()
  else state.u_vars <- state.u_vars @ [ var ]

let remember_are_var state var =
  if List.exists (fun existing -> existing == var) state.a_vars then ()
  else state.a_vars <- state.a_vars @ [ var ]

let remember_lin_var state var =
  if List.exists (fun existing -> existing == var) state.l_vars then ()
  else state.l_vars <- state.l_vars @ [ var ]

let remember_port_var state var =
  if List.exists (fun existing -> existing == var) state.p_vars then ()
  else state.p_vars <- state.p_vars @ [ var ]

let remember_cont_var state var =
  if List.exists (fun existing -> existing == var) state.c_vars then ()
  else state.c_vars <- state.c_vars @ [ var ]

module IntSet = Set.Make (Int)

let domain_to_string describe values =
  values
  |> List.map describe
  |> List.sort_uniq String.compare
  |> String.concat ", "

let render_mode_var state names remember describe var =
  remember var;
  match Modesolver.get_domain var with
  | [] ->
      let name = ModeName.name names var in
      register_mode_info state (Printf.sprintf "%s ∈ ∅" name);
      name
  | [value] -> describe value
  | values ->
      let name = ModeName.name names var in
      register_mode_info state
        (Printf.sprintf "%s ∈ {%s}" name (domain_to_string describe values));
      name

let render_uni state var =
  render_mode_var state state.u (remember_uni_var state) Modes.Uniqueness.to_string var

let render_are state var =
  render_mode_var state state.a (remember_are_var state) Modes.Areality.to_string var

let render_lin state var =
  render_mode_var state state.l (remember_lin_var state) Modes.Linearity.to_string var

let render_port state var =
  render_mode_var state state.p (remember_port_var state) Modes.Portability.to_string var

let render_cont state var =
  render_mode_var state state.c (remember_cont_var state) Modes.Contention.to_string var

let string_of_storage_mode state (storage : storage_mode) =
  Printf.sprintf "u=%s a=%s"
    (render_uni state storage.uniqueness)
    (render_are state storage.areality)

let string_of_ref_mode state (mode : ref_mode) =
  Printf.sprintf "c=%s" (render_cont state mode.contention)

let string_of_future_mode state (future : future_mode) =
  Printf.sprintf "a=%s l=%s p=%s"
    (render_are state future.areality)
    (render_lin state future.linearity)
    (render_port state future.portability)

let string_of_mode_vars state (mode_vars : mode_vars) =
  Printf.sprintf "{u=%s; c=%s; l=%s; p=%s; a=%s}"
    (render_uni state mode_vars.uniqueness)
    (render_cont state mode_vars.contention)
    (render_lin state mode_vars.linearity)
    (render_port state mode_vars.portability)
    (render_are state mode_vars.areality)

let rec string_of_ty_core state ty =
  match zonk ty with
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyArrow (domain, future, codomain) ->
      Printf.sprintf "(%s ->[%s] %s)"
        (string_of_ty_core state domain)
        (string_of_future_mode state future)
        (string_of_ty_core state codomain)
  | TyPair (left, storage, right) ->
      Printf.sprintf "(%s *[%s] %s)"
        (string_of_ty_core state left)
        (string_of_storage_mode state storage)
        (string_of_ty_core state right)
  | TySum (left, storage, right) ->
      Printf.sprintf "(%s +[%s] %s)"
        (string_of_ty_core state left)
        (string_of_storage_mode state storage)
        (string_of_ty_core state right)
  | TyList (elem, storage) ->
      Printf.sprintf "(list[%s] %s)"
        (string_of_storage_mode state storage)
        (string_of_ty_core state elem)
  | TyRef (payload, mode) ->
      Printf.sprintf "(ref[%s] %s)"
        (string_of_ref_mode state mode)
        (string_of_ty_core state payload)
  | TyMeta meta ->
      (match meta.solution with
      | Some solution -> string_of_ty_core state solution
      | None -> MetaNames.name state.meta_names meta.id)

let collect_metas ty =
  let rec aux set acc ty =
    match zonk ty with
    | TyMeta meta ->
        if IntSet.mem meta.id set then
          set, acc
        else
          let set = IntSet.add meta.id set in
          (match meta.solution with
          | Some solution -> aux set acc solution
          | None -> set, meta :: acc)
    | TyPair (left, _, right) | TySum (left, _, right) ->
        let set, acc = aux set acc left in
        aux set acc right
    | TyList (elem, _) -> aux set acc elem
    | TyRef (payload, _) -> aux set acc payload
    | TyArrow (domain, _, codomain) ->
        let set, acc = aux set acc domain in
        aux set acc codomain
    | TyUnit | TyEmpty | TyInt | TyBool -> set, acc
  in
  let _, metas = aux IntSet.empty [] ty in
  List.rev metas

let render_constraints state metas =
  let meta_ids =
    List.fold_left (fun acc meta -> IntSet.add meta.id acc) IntSet.empty metas
  in
  let seen = ref [] in
  let remember cr =
    if List.exists (fun existing -> existing == cr) !seen then false
    else (
      seen := cr :: !seen;
      true)
  in
  let meta_ref meta = MetaNames.name state.meta_names meta.id in
  let describe_future future = string_of_future_mode state future in
  let describe_constraint cr =
    match cr.constraint_ with
    | Sub { lower; upper } ->
        if IntSet.mem lower.id meta_ids || IntSet.mem upper.id meta_ids then
          Some (Printf.sprintf "%s <= %s" (meta_ref lower) (meta_ref upper))
        else
          None
    | Alias { source; target } ->
        if IntSet.mem source.id meta_ids || IntSet.mem target.id meta_ids then
          Some (Printf.sprintf "%s alias %s" (meta_ref source) (meta_ref target))
        else
          None
    | Lock { original; locked; future } ->
        if IntSet.mem original.id meta_ids || IntSet.mem locked.id meta_ids then
          Some
            (Printf.sprintf "lock %s -> %s with %s"
               (meta_ref original) (meta_ref locked) (describe_future future))
        else
          None
    | In { target; mode_vars } ->
        if IntSet.mem target.id meta_ids then
          Some
            (Printf.sprintf "%s in %s" (meta_ref target)
               (string_of_mode_vars state mode_vars))
        else
          None
  in
  let constraints =
    List.fold_left
      (fun acc meta ->
        List.fold_left
          (fun acc cr ->
            if remember cr then
              match describe_constraint cr with
              | Some text -> text :: acc
              | None -> acc
            else acc)
          acc meta.constraints)
      [] metas
  in
  List.rev constraints

let string_of_pairs describe pairs =
  let body =
    pairs
    |> List.map (fun (left, right) ->
           Printf.sprintf "(%s,%s)" (describe left) (describe right))
    |> String.concat ", "
  in
  Printf.sprintf "{%s}" body

let cartesian_relation left_domain right_domain =
  left_domain
  |> List.map (fun left ->
         List.map (fun right -> (left, right)) right_domain)
  |> List.concat
  |> Relations.make

let relation_is_cartesian left right relation =
  let left_domain = Modesolver.get_domain left in
  let right_domain = Modesolver.get_domain right in
  left_domain <> []
  && right_domain <> []
  && Relations.equal relation (cartesian_relation left_domain right_domain)

let relation_display describe left right relation =
  let left_domain = Modesolver.get_domain left in
  let right_domain = Modesolver.get_domain right in
  let present_pairs = Relations.to_list relation in
  let present_str = string_of_pairs describe present_pairs in
  let complement_pairs =
    cartesian_relation left_domain right_domain
    |> Relations.to_list
    |> List.filter (fun pair -> not (List.mem pair present_pairs))
  in
  let complement_str = string_of_pairs describe complement_pairs in
  if String.length present_str <= String.length complement_str then
    `Present present_str
  else
    `Complement complement_str

let axis_relation_lines names vars describe get_relation =
  let vars = List.rev vars in
  let all_pairs =
    vars
    |> List.mapi (fun i left ->
           vars
           |> List.mapi (fun j right ->
                  if i >= j then None else Some (left, right))
           |> List.filter_map (fun x -> x))
    |> List.concat
  in
  let lines =
    List.fold_left
      (fun acc (left, right) ->
        let relation = get_relation left right in
        if relation_is_cartesian left right relation then acc
        else
          let left_name = ModeName.name names left in
          let right_name = ModeName.name names right in
          let line =
            match relation_display describe left right relation with
            | `Present relation_str ->
                Printf.sprintf "(%s,%s) ∈ %s" left_name right_name relation_str
            | `Complement relation_str ->
                Printf.sprintf "(%s,%s) ∉ %s" left_name right_name relation_str
          in
          line :: acc)
      [] all_pairs
  in
  List.rev lines

let render_mode_relations state =
  List.concat
    [ axis_relation_lines state.u state.u_vars Modes.Uniqueness.to_string Modesolver.Uniqueness.get_relation;
      axis_relation_lines state.a state.a_vars Modes.Areality.to_string Modesolver.Areality.get_relation;
      axis_relation_lines state.l state.l_vars Modes.Linearity.to_string Modesolver.Linearity.get_relation;
      axis_relation_lines state.p state.p_vars Modes.Portability.to_string Modesolver.Portability.get_relation;
      axis_relation_lines state.c state.c_vars Modes.Contention.to_string Modesolver.Contention.get_relation ]

let string_of_section label lines =
  match lines with
  | [] -> None
  | _ ->
      let body =
        lines |> List.map (fun line -> "  " ^ line) |> String.concat "\n"
      in
      Some (Printf.sprintf "%s\n%s" label body)

let string_of_ty ty =
  let state = make_mode_print_state () in
  let metas = collect_metas ty in
  let base = string_of_ty_core state ty in
  let constraints = render_constraints state metas in
  let mode_infos = List.rev state.infos in
  let mode_relations = render_mode_relations state in
  let sections =
    [ string_of_section "where" constraints;
      string_of_section "mode vars" mode_infos;
      string_of_section "mode rels" mode_relations ]
    |> List.filter_map (fun x -> x)
    |> String.concat "\n"
  in
  if sections = "" then base else Printf.sprintf "%s\n%s" base sections

end

let string_of_ty = Printing.string_of_ty

(* -------------------------------------------------------------------------- *)
(* Environments                                                               *)

let rec lookup env name =
  match env with
  | [] -> None
  | (bound, ty) :: rest -> if String.equal bound name then Some ty else lookup rest name

let alias_binding ty =
  let alias_meta = fresh_meta () in
  let alias_ty = TyMeta alias_meta in
  assert_alias ty alias_ty;
  alias_ty

let alias_env_for env vars =
  if StringSet.is_empty vars then env
  else
    List.map
      (fun (name, ty) ->
        if StringSet.mem name vars then
          (name, alias_binding ty)
        else
          (name, ty))
      env

let restrict_env env vars =
  if StringSet.is_empty vars then []
  else List.filter (fun (name, _) -> StringSet.mem name vars) env

let split_env env fv1 fv2 =
  let shared = StringSet.inter fv1 fv2 in
  let aliased_env = alias_env_for env shared in
  (restrict_env aliased_env fv1, restrict_env aliased_env fv2)

let lock_type ty future =
  let locked_ty = TyMeta (fresh_meta ()) in
  assert_lock ty locked_ty future;
  locked_ty

let lock_env env future =
  (* Apply the lock constraint to every binding so the function body only sees
     weakened capabilities allowed by [future]. *)
  List.map (fun (name, ty) -> (name, lock_type ty future)) env

let infer_binop op ty_lhs ty_rhs =
  match op with
  | Ast.Add | Ast.Sub | Ast.Mul ->
      assert_subtype ty_lhs TyInt;
      assert_subtype ty_rhs TyInt;
      TyInt
  | Ast.Eq | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge ->
      assert_subtype ty_lhs TyInt;
      assert_subtype ty_rhs TyInt;
      TyBool
  | Ast.And | Ast.Or ->
      assert_subtype ty_lhs TyBool;
      assert_subtype ty_rhs TyBool;
      TyBool


let rec infer_with_env env expr = 
  match expr with
  | Ast.Var x ->
    (match lookup env x with
    | Some ty -> ty
    | None -> type_error (Printf.sprintf "Unbound variable %s" x))
  | Ast.Borrow (x, e1, y, e2, e3) ->
      let fv_e2 = free_vars_without e2 [ x ] in
      let fv_e3 = free_vars_without e3 [ x; y ] in
      let fv_rest = StringSet.union fv_e2 fv_e3 in
      let fv_e1 = free_vars e1 in
      let env_e1, env_rest = split_env env fv_e1 fv_rest in
      let ty_x = infer_with_env env_e1 e1 in
      let borrow_source_mode = many_mode_vars () in
      assert_in ty_x borrow_source_mode;
      let env_e2_base, env_e3_base = split_env env_rest fv_e2 fv_e3 in
      let ty_x_borrowed = TyMeta (fresh_meta ()) in
      assert_subtype ty_x ty_x_borrowed;
      assert_in ty_x_borrowed (borrowed_mode_vars ());
      let env_e2 = (x, ty_x_borrowed) :: env_e2_base in
      let ty_y = infer_with_env env_e2 e2 in
      let mode = nonborrowed_mode_vars () in
      assert_in ty_y mode;
      let env_e3 = (x, ty_x) :: (y, ty_y) :: env_e3_base in
      infer_with_env env_e3 e3
  | Ast.Unit -> TyUnit
  | Ast.Bool _ -> TyBool
  | Ast.If (cond, then_branch, else_branch) ->
      let fv_cond = free_vars cond in
      let fv_then = free_vars then_branch in
      let fv_else = free_vars else_branch in
      let branches_fv = StringSet.union fv_then fv_else in
      let env_cond, env_rest = split_env env fv_cond branches_fv in
      let cond_ty = infer_with_env env_cond cond in
      assert_subtype cond_ty TyBool;
      let env_then, env_else = split_env env_rest fv_then fv_else in
      let ty_then = infer_with_env env_then then_branch in
      let ty_else = infer_with_env env_else else_branch in
      let ty_join = TyMeta (fresh_meta ()) in
      assert_subtype ty_then ty_join;
      assert_subtype ty_else ty_join;
      ty_join
  | Ast.ListNil ->
      let elem_ty = TyMeta (fresh_meta ()) in
      let storage = fresh_storage_mode () in
      mk_list elem_ty storage
  | Ast.ListCons (alloc, head, tail) ->
      let head_fv = free_vars head in
      let tail_fv = free_vars tail in
      let env_head, env_tail = split_env env head_fv tail_fv in
      let head_ty = infer_with_env env_head head in
      let tail_ty = infer_with_env env_tail tail in
      let elem_ty = TyMeta (fresh_meta ()) in
      let storage = fresh_storage_mode () in
      let () =
        match alloc with
        | Ast.Stack -> force_storage_local storage
        | Ast.Heap -> ()
      in
      let list_ty = mk_list elem_ty storage in
      assert_subtype head_ty elem_ty;
      assert_subtype elem_ty head_ty;
      assert_subtype tail_ty list_ty;
      assert_subtype list_ty tail_ty;
      list_ty
  | Ast.MatchList (kind, scrut, nil_branch, x, xs, cons_branch) ->
      let fv_scrut = free_vars scrut in
      let fv_nil = free_vars nil_branch in
      let fv_cons = free_vars_without cons_branch [ x; xs ] in
      let branches_fv = StringSet.union fv_nil fv_cons in
      let env_scrut, env_rest = split_env env fv_scrut branches_fv in
      let ty_scrut = infer_with_env env_scrut scrut in
      let elem_ty = TyMeta (fresh_meta ()) in
      let storage = fresh_storage_mode () in
      let ty_list = mk_list elem_ty storage in
      assert_subtype ty_scrut ty_list;
      (match kind with
       | Ast.Destructive -> force_storage_unique storage
       | Ast.Regular -> ());
      let env_nil, env_cons = split_env env_rest fv_nil fv_cons in
      let ty_nil = infer_with_env env_nil nil_branch in
      let env_cons' = (x, elem_ty) :: (xs, ty_list) :: env_cons in
      let ty_cons = infer_with_env env_cons' cons_branch in
      let ty_join = TyMeta (fresh_meta ()) in
      assert_subtype ty_nil ty_join;
      assert_subtype ty_cons ty_join;
      ty_join
  | Ast.Int _ -> TyInt
  | Ast.BinOp (lhs, op, rhs) ->
      let fv_lhs = free_vars lhs in
      let fv_rhs = free_vars rhs in
      let env_lhs, env_rhs = split_env env fv_lhs fv_rhs in
      let ty_lhs = infer_with_env env_lhs lhs in
      let ty_rhs = infer_with_env env_rhs rhs in
      infer_binop op ty_lhs ty_rhs
  | Ast.IntNeg e ->
      let ty = infer_with_env env e in
      assert_subtype ty TyInt;
      TyInt
  | Ast.BoolNot e ->
      let ty = infer_with_env env e in
      assert_subtype ty TyBool;
      TyBool
  | Ast.FunRec (alloc, f, x, body) ->
      let ty_param = TyMeta (fresh_meta ()) in
      let future = fresh_future_mode () in
      let () = match alloc with Ast.Stack -> force_future_local future | Ast.Heap -> () in
      Modesolver.Linearity.restrict_domain [Linearity.many] future.linearity;
      let ty_cod = TyMeta (fresh_meta ()) in
      let fun_ty = TyArrow (ty_param, future, ty_cod) in
      let captured_vars = free_vars_without body [ f; x ] in
      let captured_env = restrict_env env captured_vars in
      let locked_env = lock_env captured_env future in
      let env' = (f, fun_ty) :: (x, ty_param) :: locked_env in
      let body_ty = infer_with_env env' body in
      assert_subtype body_ty ty_cod;
      assert_subtype ty_cod body_ty;
      fun_ty
  | Ast.Pair (alloc, e1, e2) ->
    let left_fv = free_vars e1 in
    let right_fv = free_vars e2 in
    let env_left, env_right = split_env env left_fv right_fv in
    let ty1 = infer_with_env env_left e1 in
    let ty2 = infer_with_env env_right e2 in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = mk_pair ty1 storage ty2 in
    ty
  | Ast.Inl (alloc, e) ->
    let ty_left = infer_with_env env e in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = mk_sum ty_left storage ty_right in
    ty
  | Ast.Inr (alloc, e) ->
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = infer_with_env env e in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = mk_sum ty_left storage ty_right in
    ty
  | Ast.Hole -> TyMeta (fresh_meta ())
  | Ast.Absurd e ->
    let ty = infer_with_env env e in
    assert_subtype ty TyEmpty;
    TyMeta (fresh_meta ())
  | Ast.Let (_, x, e1, e2) ->
    let fv_e1 = free_vars e1 in
    let fv_e2 = free_vars_without e2 [ x ] in
    let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
    let ty1 = infer_with_env env_e1 e1 in
    infer_with_env ((x, ty1) :: env_e2) e2
  | Ast.LetPair (kind, x1, x2, e1, e2) ->
    let fv_e1 = free_vars e1 in
    let fv_e2 = free_vars_without e2 [ x1; x2 ] in
    let env_e1, env_e2 = split_env env fv_e1 fv_e2 in
    let ty1 = infer_with_env env_e1 e1 in
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let ty_pair = mk_pair ty_left storage ty_right in
    assert_subtype ty1 ty_pair;
    (match kind with
     | Ast.Destructive -> force_storage_unique storage
     | Ast.Regular -> ());
    let env' = (x1, ty_left) :: (x2, ty_right) :: env_e2 in
    infer_with_env env' e2
  | Ast.Match (kind, e, x1, e1, x2, e2) ->
    let fv_scrut = free_vars e in
    let fv_e1 = free_vars_without e1 [ x1 ] in
    let fv_e2 = free_vars_without e2 [ x2 ] in
    let branches_fv = StringSet.union fv_e1 fv_e2 in
    let env_scrut, env_rest = split_env env fv_scrut branches_fv in
    let ty_scrut = infer_with_env env_scrut e in
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let ty_sum = mk_sum ty_left storage ty_right in
    assert_subtype ty_scrut ty_sum;
    (match kind with
     | Ast.Destructive -> force_storage_unique storage
     | Ast.Regular -> ());
    let env1, env2 = split_env env_rest fv_e1 fv_e2 in
    let ty1 = infer_with_env ((x1, ty_left) :: env1) e1 in
    let ty2 = infer_with_env ((x2, ty_right) :: env2) e2 in
    let ty_join = TyMeta (fresh_meta ()) in
    assert_subtype ty1 ty_join;
    assert_subtype ty2 ty_join;
    ty_join
  | Ast.App (e1, e2) ->
    let fn_fv = free_vars e1 in
    let arg_fv = free_vars e2 in
    let env_fn, env_arg = split_env env fn_fv arg_fv in
    let ty1 = infer_with_env env_fn e1 in
    let ty2 = infer_with_env env_arg e2 in
    let ty_dom = TyMeta (fresh_meta ()) in
    let ty_cod = TyMeta (fresh_meta ()) in
    let future = fresh_future_mode () in
    let ty_f = TyArrow (ty_dom, future, ty_cod) in
    assert_subtype ty1 ty_f;
    assert_subtype ty2 ty_dom;
    ty_cod
  | Ast.Fun (alloc, x, e) ->
    let ty_param = TyMeta (fresh_meta ()) in
    let future = fresh_future_mode () in
    let () = match alloc with Ast.Stack -> force_future_local future | Ast.Heap -> () in
    let captured_vars = free_vars_without e [ x ] in
    let captured_env = restrict_env env captured_vars in
    let locked_env = lock_env captured_env future in
    let env' = (x, ty_param) :: locked_env in
    let ty_body = infer_with_env env' e in
    let ty_arrow = TyArrow (ty_param, future, ty_body) in
    ty_arrow
  | Ast.Annot (e, ty_syntax) ->
    let ty' = infer_with_env env e in
    let ty = ty_of_ast ty_syntax in
    assert_subtype ty' ty;
    ty
  | Ast.Region e ->
    let ty = infer_with_env env e in
    let mode_vars = global_mode_vars () in
    assert_in ty mode_vars;
    ty
  | Ast.Ref e ->
    let payload = infer_with_env env e in
    mk_ref payload (precise_ref_mode ())
  | Ast.Deref e ->
    let ref_ty = infer_with_env env e in
    let payload = TyMeta (fresh_meta ()) in
    let ref_mode =
      { contention = Mode_consts.contention Contention.shared }
    in
    let expected = mk_ref payload ref_mode in
    assert_subtype ref_ty expected;
    payload
  | Ast.Assign (lhs, rhs) ->
    let lhs_ty = infer_with_env env lhs in
    let rhs_ty = infer_with_env env rhs in
    let payload = TyMeta (fresh_meta ()) in
    let ref_mode =
      { contention = Mode_consts.contention Contention.uncontended }
    in
    let expected = mk_ref payload ref_mode in
    assert_subtype lhs_ty expected;
    assert_subtype rhs_ty payload;
    TyUnit
  | Ast.Fork e ->
    let fv = free_vars e in
    let captured_env = restrict_env env fv in
    let future =
      { linearity = Mode_consts.linearity Linearity.once;
        portability = Mode_consts.portability Portability.portable;
        areality = Mode_consts.areality Areality.global }
    in
    let locked_env = lock_env captured_env future in
    let body_ty = infer_with_env locked_env e in
    assert_subtype body_ty TyUnit;
    TyUnit

let infer expr =
  try infer_with_env [] expr with
  | Modesolver.Inconsistent msg ->
      let formatted =
        if msg = "" then "mode solver detected inconsistency"
        else Printf.sprintf "mode solver detected %s" msg
      in
      type_error formatted
