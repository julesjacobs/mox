open Modes

type storage_mode = 
  { uniqueness : Modesolver.Uniqueness.var;
    areality : Modesolver.Areality.var }

type future_mode =
  { linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

type mode_vars =
  { uniqueness : Modesolver.Uniqueness.var;
    contention : Modesolver.Contention.var;
    linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

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
    (* Invariant:
       - bounds only reference unsolved metas (TyMeta with [solution = None])
       - the bound graph is kept transitively closed (edges imply their consequences) *)
    mutable lower_bounds : meta list;
    mutable upper_bounds : meta list;
    modes : mode_vars }

let fresh_meta_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

(* fresh_meta creates a new meta-type variable with optional solution and bound lists. *)
let fresh_meta ?solution ?(lower_bounds = []) ?(upper_bounds = []) ~modes () =
  { id = fresh_meta_id ();
    solution;
    lower_bounds;
    upper_bounds;
    modes }

(* solve_with_unit forces the meta-variable to resolve to [unit] and closes its bounds. *)
let rec solve_with_unit meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyUnit;
      List.iter solve_with_unit meta.lower_bounds;
      List.iter solve_with_unit meta.upper_bounds;
      meta.lower_bounds <- [];
      meta.upper_bounds <- []

(* solve_with_empty mirrors solve_with_unit but pins the meta-variable to [empty]. *)
let rec solve_with_empty meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyEmpty;
      List.iter solve_with_empty meta.lower_bounds;
      List.iter solve_with_empty meta.upper_bounds;
      meta.lower_bounds <- [];
      meta.upper_bounds <- []

(* ensure_unsolved guards uses of metas that should still be flexible. *)
let ensure_unsolved label meta =
  match meta.solution with
  | None -> ()
  | Some _ ->
      invalid_arg
        (Printf.sprintf "assert_subtype: %s meta is already solved" label)

(* has_bound checks whether [target] already appears in the given meta list. *)
let has_bound target bounds =
  List.exists
    (fun meta -> meta == target)
    bounds

(* insert_bound adds [target] if it is new and reports whether the list changed. *)
let insert_bound target bounds =
  if has_bound target bounds then (bounds, false)
  else (target :: bounds, true)

(* Asserts the leq_in relation between every axis in the lower and upper modes.
  Uses the mode solver functions directly. *)
let assert_modes_leq lower upper =
  Modesolver.Uniqueness.assert_leq_in lower.uniqueness upper.uniqueness;
  Modesolver.Contention.assert_leq_in lower.contention upper.contention;
  Modesolver.Linearity.assert_leq_in lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_in lower.portability upper.portability;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

(* assert_subtype links two metas via <= and pushes the relationship through neighbors. *)
let rec assert_subtype lower upper =
  if lower == upper then ()
  else (
    ensure_unsolved "lower" lower;
    ensure_unsolved "upper" upper;
    let updated, changed_lower = insert_bound upper lower.upper_bounds in
    lower.upper_bounds <- updated;
    let updated, changed_upper = insert_bound lower upper.lower_bounds in
    upper.lower_bounds <- updated;
    assert_modes_leq lower.modes upper.modes;
    if changed_lower || changed_upper then (
      List.iter (fun bound -> assert_subtype bound upper) lower.lower_bounds;
      List.iter (fun bound -> assert_subtype lower bound) upper.upper_bounds))

(* Takes the parent modes and does the following:
  - Creates fresh storage modes and asserts the leq_in relation between the parent and them.
  - Returns the component modes (the parent modes with new storage modes), and the storage modes separately. *)
let component_modes_pair modes =
  let storage_mode =
    { uniqueness = Modesolver.Uniqueness.new_var ();
      areality = Modesolver.Areality.new_var () }
  in
  Modesolver.Uniqueness.assert_leq_in storage_mode.uniqueness modes.uniqueness;
  Modesolver.Areality.assert_leq_in storage_mode.areality modes.areality;
  let component_modes =
    { modes with
      uniqueness = storage_mode.uniqueness;
      areality = storage_mode.areality }
  in
  (component_modes, storage_mode)

(* assert_storage_leq ensures both fields of storage_mode respect <=. *)
let assert_storage_leq (lower : storage_mode) (upper : storage_mode) =
  Modesolver.Uniqueness.assert_leq_in lower.uniqueness upper.uniqueness;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

(* assert_future_leq compares function-mode components along their axes. *)
let assert_future_leq (lower : future_mode) (upper : future_mode) =
  Modesolver.Linearity.assert_leq_in lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_in lower.portability upper.portability;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

(* solve_with_pair decomposes or instantiates a meta as a pair and syncs bounds. *)
let rec solve_with_pair meta =
  match meta.solution with
  | Some (TyPair (TyMeta left_meta, storage, TyMeta right_meta)) ->
      (left_meta, storage, right_meta)
  | Some (TyPair _) ->
      invalid_arg "solve_with_pair: expected meta components"
  | Some _ ->
      invalid_arg "solve_with_pair: meta already solved to non-pair type"
  | None ->
      let component_modes, storage_mode = component_modes_pair meta.modes in
      let left_meta = fresh_meta ~modes:component_modes () in
      let right_meta = fresh_meta ~modes:component_modes () in
      meta.solution <- Some (TyPair (TyMeta left_meta, storage_mode, TyMeta right_meta));
      let lower_bounds = meta.lower_bounds in
      let upper_bounds = meta.upper_bounds in
      meta.lower_bounds <- [];
      meta.upper_bounds <- [];
      let handle_lower bound =
        let (lower_left, lower_storage_mode, lower_right) = solve_with_pair bound in
        assert_subtype lower_left left_meta;
        assert_subtype lower_right right_meta;
        assert_storage_leq lower_storage_mode storage_mode
      and handle_upper bound =
        let (upper_left, upper_storage_mode, upper_right) = solve_with_pair bound in
        assert_subtype left_meta upper_left;
        assert_subtype right_meta upper_right;
        assert_storage_leq upper_storage_mode storage_mode
      in
      List.iter handle_lower lower_bounds;
      List.iter handle_upper upper_bounds;
      (left_meta, storage_mode, right_meta)

(* component_modes_sum is identical to component_modes_pair, exposed for clarity. *)
let component_modes_sum = component_modes_pair

(* solve_with_sum mirrors solve_with_pair but for sum types. *)
let rec solve_with_sum meta =
  match meta.solution with
  | Some (TySum (TyMeta left_meta, storage, TyMeta right_meta)) ->
      (left_meta, storage, right_meta)
  | Some (TySum _) ->
      invalid_arg "solve_with_sum: expected meta components"
  | Some _ ->
      invalid_arg "solve_with_sum: meta already solved to non-sum type"
  | None ->
      let component_modes, storage_mode = component_modes_sum meta.modes in
      let left_meta = fresh_meta ~modes:component_modes () in
      let right_meta = fresh_meta ~modes:component_modes () in
      meta.solution <- Some (TySum (TyMeta left_meta, storage_mode, TyMeta right_meta));
      let lower_bounds = meta.lower_bounds in
      let upper_bounds = meta.upper_bounds in
      meta.lower_bounds <- [];
      meta.upper_bounds <- [];
      let handle_lower bound =
        let (lower_left, lower_storage_mode, lower_right) = solve_with_sum bound in
        assert_subtype lower_left left_meta;
        assert_subtype lower_right right_meta;
        assert_storage_leq lower_storage_mode storage_mode
      and handle_upper bound =
        let (upper_left, upper_storage_mode, upper_right) = solve_with_sum bound in
        assert_subtype left_meta upper_left;
        assert_subtype right_meta upper_right;
        assert_storage_leq upper_storage_mode storage_mode
      in
      List.iter handle_lower lower_bounds;
      List.iter handle_upper upper_bounds;
      (left_meta, storage_mode, right_meta)

(* Takes the parent modes and does the following:
  - Creates fresh future (function) mode and asserts the leq_in relation between the parent and it.
  - Returns fresh component modes (minimum elements in the \in relation), and the future modes *)
let component_modes_arrow modes =
  let open Modes in
  let min_uniqueness = Modesolver.Uniqueness.bottom_in in
  let min_contention = Modesolver.Contention.bottom_in in
  let min_linearity = Modesolver.Linearity.bottom_in in
  let min_portability = Modesolver.Portability.bottom_in in
  let min_areality = Modesolver.Areality.bottom_in in
  let component_modes = {
    uniqueness = min_uniqueness;
    contention = min_contention;
    linearity = min_linearity;
    portability = min_portability;
    areality = min_areality
  } in
  let arrow_mode = {
    linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var ();
  } in
  Modesolver.Linearity.assert_leq_in modes.linearity arrow_mode.linearity;
  Modesolver.Portability.assert_leq_in modes.portability arrow_mode.portability;
  Modesolver.Areality.assert_leq_in modes.areality arrow_mode.areality;
  (component_modes, arrow_mode)

(* solve_with_arrow materializes arrow structure for a meta and propagates constraints. *)
let rec solve_with_arrow meta =
  match meta.solution with
  | Some (TyArrow (TyMeta domain_meta, arrow_mode, TyMeta codomain_meta)) ->
      (domain_meta, arrow_mode, codomain_meta)
  | Some (TyArrow _) ->
      invalid_arg "solve_with_arrow: expected meta components"
  | Some _ ->
      invalid_arg "solve_with_arrow: meta already solved to non-arrow type"
  | None ->
      let component_modes, arrow_mode = component_modes_arrow meta.modes in
      let domain_meta = fresh_meta ~modes:component_modes () in
      let codomain_meta = fresh_meta ~modes:component_modes () in
      meta.solution <- Some (TyArrow (TyMeta domain_meta, arrow_mode, TyMeta codomain_meta));
      let lower_bounds = meta.lower_bounds in
      let upper_bounds = meta.upper_bounds in
      meta.lower_bounds <- [];
      meta.upper_bounds <- [];
      let handle_lower bound =
        let (lower_domain, lower_future, lower_codomain) = solve_with_arrow bound in
        assert_subtype domain_meta lower_domain;
        assert_subtype lower_codomain codomain_meta;
        assert_future_leq lower_future arrow_mode
      and handle_upper bound =
        let (upper_domain, upper_future, upper_codomain) = solve_with_arrow bound in
        assert_subtype upper_domain domain_meta;
        assert_subtype codomain_meta upper_codomain;
        assert_future_leq arrow_mode upper_future
      in
      List.iter handle_lower lower_bounds;
      List.iter handle_upper upper_bounds;
      (domain_meta, arrow_mode, codomain_meta)

(* -------------------------------------------------------------------------- *)
(* Typing context and errors                                                  *)
(* -------------------------------------------------------------------------- *)

type error =
  | Unbound_variable of Ast.ident
  | Expected_function of ty
  | Expected_pair of ty
  | Expected_sum of ty
  | Cannot_infer of string
  | Not_a_subtype of ty * ty

exception Error of error

type context = (Ast.ident * ty) list

(* empty_context is the baseline environment with no bindings. *)
let empty_context : context = []

(* extend pushes a new binding on the context stack. *)
let extend ctx name ty = (name, ty) :: ctx

(* lookup fetches a variable binding or raises a descriptive error. *)
let lookup ctx name =
  match List.assoc_opt name ctx with
  | Some ty -> ty
  | None -> raise (Error (Unbound_variable name))

(* -------------------------------------------------------------------------- *)
(* Helpers for creating fresh mode/meta state                                 *)
(* -------------------------------------------------------------------------- *)

(* fresh_storage_mode produces storage axes used for pairs/sums. *)
let fresh_storage_mode () =
  { uniqueness = Modesolver.Uniqueness.new_var ();
    areality = Modesolver.Areality.new_var () }

(* fresh_future_mode allocates new function-mode axes for arrows. *)
let fresh_future_mode () =
  { linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var () }

(* fresh_mode_vars creates the full set of mode variables for a new meta-type. *)
let fresh_mode_vars () =
  { uniqueness = Modesolver.Uniqueness.new_var ();
    contention = Modesolver.Contention.new_var ();
    linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var () }

(* fresh_ty_var packages a newly created meta-type as a TyMeta node. *)
let fresh_ty_var () = TyMeta (fresh_meta ~modes:(fresh_mode_vars ()) ())

(* -------------------------------------------------------------------------- *)
(* Conversion helpers                                                         *)
(* -------------------------------------------------------------------------- *)

(* fixed_uniqueness builds a uniqueness var constrained to a single value. *)
let fixed_uniqueness value =
  Modesolver.Uniqueness.new_var ~domain:[ value ] ()

(* fixed_areality builds an areality var constrained to a single value. *)
let fixed_areality value =
  Modesolver.Areality.new_var ~domain:[ value ] ()

(* fixed_linearity builds a linearity var constrained to a single value. *)
let fixed_linearity value = Modesolver.Linearity.new_var ~domain:[ value ] ()

(* fixed_portability builds a portability var constrained to a single value. *)
let fixed_portability value = Modesolver.Portability.new_var ~domain:[ value ] ()

(* storage_mode_of_ast converts an AST storage annotation into solver vars. *)
let storage_mode_of_ast (storage : Ast.storage_mode) : storage_mode =
  { uniqueness = fixed_uniqueness storage.uniqueness;
    areality = fixed_areality storage.areality }

(* future_mode_of_ast converts an AST future mode annotation into solver vars. *)
let future_mode_of_ast (mode : Modes.Future.t) : future_mode =
  { linearity = fixed_linearity mode.linearity;
    portability = fixed_portability mode.portability;
    areality = fixed_areality mode.areality }

(* fixed_contention builds a contention var constrained to a single value. *)
let fixed_contention value =
  Modesolver.Contention.new_var ~domain:[ value ] ()

type mode_bound = mode_vars

(* mode_bound_of_mode materializes solver variables from a concrete mode. *)
let mode_bound_of_mode (mode : Modes.Mode.t) : mode_bound =
  let open Modes in
  let { Mode.past; future } = mode in
  { uniqueness = fixed_uniqueness past.Past.uniqueness;
    contention = fixed_contention past.Past.contention;
    linearity = fixed_linearity future.Future.linearity;
    portability = fixed_portability future.Future.portability;
    areality = fixed_areality future.Future.areality }

(* top_mode_bound is the universal bound mode. *)
let top_mode_bound = mode_bound_of_mode Modes.Mode.top_in

(* assert_meta_within checks all mode axes of a meta-type against the bound. *)
let assert_meta_within meta bound = assert_modes_leq meta.modes bound

(* assert_future_within_bound ensures a function-mode stays within a bound. *)
let assert_future_within_bound (future : future_mode) (bound : mode_bound) =
  Modesolver.Linearity.assert_leq_in future.linearity bound.linearity;
  Modesolver.Portability.assert_leq_in future.portability bound.portability;
  Modesolver.Areality.assert_leq_in future.areality bound.areality

(* assert_storage_within_bound ensures a storage-mode stays within a bound. *)
let assert_storage_within_bound (storage : storage_mode) (bound : mode_bound) =
  Modesolver.Uniqueness.assert_leq_in storage.uniqueness bound.uniqueness;
  Modesolver.Areality.assert_leq_in storage.areality bound.areality

(* component_bound specializes a bound for a component sharing storage axes. *)
let component_bound (bound : mode_bound) (storage : storage_mode) : mode_bound =
  { bound with
    uniqueness = storage.uniqueness;
    areality = storage.areality }

(* check_mode_within_bound walks a type structure, asserting every mode axis fits. *)
let rec check_mode_within_bound ty bound =
  match ty with
  | TyUnit | TyEmpty -> ()
  | TyMeta meta ->
      assert_meta_within meta bound;
      (match meta.solution with
      | None -> ()
      | Some ty -> check_mode_within_bound ty bound)
  | TyArrow (domain, future, codomain) ->
      assert_future_within_bound future bound;
      check_mode_within_bound domain top_mode_bound;
      check_mode_within_bound codomain top_mode_bound
  | TyPair (left, storage, right) | TySum (left, storage, right) ->
      assert_storage_within_bound storage bound;
      let child = component_bound bound storage in
      check_mode_within_bound left child;
      check_mode_within_bound right child

(* ensure_mode_within runs check_mode_within_bound for a concrete mode. *)
let ensure_mode_within ty mode =
  let bound = mode_bound_of_mode mode in
  check_mode_within_bound ty bound

(* ensure_well_formed asserts that a type fits inside the top mode bound. *)
let ensure_well_formed ty = check_mode_within_bound ty top_mode_bound

(* -------------------------------------------------------------------------- *)
(* AST type conversion                                                         *)
(* -------------------------------------------------------------------------- *)

(* ty_of_ast converts an AST-level type annotation into the internal Ty form. *)
let rec ty_of_ast (ty : Ast.ty) : ty =
  let rec convert = function
    | Ast.TyUnit -> TyUnit
    | Ast.TyEmpty -> TyEmpty
    | Ast.TyArrow (domain, mode, codomain) ->
        TyArrow (convert domain, future_mode_of_ast mode, convert codomain)
    | Ast.TyPair (left, storage, right) ->
        TyPair (convert left, storage_mode_of_ast storage, convert right)
    | Ast.TySum (left, storage, right) ->
        TySum (convert left, storage_mode_of_ast storage, convert right)
  in
  let converted = convert ty in
  ensure_well_formed converted;
  converted

(* -------------------------------------------------------------------------- *)
(* AST reification                                                            *)
(* -------------------------------------------------------------------------- *)

let diag_values ~equal relation =
  Relations.to_list relation
  |> List.fold_left
       (fun acc (a, b) ->
         if equal a b && not (List.exists (fun existing -> equal existing a) acc) then
           a :: acc
         else acc)
       []
  |> List.rev

let singleton_axis ~label ~equal get_relation var =
  let relation = get_relation var var in
  match diag_values ~equal relation with
  | [value] -> value
  | [] -> raise (Error (Cannot_infer label))
  | _ -> raise (Error (Cannot_infer label))

let storage_mode_to_ast (storage : storage_mode) =
  { Ast.uniqueness =
      singleton_axis ~label:"expression" ~equal:Modes.Uniqueness.equal
        Modesolver.Uniqueness.get_relation storage.uniqueness;
    areality =
      singleton_axis ~label:"expression" ~equal:Modes.Areality.equal
        Modesolver.Areality.get_relation storage.areality }

let future_mode_to_ast (mode : future_mode) =
  let linearity =
    singleton_axis ~label:"expression" ~equal:Modes.Linearity.equal
      Modesolver.Linearity.get_relation mode.linearity
  in
  let portability =
    singleton_axis ~label:"expression" ~equal:Modes.Portability.equal
      Modesolver.Portability.get_relation mode.portability
  in
  let areality =
    singleton_axis ~label:"expression" ~equal:Modes.Areality.equal
      Modesolver.Areality.get_relation mode.areality
  in
  Modes.Future.make ~linearity ~portability ~areality

let rec resolve_meta label meta =
  match meta.solution with
  | Some ty -> ty
  | None -> raise (Error (Cannot_infer label))

let rec ty_to_ast ?(label = "expression") ty =
  match ty with
  | TyUnit -> Ast.TyUnit
  | TyEmpty -> Ast.TyEmpty
  | TyArrow (domain, mode, codomain) ->
      let domain' = ty_to_ast ~label domain in
      let codomain' = ty_to_ast ~label codomain in
      let mode' = future_mode_to_ast mode in
      Ast.TyArrow (domain', mode', codomain')
  | TyPair (left, storage, right) ->
      let left' = ty_to_ast ~label left in
      let right' = ty_to_ast ~label right in
      Ast.TyPair (left', storage_mode_to_ast storage, right')
  | TySum (left, storage, right) ->
      let left' = ty_to_ast ~label left in
      let right' = ty_to_ast ~label right in
      Ast.TySum (left', storage_mode_to_ast storage, right')
  | TyMeta meta -> ty_to_ast ~label (resolve_meta label meta)

let ty_to_ast_opt ty =
  try Some (ty_to_ast ty) with
  | Error _ -> None

(* -------------------------------------------------------------------------- *)
(* Subtyping on concrete types                                                *)
(* -------------------------------------------------------------------------- *)

(* subtype_ty enforces that [lower] is a subtype of [upper], instantiating metas. *)
let rec subtype_ty lower upper =
  match (lower, upper) with
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyArrow (arg1, mode1, res1), TyArrow (arg2, mode2, res2) ->
      subtype_ty arg2 arg1;
      subtype_ty res1 res2;
      assert_future_leq mode1 mode2
  | TyPair (l1, storage1, r1), TyPair (l2, storage2, r2)
  | TySum (l1, storage1, r1), TySum (l2, storage2, r2) ->
      subtype_ty l1 l2;
      subtype_ty r1 r2;
      assert_storage_leq storage1 storage2
  | TyMeta meta_lower, TyMeta meta_upper ->
      assert_subtype meta_lower meta_upper
  | TyMeta meta, TyUnit ->
      solve_with_unit meta
  | TyUnit, TyMeta meta ->
      solve_with_unit meta
  | TyMeta meta, TyEmpty ->
      solve_with_empty meta
  | TyEmpty, TyMeta meta ->
      solve_with_empty meta
  | TyMeta meta, TyArrow (arg, mode, res) ->
      let domain_meta, arrow_mode, codomain_meta = solve_with_arrow meta in
      subtype_ty arg (TyMeta domain_meta);
      subtype_ty (TyMeta codomain_meta) res;
      assert_future_leq arrow_mode mode
  | TyArrow (arg, mode, res), TyMeta meta ->
      let domain_meta, arrow_mode, codomain_meta = solve_with_arrow meta in
      subtype_ty (TyMeta domain_meta) arg;
      subtype_ty res (TyMeta codomain_meta);
      assert_future_leq mode arrow_mode
  | TyMeta meta, TyPair (left, storage, right) ->
      let lower_left, lower_storage, lower_right = solve_with_pair meta in
      subtype_ty (TyMeta lower_left) left;
      subtype_ty (TyMeta lower_right) right;
      assert_storage_leq lower_storage storage
  | TyPair (left, storage, right), TyMeta meta ->
      let upper_left, upper_storage, upper_right = solve_with_pair meta in
      subtype_ty left (TyMeta upper_left);
      subtype_ty right (TyMeta upper_right);
      assert_storage_leq storage upper_storage
  | TyMeta meta, TySum (left, storage, right) ->
      let lower_left, lower_storage, lower_right = solve_with_sum meta in
      subtype_ty (TyMeta lower_left) left;
      subtype_ty (TyMeta lower_right) right;
      assert_storage_leq lower_storage storage
  | TySum (left, storage, right), TyMeta meta ->
      let upper_left, upper_storage, upper_right = solve_with_sum meta in
      subtype_ty left (TyMeta upper_left);
      subtype_ty right (TyMeta upper_right);
      assert_storage_leq storage upper_storage
  | _ -> raise (Error (Not_a_subtype (lower, upper)))

(* unify_ty is symmetric subtyping that collapses both directions. *)
let unify_ty t1 t2 =
  subtype_ty t1 t2;
  subtype_ty t2 t1;
  t1

(* -------------------------------------------------------------------------- *)
(* Shape destruction helpers                                                  *)
(* -------------------------------------------------------------------------- *)

(* expect_arrow destructs an arrow type, instantiating metas when necessary. *)
let rec expect_arrow ty =
  match ty with
  | TyArrow (domain, mode, codomain) -> (domain, mode, codomain)
  | TyMeta meta ->
      let domain_meta, mode, codomain_meta = solve_with_arrow meta in
      (TyMeta domain_meta, mode, TyMeta codomain_meta)
  | _ -> raise (Error (Expected_function ty))

(* expect_pair destructs a pair type, instantiating metas when necessary. *)
let rec expect_pair ty =
  match ty with
  | TyPair (left, storage, right) -> (left, storage, right)
  | TyMeta meta ->
      let left_meta, storage, right_meta = solve_with_pair meta in
      (TyMeta left_meta, storage, TyMeta right_meta)
  | _ -> raise (Error (Expected_pair ty))

(* expect_sum destructs a sum type, instantiating metas when necessary. *)
let rec expect_sum ty =
  match ty with
  | TySum (left, storage, right) -> (left, storage, right)
  | TyMeta meta ->
      let left_meta, storage, right_meta = solve_with_sum meta in
      (TyMeta left_meta, storage, TyMeta right_meta)
  | _ -> raise (Error (Expected_sum ty))

(* -------------------------------------------------------------------------- *)
(* Inference                                                                  *)
(* -------------------------------------------------------------------------- *)

(* infer implements bidirectional inference for expressions under a typing context. *)
let rec infer_expr (ctx : context) (expr : Ast.expr) : ty =
  match expr with
  | Ast.Var name -> lookup ctx name
  | Ast.Unit -> TyUnit
  | Ast.Hole -> fresh_ty_var ()
  | Ast.Absurd contradiction ->
      let contradiction_ty = infer_expr ctx contradiction in
      subtype_ty contradiction_ty TyEmpty;
      fresh_ty_var ()
  | Ast.Fun (param, body) ->
      let param_ty = fresh_ty_var () in
      let result_ty = infer_expr (extend ctx param param_ty) body in
      TyArrow (param_ty, fresh_future_mode (), result_ty)
  | Ast.App (fn, arg) ->
      let fn_ty = infer_expr ctx fn in
      let domain_ty, _, codomain_ty = expect_arrow fn_ty in
      let arg_ty = infer_expr ctx arg in
      subtype_ty arg_ty domain_ty;
      codomain_ty
  | Ast.Pair (left, right) ->
      let left_ty = infer_expr ctx left in
      let right_ty = infer_expr ctx right in
      TyPair (left_ty, fresh_storage_mode (), right_ty)
  | Ast.Let (name, bound, body) ->
      let bound_ty = infer_expr ctx bound in
      infer_expr (extend ctx name bound_ty) body
  | Ast.LetPair (x1, x2, pair_expr, body) ->
      let pair_ty = infer_expr ctx pair_expr in
      let left_ty, _, right_ty = expect_pair pair_ty in
      infer_expr (extend (extend ctx x2 right_ty) x1 left_ty) body
  | Ast.Inl value ->
      let left_ty = infer_expr ctx value in
      TySum (left_ty, fresh_storage_mode (), fresh_ty_var ())
  | Ast.Inr value ->
      let right_ty = infer_expr ctx value in
      TySum (fresh_ty_var (), fresh_storage_mode (), right_ty)
  | Ast.Match (scrutinee, x1, e1, x2, e2) ->
      let scrutinee_ty = infer_expr ctx scrutinee in
      let left_ty, _, right_ty = expect_sum scrutinee_ty in
      let branch1_ty = infer_expr (extend ctx x1 left_ty) e1 in
      let branch2_ty = infer_expr (extend ctx x2 right_ty) e2 in
      unify_ty branch1_ty branch2_ty
  | Ast.Annot (expr, annotation) ->
      let annotated_ty = ty_of_ast annotation in
      let inferred = infer_expr ctx expr in
      subtype_ty inferred annotated_ty;
      annotated_ty

(* infer_top infers a top-level expression under the empty context. *)
let infer_top expr = infer_expr empty_context expr

let infer expr = ty_to_ast (infer_top expr)

let string_of_inferred_ty ty =
  match ty_to_ast_opt ty with
  | Some ast -> Pretty.string_of_ty ast
  | None -> "<unknown type>"

let string_of_error = function
  | Unbound_variable x -> Printf.sprintf "Unbound variable %s" x
  | Expected_function ty ->
      Printf.sprintf "Expected a function type, found %s" (string_of_inferred_ty ty)
  | Expected_pair ty ->
      Printf.sprintf "Expected a pair type, found %s" (string_of_inferred_ty ty)
  | Expected_sum ty ->
      Printf.sprintf "Expected a sum type, found %s" (string_of_inferred_ty ty)
  | Cannot_infer what ->
      Printf.sprintf "Cannot infer the type of %s; add a type annotation" what
  | Not_a_subtype (t1, t2) ->
      Printf.sprintf "%s is not a subtype of %s"
        (string_of_inferred_ty t1)
        (string_of_inferred_ty t2)
