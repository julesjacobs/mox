open Modes

type storage_mode = Ast.storage_mode =
  { uniqueness : Modes.Uniqueness.t;
    areality : Modes.Areality.t }

type ty =
  | TyUnit
  | TyEmpty
  | TyArrow of ty * Future.t * ty
  | TyPair of ty * storage_mode * ty
  | TySum of ty * storage_mode * ty
  | TyMeta of meta

and mode_vars =
  { uniqueness : Modesolver.Uniqueness.var;
    contention : Modesolver.Contention.var;
    linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

and meta =
  { mutable solution : ty option;
    (* Invariant:
       - bounds only reference unsolved metas (TyMeta with [solution = None])
       - the bound graph is kept transitively closed (edges imply their consequences) *)
    mutable lower_bounds : meta list;
    mutable upper_bounds : meta list;
    modes : mode_vars }

let fresh_meta ?solution ?(lower_bounds = []) ?(upper_bounds = []) ~modes () =
  { solution;
    lower_bounds;
    upper_bounds;
    modes }

let rec solve_with_unit meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyUnit;
      List.iter solve_with_unit meta.lower_bounds;
      List.iter solve_with_unit meta.upper_bounds;
      meta.lower_bounds <- [];
      meta.upper_bounds <- []

let rec solve_with_empty meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyEmpty;
      List.iter solve_with_empty meta.lower_bounds;
      List.iter solve_with_empty meta.upper_bounds;
      meta.lower_bounds <- [];
      meta.upper_bounds <- []

let ensure_unsolved label meta =
  match meta.solution with
  | None -> ()
  | Some _ ->
      invalid_arg
        (Printf.sprintf "assert_subtype: %s meta is already solved" label)

let has_bound target bounds =
  List.exists
    (fun meta -> meta == target)
    bounds

let insert_bound target bounds =
  if has_bound target bounds then (bounds, false)
  else (target :: bounds, true)

let assert_modes_leq lower upper = failwith "TODO"

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

let component_modes_pair modes = failwith "TODO"
let assert_storage_leq lower upper = failwith "TODO"

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
