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

(* Asserts the leq_in relation between every axis in the lower and upper modes.
  Uses the mode solver functions directly. *)
let assert_modes_leq lower upper =
  Modesolver.Uniqueness.assert_leq_in lower.uniqueness upper.uniqueness;
  Modesolver.Contention.assert_leq_in lower.contention upper.contention;
  Modesolver.Linearity.assert_leq_in lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_in lower.portability upper.portability;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

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

let assert_storage_leq (lower : storage_mode) (upper : storage_mode) =
  Modesolver.Uniqueness.assert_leq_in lower.uniqueness upper.uniqueness;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

let assert_future_leq (lower : future_mode) (upper : future_mode) =
  Modesolver.Linearity.assert_leq_in lower.linearity upper.linearity;
  Modesolver.Portability.assert_leq_in lower.portability upper.portability;
  Modesolver.Areality.assert_leq_in lower.areality upper.areality

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

let component_modes_sum = component_modes_pair

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
