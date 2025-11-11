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

and meta =
  { mutable solution : ty option;
    (* Invariant:
       - bounds only reference unsolved metas (TyMeta with [solution = None])
       - the bound graph is kept transitively closed (edges imply their consequences) *)
    mutable lower_bounds : ty list;
    mutable upper_bounds : ty list;
    uniqueness : Modesolver.Uniqueness.var;
    contention : Modesolver.Contention.var;
    linearity : Modesolver.Linearity.var;
    portability : Modesolver.Portability.var;
    areality : Modesolver.Areality.var }

let fresh_meta ?solution ?(lower_bounds = []) ?(upper_bounds = []) () =
  { solution;
    lower_bounds;
    upper_bounds;
    uniqueness = Modesolver.Uniqueness.new_var ();
    contention = Modesolver.Contention.new_var ();
    linearity = Modesolver.Linearity.new_var ();
    portability = Modesolver.Portability.new_var ();
    areality = Modesolver.Areality.new_var () }

let rec solve_with_unit meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyUnit;
      let solve_bound = function
        | TyMeta other -> solve_with_unit other
        | _ -> ()
      in
      List.iter solve_bound meta.lower_bounds;
      List.iter solve_bound meta.upper_bounds;
      meta.lower_bounds <- [];
      meta.upper_bounds <- []

let rec solve_with_empty meta =
  match meta.solution with
  | Some _ -> ()
  | None ->
      meta.solution <- Some TyEmpty;
      let solve_bound = function
        | TyMeta other -> solve_with_empty other
        | _ -> ()
      in
      List.iter solve_bound meta.lower_bounds;
      List.iter solve_bound meta.upper_bounds;
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
    (function
      | TyMeta meta when meta == target -> true
      | _ -> false)
    bounds

let insert_bound target bounds =
  if has_bound target bounds then (bounds, false)
  else (TyMeta target :: bounds, true)

let rec assert_subtype lower upper =
  if lower == upper then ()
  else (
    ensure_unsolved "lower" lower;
    ensure_unsolved "upper" upper;
    let updated, changed_lower = insert_bound upper lower.upper_bounds in
    lower.upper_bounds <- updated;
    let updated, changed_upper = insert_bound lower upper.lower_bounds in
    upper.lower_bounds <- updated;
    if changed_lower || changed_upper then (
      let propagate_lower = function
        | TyMeta lower_lower -> assert_subtype lower_lower upper
        | _ -> ()
      in
      let propagate_upper = function
        | TyMeta upper_upper -> assert_subtype lower upper_upper
        | _ -> ()
      in
      List.iter propagate_lower lower.lower_bounds;
      List.iter propagate_upper upper.upper_bounds))
