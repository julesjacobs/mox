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
    add_constraint meta (In { target = meta; mode_vars = mode_vars })
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

let assert_alias source target = 
  outer_equiv source target;
  match (zonk source, zonk target) with
  | TyMeta source_meta, TyMeta target_meta ->
    let constraint_ = mk_constraint (Alias { source = source_meta; target = target_meta }) in
    add_constraint source_meta constraint_;
    add_constraint target_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair (source_left, source_storage, source_right), TyPair (target_left, target_storage, target_right) ->
    failwith "TODO"
  | TySum (source_left, source_storage, source_right), TySum (target_left, target_storage, target_right) ->
    failwith "TODO"
  | TyArrow (source_domain, source_future, source_codomain), TyArrow (target_domain, target_future, target_codomain) ->
    failwith "TODO"
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

let infer _expr = raise (Error "type inference (new solver) not implemented yet")
