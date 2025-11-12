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
    modes : mode_vars;
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

let fresh_meta ?solution ?(constraints = []) ?modes () : meta =
  let modes = match modes with Some m -> m | None -> fresh_mode_vars () in
  { id = fresh_meta_id ();
    solution;
    modes;
    constraints }

(* -------------------------------------------------------------------------- *)
(* Constraint management. *)

let add_constraint meta constraint_ =
  if List.exists (fun existing -> existing.constraint_ = constraint_) meta.constraints then ()
  else meta.constraints <- { constraint_; fired = false } :: meta.constraints

let add_constraints meta constraints =
  List.iter (add_constraint meta) constraints

(* -------------------------------------------------------------------------- *)
(* Error reporting.                                                           *)

type error = string

exception Error of error

let string_of_error err = err

let type_error message = raise (Error message)

(* -------------------------------------------------------------------------- *)
(* Temporary public API stubs.                                                *)

let rec fire_constraints meta =
  let pending = meta.constraints in
  meta.constraints <- [];
  List.iter fire_constraint pending
and fire_constraint record =
  if record.fired then ()
  else (
    record.fired <- true;
    match record.constraint_ with
    | Sub {lower; upper} -> failwith "Sub constraints not implemented yet"
    | Alias {source; target} -> failwith "Alias constraints not implemented yet"
    | Lock {original; locked; future} -> failwith "Lock constraints not implemented yet"
    | In {target; mode_vars} -> failwith "In constraints not implemented yet")

let rec solve_with_unit meta =
  match meta.solution with
  | Some TyUnit -> ()
  | Some _ -> type_error "solve_with_unit: meta already solved to non-unit type"
  | None ->
      meta.solution <- Some TyUnit;
      fire_constraints meta


let infer _expr = raise (Error "type inference (new solver) not implemented yet")
