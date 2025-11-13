open Modes

module StringSet = Set.Make (String)
module ModeInfoSet = Set.Make (String)

module ModeName = struct
  type t =
    { tbl : (Obj.t, string) Hashtbl.t;
      mutable counter : int;
      prefix : string }

  let create prefix =
    { tbl = Hashtbl.create 16; counter = 0; prefix }

  let name t var =
    let key = Obj.repr var in
    match Hashtbl.find_opt t.tbl key with
    | Some n -> n
    | None ->
        t.counter <- t.counter + 1;
        let n = Printf.sprintf "%s%d" t.prefix t.counter in
        Hashtbl.add t.tbl key n;
        n
end

type mode_print_state =
  { u : ModeName.t;
    a : ModeName.t;
    l : ModeName.t;
    p : ModeName.t;
    c : ModeName.t;
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

let remove_vars vars set =
  List.fold_left (fun acc var -> StringSet.remove var acc) set vars

let rec free_vars expr =
  match expr with
  | Ast.Var x -> StringSet.singleton x
  | Ast.Unit -> StringSet.empty
  | Ast.Hole -> StringSet.empty
  | Ast.Absurd e -> free_vars e
  | Ast.Annot (e, _) -> free_vars e
  | Ast.Fun (_, x, body) -> free_vars_without body [ x ]
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

let force_storage_local (storage : storage_mode) =
  Modesolver.Areality.restrict_domain [Areality.local] storage.areality

let force_future_local (future : future_mode) =
  Modesolver.Areality.restrict_domain [Areality.local] future.areality

let force_storage_unique (storage : storage_mode) =
  Modesolver.Uniqueness.restrict_domain [Uniqueness.unique] storage.uniqueness
let const_uniqueness_var value =
  Modesolver.Uniqueness.new_var ~domain:[value] ()

let const_contention_var value =
  Modesolver.Contention.new_var ~domain:[value] ()

let const_areality_var value =
  Modesolver.Areality.new_var ~domain:[value] ()

let const_linearity_var value =
  Modesolver.Linearity.new_var ~domain:[value] ()

let const_portability_var value =
  Modesolver.Portability.new_var ~domain:[value] ()

let top_mode_vars () : mode_vars =
  (* Mode lattice top: type unrestricted on every axis. Useful when rules require
     checking subcomponents at ⊤₍in₎ (see tex/mox.tex §Kinding). *)
  { uniqueness = const_uniqueness_var Uniqueness.top_in;
    contention = const_contention_var Contention.top_in;
    linearity = const_linearity_var Linearity.top_in;
    portability = const_portability_var Portability.top_in;
    areality = const_areality_var Areality.top_in }

let global_mode_vars () : mode_vars =
  let mode = top_mode_vars () in
  { mode with areality = const_areality_var Areality.global }

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

let alias_linearity_relation =
  Relations.make
    [ (Linearity.many, Linearity.many);
      (Linearity.once, Linearity.never);
      (Linearity.never, Linearity.never) ]

let assert_equal_in assert_leq var1 var2 =
  assert_leq var1 var2;
  assert_leq var2 var1

let assert_equal_areality (left : Modesolver.Areality.var) (right : Modesolver.Areality.var) =
  Modesolver.Areality.assert_leq_to left right;
  Modesolver.Areality.assert_leq_to right left

let assert_equal_portability (left : Modesolver.Portability.var) (right : Modesolver.Portability.var) =
  Modesolver.Portability.assert_leq_to left right;
  Modesolver.Portability.assert_leq_to right left

(* -------------------------------------------------------------------------- *)
(* Error reporting.                                                           *)

type error = string

exception Error of error

let string_of_error err = err

let type_error message = raise (Error message)

let assert_callable (future : future_mode) =
  try Modesolver.Linearity.restrict_domain [Linearity.many; Linearity.once] future.linearity with
  | Modesolver.Inconsistent _ ->
      type_error "cannot call a function whose linearity is never"

module IntSet = Set.Make (Int)

let describe_uniqueness var = Modesolver.describe_var Modes.Uniqueness.to_string var
let describe_areality var = Modesolver.describe_var Modes.Areality.to_string var
let describe_linearity var = Modesolver.describe_var Modes.Linearity.to_string var
let describe_portability var = Modesolver.describe_var Modes.Portability.to_string var
let describe_contention var = Modesolver.describe_var Modes.Contention.to_string var

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

(* -------------------------------------------------------------------------- *)


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

let rec assert_in ty mode_vars =
  match zonk ty with
  | TyMeta meta ->
    (* Record α : m by attaching an in-placement constraint to the meta. *)
    add_constraint meta (mk_constraint (In { target = meta; mode_vars }))
  | TyUnit -> ()
  | TyEmpty -> ()
  | TyPair (left, storage, right)
  | TySum (left, storage, right) ->
    assert_storage_within storage mode_vars;
    let component_mode = push_storage_to_components storage mode_vars in
    assert_in left component_mode;
    assert_in right component_mode
  | TyArrow (domain, future, codomain) ->
    (* \hat{f} ≤₍in₎ m *)
    Modesolver.Areality.assert_leq_in future.areality mode_vars.areality;
    Modesolver.Linearity.assert_leq_in future.linearity mode_vars.linearity;
    Modesolver.Portability.assert_leq_in future.portability mode_vars.portability;
    let top_mode = top_mode_vars () in
    assert_in domain top_mode;
    assert_in codomain top_mode

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

(* Core constraint propagation and meta assignment. *)
let rec outer_equiv ty1 ty2 =
  match (zonk ty1, zonk ty2) with
  | TyMeta meta1, TyMeta meta2 -> ()
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair _, TyPair _ -> ()
  | TySum _, TySum _ -> ()
  | TyArrow _, TyArrow _ -> ()
  | TyUnit, TyMeta meta | TyMeta meta, TyUnit ->
      set_meta_solution meta TyUnit
  | TyEmpty, TyMeta meta | TyMeta meta, TyEmpty ->
      set_meta_solution meta TyEmpty
  | TyPair _, TyMeta meta | TyMeta meta, TyPair _ ->
      let storage = fresh_storage_mode () in
      let left = fresh_meta () in
      let right = fresh_meta () in
      set_meta_solution meta (TyPair (TyMeta left, storage, TyMeta right))
  | TySum _, TyMeta meta | TyMeta meta, TySum _ ->
      let storage = fresh_storage_mode () in
      let left = fresh_meta () in
      let right = fresh_meta () in
      set_meta_solution meta (TySum (TyMeta left, storage, TyMeta right))
  | TyArrow _, TyMeta meta | TyMeta meta, TyArrow _ ->
      let future = fresh_future_mode () in
      let domain = fresh_meta () in
      let codomain = fresh_meta () in
      set_meta_solution meta (TyArrow (TyMeta domain, future, TyMeta codomain))
  | _ ->
      type_error "outer_equiv: not equivalent"

and assert_subtype lower upper =
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

and assert_alias source target =
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
  | TyArrow (_source_domain, source_future, _source_codomain), TyArrow (_target_domain, target_future, _target_codomain) ->
      Modesolver.Linearity.assert_relation alias_linearity_relation source_future.linearity target_future.linearity;
      assert_equal_areality source_future.areality target_future.areality;
      assert_equal_portability source_future.portability target_future.portability;
  | _ ->
      type_error "assert_alias: not equivalent"

and assert_lock original locked future =
  log_lock "lock %s into %s" (string_of_ty original) (string_of_ty locked);
  outer_equiv original locked;
  match (zonk original, zonk locked) with
  | TyMeta original_meta, TyMeta locked_meta ->
      log_lock "record meta constraint original=?%d locked=?%d" original_meta.id locked_meta.id;
      let constraint_ = mk_constraint (Lock { original = original_meta; locked = locked_meta; future = future }) in
      add_constraint original_meta constraint_;
      add_constraint locked_meta constraint_
  | TyUnit, TyUnit -> ()
  | TyEmpty, TyEmpty -> ()
  | TyPair (original_left, original_storage, original_right), TyPair (locked_left, locked_storage, locked_right) ->
      log_lock "pair storage lock";
      (* Unique component joins with dagger(future), areality unchanged. *)
      Modesolver.Uniqueness.assert_leq_to original_storage.uniqueness locked_storage.uniqueness;
      Modesolver.assert_linearity_dagger future.linearity locked_storage.uniqueness;
      assert_equal_areality original_storage.areality locked_storage.areality;
      assert_lock original_left locked_left future;
      assert_lock original_right locked_right future
  | TySum (original_left, original_storage, original_right), TySum (locked_left, locked_storage, locked_right) ->
      log_lock "sum storage lock";
      Modesolver.Uniqueness.assert_leq_to original_storage.uniqueness locked_storage.uniqueness;
      Modesolver.assert_linearity_dagger future.linearity locked_storage.uniqueness;
      assert_equal_areality original_storage.areality locked_storage.areality;
      assert_lock original_left locked_left future;
      assert_lock original_right locked_right future
  | TyArrow (original_domain, original_future, original_codomain), TyArrow (locked_domain, locked_future, locked_codomain) ->
      log_lock "arrow lock enforcement";
      (* Locking leaves functions untouched provided ambient future ≤ function future. *)
      assert_future_leq_to future original_future;
      assert_future_leq_to original_future locked_future;
      assert_future_leq_to locked_future original_future;
      assert_subtype original_domain locked_domain;
      assert_subtype locked_domain original_domain;
      assert_subtype original_codomain locked_codomain;
      assert_subtype locked_codomain original_codomain
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

let top_mode_vars () : mode_vars =
  { uniqueness = const_uniqueness_var Uniqueness.top_in;
    contention = const_contention_var Contention.top_in;
    linearity = const_linearity_var Linearity.top_in;
    portability = const_portability_var Portability.top_in;
    areality = const_areality_var Areality.top_in }

(* -------------------------------------------------------------------------- *)
(* Pretty-printing inference types.                                           *)

let string_of_storage_mode state (storage : storage_mode) =
  Printf.sprintf "u=%s a=%s"
    (render_uni state storage.uniqueness)
    (render_are state storage.areality)

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

let add_entry (set : ModeInfoSet.t) acc entry =
  if ModeInfoSet.mem entry set then set, acc
  else ModeInfoSet.add entry set, entry :: acc

let add_uni_var (set : ModeInfoSet.t) acc var =
  add_entry set acc (Printf.sprintf "u: %s" (describe_uniqueness var))

let add_are_var (set : ModeInfoSet.t) acc var =
  add_entry set acc (Printf.sprintf "a: %s" (describe_areality var))

let add_lin_var (set : ModeInfoSet.t) acc var =
  add_entry set acc (Printf.sprintf "l: %s" (describe_linearity var))

let add_port_var (set : ModeInfoSet.t) acc var =
  add_entry set acc (Printf.sprintf "p: %s" (describe_portability var))

let add_cont_var (set : ModeInfoSet.t) acc var =
  add_entry set acc (Printf.sprintf "c: %s" (describe_contention var))

let add_storage_mode (set : ModeInfoSet.t) acc (storage : storage_mode) =
  let set, acc = add_uni_var set acc storage.uniqueness in
  add_are_var set acc storage.areality

let add_future_mode (set : ModeInfoSet.t) acc (future : future_mode) =
  let set, acc = add_are_var set acc future.areality in
  let set, acc = add_lin_var set acc future.linearity in
  add_port_var set acc future.portability

let add_mode_vars_record (set : ModeInfoSet.t) acc (mode_vars : mode_vars) =
  let set, acc = add_uni_var set acc mode_vars.uniqueness in
  let set, acc = add_cont_var set acc mode_vars.contention in
  let set, acc = add_lin_var set acc mode_vars.linearity in
  let set, acc = add_port_var set acc mode_vars.portability in
  add_are_var set acc mode_vars.areality

let rec string_of_ty_core state ty =
  match zonk ty with
  | TyUnit -> "unit"
  | TyEmpty -> "empty"
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
  | TyMeta meta ->
      (match meta.solution with
      | Some solution -> string_of_ty_core state solution
      | None -> Printf.sprintf "?%d" meta.id)

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
    | TyArrow (domain, _, codomain) ->
        let set, acc = aux set acc domain in
        aux set acc codomain
    | TyUnit | TyEmpty -> set, acc
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
  let meta_ref meta = Printf.sprintf "?%d" meta.id in
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

let lock_env env future =
  (* Apply the lock constraint to every binding so the function body only sees
     weakened capabilities allowed by [future]. *)
  List.map
    (fun (name, ty) ->
      let locked_ty = TyMeta (fresh_meta ()) in
      assert_lock ty locked_ty future;
      (name, locked_ty))
    env


let rec infer_with_env env expr = 
  match expr with
  | Ast.Var x ->
    (match lookup env x with
    | Some ty -> ty
    | None -> type_error (Printf.sprintf "Unbound variable %s" x))
  | Ast.Unit -> TyUnit
  | Ast.Pair (alloc, e1, e2) ->
    let left_fv = free_vars e1 in
    let right_fv = free_vars e2 in
    let env_left, env_right = split_env env left_fv right_fv in
    let ty1 = infer_with_env env_left e1 in
    let ty2 = infer_with_env env_right e2 in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = TyPair (ty1, storage, ty2) in
    ty
  | Ast.Inl (alloc, e) ->
    let ty_left = infer_with_env env e in
    let ty_right = TyMeta (fresh_meta ()) in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = TySum (ty_left, storage, ty_right) in
    ty
  | Ast.Inr (alloc, e) ->
    let ty_left = TyMeta (fresh_meta ()) in
    let ty_right = infer_with_env env e in
    let storage = fresh_storage_mode () in
    let () = match alloc with Ast.Stack -> force_storage_local storage | Ast.Heap -> () in
    let ty = TySum (ty_left, storage, ty_right) in
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
    let ty_pair = TyPair (ty_left, storage, ty_right) in
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
    let ty_sum = TySum (ty_left, storage, ty_right) in
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
    assert_callable future;
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
    let ty = ty_of_ast ty_syntax in
    let ty' = infer_with_env env e in
    assert_subtype ty' ty;
    ty'
  | Ast.Region e ->
    let ty = infer_with_env env e in
    let mode_vars = global_mode_vars () in
    assert_in ty mode_vars;
    ty

let infer expr =
  try infer_with_env [] expr with
  | Modesolver.Inconsistent msg -> type_error msg
