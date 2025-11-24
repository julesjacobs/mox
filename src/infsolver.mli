(** Robust Graph-Based Integer Solver.
   
   This solver operates on the domain of Extended Non-Negative Integers:
   [0, +infinity].
   
   It uses a "Longest Path" graph algorithm to propagate lower bounds 
   and strict assertions to enforce upper bounds.
*)

(* ========================================================================= *)
(* TYPES & EXCEPTIONS                                                        *)
(* ========================================================================= *)

(** An abstract handle to a variable in the solver. *)
type var

(** Raised when a constraint leads to a logical inconsistency 
    (e.g., Lower Bound > Upper Bound). Carries the offending variable name and
    the conflicting bounds. *)
type contradiction =
  { var : string;
    lower : int;
    upper : int;
    lower_repr : string;
    upper_repr : string }
exception Contradiction of contradiction

(* ========================================================================= *)
(* CONSTANTS                                                                 *)
(* ========================================================================= *)

(** The integer representation of +Infinity. 
    Arithmetic operations involving this value are "sticky" (saturated). *)
val infinity : int

(* ========================================================================= *)
(* LIFECYCLE                                                                 *)
(* ========================================================================= *)

(** [create_var ?name ()] creates a new variable initialized to [0, +oo]. 
    The optional name is used for debugging and error messages. *)
val create_var : ?name:string -> unit -> var

(** Resets the global solver state (clears all variables and constraints). *)
val reset : unit -> unit

(* ========================================================================= *)
(* CONSTRAINTS                                                               *)
(* ========================================================================= *)

(** [assert_leq x y] asserts that x <= y.
    
    Logic:
    - Propagates lower bounds: y.lower >= x.lower.
    - If x increases, y increases.
    - Raises [Contradiction] if this forces y above its static upper bound. *)
val assert_leq : var -> var -> unit

(** [decrease_by x delta y] asserts [y >= x + delta].
    Use positive [delta] to express a lower bound reduction on [y] relative to [x]. *)
val decrease_by : var -> int -> var -> unit

(** [increase_by x delta y] asserts [y >= x - delta].
    Equivalent to [decrease_by x (-delta) y]; useful for modeling predecessors. *)
val increase_by : var -> int -> var -> unit

(** [assert_eq_const x k] asserts that x = k.
    
    Logic:
    - Sets x.upper = k.
    - Sets x.lower = k.
    - Propagates this value to neighbors.
    - [k] can be [Solver.infinity]. *)
val assert_eq_const : var -> int -> unit

(** [assert_predecessor x y] asserts the relation set: 
    { y = x - 1 /\ x >= 1 }.
    
    Logic:
    - Enforces y >= x - 1.
    - Enforces x >= y + 1.
    - Automatically derives x >= 1 (since y >= 0). *)
val assert_predecessor : var -> var -> unit

(* ========================================================================= *)
(* INSPECTION                                                                *)
(* ========================================================================= *)

(** Returns the current dynamic lower bound of the variable. *)
val get_lower : var -> int

(** Returns the current static upper bound of the variable. *)
val get_upper : var -> int

(** Prints the current bounds of all variables to stdout. 
    Format: "name: [lower, upper]" *)
val print_model : unit -> unit
