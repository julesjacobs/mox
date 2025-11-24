# Mox

Mox is an experimental OxCaml-like calculus that explores a mode system for reasoning about aliasing, borrowing, placement, and concurrency. The key difference with OxCaml is that we unify modes/modalities/mode-crossing into one concept.

## Language grammar

```ebnf
expr ::=
    x                                         -- variable
  | unit | int | true | false                 -- base literals
  | ? | (expr : ty)                           -- typed holes or annotations
  | fun x => expr | rec f x => expr           -- heap-allocated functions
  | $fun x => expr | $rec f x => expr         -- stack-allocated closures
  | expr expr                                 -- application
  | let x = expr in expr                      -- shared binding
  | let (x, y) = expr in expr                -- pair bind
  | let! (x, y) = expr in expr                -- destructive pair bind
  | borrow x = expr for y = expr in expr      -- temporary unique borrow
  | if expr then expr else expr | absurd expr -- control flow/elimination for empty
  | expr + expr | expr - expr | expr * expr | -expr
  | expr == expr | expr < expr | expr <= expr | expr > expr | expr >= expr
  | expr and expr | expr or expr | not expr
  | match expr with left(x) => expr | right(y) => expr -- shared sum matches
  | match! expr with left(x) => expr | right(y) => expr -- destructive sum matches
  | match expr with [] => expr | x :: y => expr -- shared list matches
  | match! expr with [] => expr | x :: y => expr -- destructive list matches
  | (expr, expr) | left(expr) | right(expr)   -- product and sum constructors
  | [expr, ...] | expr :: expr                -- list literals/cons
  | $(expr, expr) | $left(expr) | $right(expr)
  | $[expr, ...] | $expr :: expr               -- stack-allocated list constructors
  | region expr                               -- stack region
  | ref expr | !expr | expr := expr           -- mutable references
  | fork expr                                 -- spawn a concurrent thread

ty ::=
    unit | empty | int | bool
  | ty *[m] ty | ty +[m] ty                   -- optional storage modes m = [u=<..> a=<..>]
  | list[m] ty                                -- list with storage mode
  | ref[m] ty                                 -- reference with contention mode
  | ty ->[m] ty                               -- functions with future mode (a,l,p)
```

## Mode axes

Mox separates *past* and *future* capabilities. Every axis supports two orders:

- `≤ₜₒ` (“convert to”) lets us forget guarantees (turn `unique` into `aliased`, for example).
- `≤ᵢₙ` (“may live in”) governs what may be placed inside what (an aliased child can live inside a unique container, but not the reverse).

Past axes (properties established already):

| Axis        | `≤ₜₒ` order                | `≤ᵢₙ` order |
|-------------|----------------------------|---------------------------------------|
| Uniqueness (`u`) | `unique ≤ₜₒ aliased`      | `aliased ≤ᵢₙ unique`                    |
| Contention (`c`) | `uncontended ≤ₜₒ shared ≤ₜₒ contended` | `contended ≤ᵢₙ shared ≤ᵢₙ uncontended` |

Future axes (restrictions on upcoming use):

| Axis           | `≤ₜₒ` order                         | `≤ᵢₙ` order |
|----------------|-------------------------------------|-------------|
| Linearity (`l`)| `many ≤ₜₒ once ≤ₜₒ never`               | same as `≤ₜₒ` |
| Portability (`p`)| `portable ≤ₜₒ nonportable`          | same as `≤ₜₒ` |
| Areality (`a`) | `global ≤ₜₒ borrowed` | `global ≤ᵢₙ global`, `borrowed ≤ᵢₙ borrowed` |
| Regionality (`r`)| `r∞ ≤ₜₒ r4 ≤ₜₒ … ≤ₜₒ r0` (reverse numeric) | same as `≤ₜₒ` |

- Past axes flip when stored: a unique container may hold only unique children (`aliased ≤ᵢₙ unique`), whereas future axes (except for `borrowed`) weaken going inward (a `many` value can live inside an `once` container).
- Linearity and portability also interact with closures: capturing an environment in a `many` closure marks those bindings as `aliased`, and capturing into a `portable` closure forces their contention to become `contended`.
- Areality now only distinguishes owned (`global`) values from temporary `borrowed` ones; borrowed values cannot be nested inside non-borrowed data.
- Regionality tracks concrete regions (heap = `r∞`, stack = `r0`), ordered in reverse numeric order so outer regions are “smaller”.

These component-wise relations power the mode solver described in `tex/mox.tex`.

## Examples

### Stack allocation and locality

Stack-allocated constructors are indicated with `$` and pin their regionality to a stack slot. You can repeat `$` to target an older stack region (`$` = region 0, `$$` = region 1, `$$$` = region 2, …). Areality stays `global`, but the regionality axis keeps stack data from escaping its enclosing `region`:

```mox
region
  let tmp = $(unit, unit) in
  let (x, y) = tmp in
  x
```

That is valid, but this is not:

```mox
region
  let tmp = $(unit, unit) in
  tmp
```

Inference rejects the program because stack-bound regionality cannot escape.

### Destructive matching and uniqueness

`let!` and `match!` demand a `unique` scrutinee. They give exclusive access to the components and forbid the original aggregate from being used again:

```mox
let unique_pair = (unit, unit) in
let! (x, y) = unique_pair in
x
```

Attempting a destructive match on an aliased value (for example one produced by duplicating a pair) fails for the same reason—uniqueness must be preserved until the pattern consumes the value.

### Concurrence with portability and contention

`fork` spawns a new thread. References become contended when they cross a thread boundary, and reading/writing is an error, to prevent data races:

```mox
let r = ref 3 in
fork (let x = !r in x)
```

Likewise, capturing stack-allocated unique pairs in a forked closure is rejected—the closure would outlive the region where the data is valid. The test suite in `tests/mox/codex.mox` contains many more edge cases that illustrate how portability and contention interact.

## Running Mox programs

Install dependencies and build the project:

```bash
opam install . --deps-only
dune build
```

`tests/mox/` contains the example files. Each `.mox` file holds a sequence of expressions separated by blank lines. The implementation will show the inferred type or type error of every expression on the next line beginnig with `>`:

```
2 + 3
> int
```

To run all the `.mox` files in `tests/mox`, do:

```bash
./mox.sh
git status  # inspect the delta
```

## Repository

- `src/` – AST, parser, lexer, mode solver, pretty-printer, type inference.
- `bin/` – CLI entry point and the `record` harness.
- `tests/mox/` – representative programs covering core typing features, locking, borrowing, linearity, contention, and error cases.
- `tex` – a LaTeX notes that spells out the formal typing and mode rules that guide the implementation.
