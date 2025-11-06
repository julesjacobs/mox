# Helly-2 Slice Checker

`helly_checker.py` exposes a tiny API for checking the Helly-2 slice property from
`tex/resolver.tex`. Pass a dictionary of sorts and a list of named relations to
`check_helly`, then print the returned `HellyResult`.

## Library Usage

```bash
python3 -q <<'PY'
from elimrel.helly_checker import Relation, Predicate, check_helly, create_helly_report

sorts = {"A": ["a0", "a1"]}
relations = [Relation("Id", "A", "A", (("a0", "a0"), ("a1", "a1")))]
predicates = [Predicate("OnlyA0", "A", ["a0"])]

result = check_helly(sorts, relations, predicates=predicates)
print(result.to_text())

create_helly_report("helly_report.html", sorts, relations, predicates=predicates)
print("Report written to helly_report.html")
PY
```

## Command Line

The module can also be used as a CLI by pointing it at a Python module that exposes
`sorts` and `relations`:

```bash
python3 -m elimrel.helly_checker elimrel.examples.helly_violation
```

Pass `--report out.html` to emit an HTML report alongside the console summary. If the
module exposes a `predicates` list (or its `build_family()` returns `(sorts, relations,
predicates)`), those predicates are included automatically. The
process exits with status `0` when every sort satisfies Helly-2 and `1` when a
counterexample is found; the offending slices are printed with provenance.

## Examples

- `elimrel/examples/helly_violation.py` declares a bad triple of slices that violates
  Helly-2 (`python3 -m elimrel.helly_checker elimrel.examples.helly_violation`).
- `elimrel/examples/diff_constraints.py` models the difference constraints `x ≤ y + k`
  for `k ∈ {-3,…,3}` over `{0,1,2,3}` and satisfies Helly-2 (`python3 -m
  elimrel.helly_checker elimrel.examples.diff_constraints`).
