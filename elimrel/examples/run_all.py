#!/usr/bin/env python3
"""Run the Helly checker across every example in one shot."""

from __future__ import annotations

import argparse
import importlib
from pathlib import Path
import sys
from typing import Iterable, Mapping, Optional, Sequence, Tuple

EXAMPLES_ROOT = Path(__file__).resolve().parent
REPO_ROOT = EXAMPLES_ROOT.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from elimrel.helly_checker import HellyCheckError, HellyResult, create_helly_report


def _load_family(module: object) -> Tuple[Mapping[str, Sequence[str]], Iterable, Optional[Iterable]]:
    if hasattr(module, "build"):
        data = module.build()  # type: ignore[attr-defined]
        if isinstance(data, tuple):
            if len(data) == 2:
                sorts, relations = data
                return sorts, relations, None
            if len(data) == 3:
                sorts, relations, predicates = data
                return sorts, relations, predicates
        raise HellyCheckError("build() must return (sorts, relations[, predicates])")
    sorts = getattr(module, "sorts", None)
    relations = getattr(module, "relations", None)
    predicates = getattr(module, "predicates", None)
    if sorts is None or relations is None:
        raise HellyCheckError("examples must define `sorts` and `relations`, or a build() function")
    return sorts, relations, predicates


def _discover_examples() -> Sequence[str]:
    names = []
    for path in sorted(EXAMPLES_ROOT.iterdir()):
        if not path.is_dir():
            continue
        if path.name.startswith("__"):
            continue
        if (path / "__init__.py").exists():
            names.append(path.name)
    return names


def _run_example(name: str, include_outer_products: bool = False) -> HellyResult:
    module_name = f"elimrel.examples.{name}"
    module = importlib.import_module(module_name)
    sorts, relations, predicates = _load_family(module)
    example_root = EXAMPLES_ROOT / name
    report_path = example_root / "report.html"
    solver_prefix = example_root / "solver"
    return create_helly_report(
        report_path,
        sorts,
        relations,
        predicates=predicates,
        title=f"Helly-2 Report — {name}",
        include_outer_products=include_outer_products,
        solver_prefix=solver_prefix,
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Run the Helly checker across every packaged example.")
    parser.add_argument(
        "--include-outer-products",
        action="store_true",
        help="Include outer-product relations in the report output.",
    )
    args = parser.parse_args(argv)

    names = _discover_examples()
    if not names:
        print("No examples found.", flush=True)
        return 0

    failures: list[Tuple[str, str]] = []
    for name in names:
        print(f"Running Helly checker for {name}...", flush=True)
        try:
            result = _run_example(name, include_outer_products=args.include_outer_products)
        except (HellyCheckError, ModuleNotFoundError) as exc:
            print(f"  Failed: {exc}", flush=True)
            failures.append((name, str(exc)))
            continue
        status = "ok" if result.ok else "violations found"
        print(
            f"  Result: {status} — closure size {result.closure_size} across {result.num_sorts} sorts",
            flush=True,
        )
        example_root = EXAMPLES_ROOT / name
        print(f"  Report: {example_root / 'report.html'}", flush=True)
        print(f"  Solver: {(example_root / 'solver.ml')} / {(example_root / 'solver.mli')}", flush=True)

    if failures:
        print("\nFailures:", flush=True)
        for name, message in failures:
            print(f"- {name}: {message}", flush=True)
        return 1

    print("\nAll examples processed.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
