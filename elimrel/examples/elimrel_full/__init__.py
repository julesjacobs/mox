import argparse
from pathlib import Path

from elimrel.helly_checker import Predicate, Relation, check_helly, create_helly_report

sorts = {
    "uniqueness": ("unique", "aliased", "taken"),
    "contention": ("uncontended", "shared", "contended"),
    "linearity": ("many", "once", "never"),
    "portability": ("portable", "nonportable"),
    "areality": ("global", "regional", "local", "borrowed"),
}

def leq(elems):
    n = len(elems)
    return [(elems[i],elems[j]) for i in range(0,n) for j in range(i,n)]

def leqrel(name):
    return Relation(f"{name}<=", name, name, leq(sorts[name]))

relations = [
    leqrel('uniqueness'), 
    leqrel('contention'), 
    leqrel('linearity'), 
    leqrel('portability'), 
    leqrel('areality'),
    Relation("areality<=in", "areality", "areality", (
        ("borrowed", "borrowed"), 
        ("global", "global"), ("global", "regional"), ("global", "local"), 
        ("regional", "regional"), ("regional", "local"), 
        ("local", "local")
    )),
    Relation("linearity_dagger_uniqueness", "linearity", "uniqueness", (
        ("many", "aliased"), 
        ("once", "unique"),
        ("once", "aliased"),
        ("never", "taken"),
        ("never", "aliased"),
        ("never", "unique")
    )),
    Relation("portability_dagger_contention", "portability", "contention", (
        ("portable", "contended"), 
        ("nonportable", "contended"), 
        ("nonportable", "shared"), 
        ("nonportable", "uncontended"), 
    )),
    Relation("shared_modality", "contention", "contention", (
        ("contended", "shared"),
        ("shared", "shared"),
        ("uncontended", "uncontended"),
    )),
    Relation("not_both_unique", "uniqueness", "uniqueness", (
        ("unique", "taken"),
        ("taken", "unique"),
        ("aliased", "aliased"),
        ("aliased", "taken"),
        ("taken", "aliased"),
        ("taken", "taken"),
    )),
    Relation("is_callable_linearity", "linearity", "uniqueness", (
        ("many", "aliased"),
        ("once", "unique"),
    )),
]

predicates = [
    Predicate(f"{sort}={value}", sort, (value,))
    for sort, values in sorts.items()
    for value in values
]

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Run the elimrel full Helly-2 check and emit an HTML report."
    )
    parser.add_argument(
        "--include-outer-products",
        action="store_true",
        help="Show relations whose matrices are full outer products (normally hidden).",
    )
    args = parser.parse_args()

    result = check_helly(sorts, relations, predicates=predicates)
    print(result.to_text())
    report_path = Path(__file__).with_name("report.html")
    create_helly_report(
        report_path,
        sorts,
        relations,
        predicates=predicates,
        title="Helly-2 Report — elimrel full",
        include_outer_products=args.include_outer_products,
    )
    print(f"Report written to {report_path}")
