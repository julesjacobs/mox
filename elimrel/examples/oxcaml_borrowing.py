import argparse
from pathlib import Path

from elimrel.helly_checker import Predicate, Relation, check_helly, create_helly_report

sorts = {
    "uniqueness": ("unique", "aliased"),
    "contention": ("uncontended", "shared", "contended"),
    "linearity": ("many", "once"),
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
    Relation("global_in", "areality", "areality", (
        ("borrowed", "borrowed"), 
        ("local", "borrowed"), 
        ("regional", "borrowed"), 
        ("global", "borrowed"), 
        ("global", "global"),
        ("global", "regional"),
        ("global", "local"),
    )),
    Relation("global_out", "areality", "areality", (
        ("borrowed", "borrowed"), 
        ("global", "global"), ("global", "regional"), ("global", "local"), ("global", "borrowed"),
        ("regional", "global"), ("regional", "regional"), ("regional", "local"), ("regional", "borrowed"),
        ("local", "global"), ("local", "regional"), ("local", "local"), ("local", "borrowed"),
    )),
    Relation("linearity_dagger_uniqueness", "linearity", "uniqueness", (
        ("many", "aliased"), 
        ("once", "unique"),
        ("once", "aliased"),
    )),
    Relation("portability_dagger_contention", "portability", "contention", (
        ("portable", "contended"),
        ("nonportable", "contended"),
        ("nonportable", "shared"),
        ("nonportable", "uncontended"), 
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
    report_path = Path(__file__).with_suffix(".html")
    create_helly_report(
        report_path,
        sorts,
        relations,
        predicates=predicates,
        title="Helly-2 Report — oxcaml",
        include_outer_products=args.include_outer_products,
    )
    print(f"Report written to {report_path}")
