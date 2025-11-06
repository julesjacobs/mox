from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {
    "uniqueness": ("unique", "aliased"),
    "contention": ("uncontended", "shared", "contended"),
    "linearity": ("many", "once"),
    "portability": ("portable", "nonportable"),
    "areality": ("global", "stack", "borrowed"),
}

relations = [
    Relation("uniqueness<=", "uniqueness", "uniqueness", (("aliased", "aliased"), ("aliased", "unique"), ("unique", "unique"))),
    Relation("contention<=", "contention", "contention", (("contended", "contended"), ("shared", "contended"), ("uncontended", "contended"), ("shared", "shared"), ("uncontended", "shared"), ("uncontended", "uncontended"))),
    Relation("linearity<=", "linearity", "linearity", (("many", "many"), ("many", "once"), ("once", "once"))),
    Relation("portability<=", "portability", "portability", (("nonportable", "nonportable"), ("portable", "nonportable"), ("portable", "portable"))),
    Relation("areality<=", "areality", "areality", (("borrowed", "borrowed"), ("global", "borrowed"), ("global", "global"), ("global", "stack"), ("stack", "borrowed"), ("stack", "stack"))),
    Relation("areality<=in", "areality", "areality", (("borrowed", "borrowed"), ("global", "global"), ("global", "stack"), ("stack", "stack"))),
    Relation("linearity_dagger_uniqueness", "linearity", "uniqueness", (("many", "aliased"), ("once", "aliased"), ("once", "unique"))),
    Relation("portability_dagger_contention", "portability", "contention", (("nonportable", "contended"), ("nonportable", "shared"), ("nonportable", "uncontended"), ("portable", "uncontended"))),
]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_suffix(".html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — elimrel full")
    print(f"Report written to {report_path}")

