from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {
    "A": ["a0", "a1", "a2"],
}

relations = [
    Relation(
        "R",
        "A",
        "A",
        (
            ("a0", "a1"),
            ("a0", "a2"),
            ("a1", "a0"),
            ("a1", "a2"),
            ("a2", "a0"),
            ("a2", "a1"),
        ),
    )
]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_suffix(".html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — helly_violation")
    print(f"Report written to {report_path}")
