from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {
    "A": ["0", "1"],
}

relations = [
    Relation(
        "not_both",    
        "A",
        "A",
        (
            ("0", "0"),
            ("0", "1"),
            ("1", "0"),
        ),
    ),
    Relation(
        "implies",    
        "A",
        "A",
        (
            ("0", "0"),
            ("0", "1"),
            ("1", "1"),
        ),
    ),
]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_suffix(".html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — split")
    print(f"Report written to {report_path}")
