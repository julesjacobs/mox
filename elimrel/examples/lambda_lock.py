from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {
    "token": ["0", "1"],
}

relations = [
    Relation(
        "disjoint_tokens",
        "token",
        "token",
        (
            ("0", "1"),
            ("1", "0"),
            ("0", "0"),
        ),
    ),
    Relation(
        "leq_token",
        "token",
        "token",
        (
            ("1", "1"),
            ("0", "1"),
            ("0", "0"),
        ),
    ),
]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_suffix(".html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — lambda_lock")
    print(f"Report written to {report_path}")
