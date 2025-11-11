from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {
    "A": ["0", "1"],
}

relations = [
    Relation(
        "x_or_y",    
        "A",
        "A",
        (
            ("0", "1"),
            ("1", "0"),
            ("1", "1"),
        ),
    ),
    Relation(
        "x_or_not_y",    
        "A",
        "A",
        (
            ("0", "0"),
            ("0", "1"),
            ("1", "0"),
        ),
    ),
    Relation(
        "not_x_or_y",    
        "A",
        "A",
        (
            ("1", "1"),
            ("0", "0"),
            ("0", "1"),
        ),
    ),
    Relation(
        "not_x_or_not_y",    
        "A",
        "A",
        (
            ("1", "0"),
            ("0", "1"),
            ("0", "0"),
        ),
    ),
]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_name("report.html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — two_sat")
    print(f"Report written to {report_path}")
