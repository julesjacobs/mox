from pathlib import Path

from elimrel.helly_checker import Relation, check_helly, create_helly_report

sorts = {"A": ["0", "1", "2", "3"]}

relations = [
    Relation(
        f"le_plus_{k}",
        "A",
        "A",
        tuple(
            (str(x), str(y))
            for x in range(4)
            for y in range(4)
            if x <= y + k
        ),
    )
    for k in range(-3, 4)
]

relations = [rel for rel in relations if rel.pairs]

if __name__ == "__main__":
    result = check_helly(sorts, relations)
    print(result.to_text())
    report_path = Path(__file__).with_name("report.html")
    create_helly_report(report_path, sorts, relations, title="Helly-2 Report — diff_constraints")
    print(f"Report written to {report_path}")
