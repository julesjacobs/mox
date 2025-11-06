#!/usr/bin/env python3
"""Minimal Helly-2 slice checker for many-sorted relation families.

The public surface is intentionally small:

    >>> from elimrel.helly_checker import Relation, check_helly
    >>> sorts = {"A": ["a0", "a1"]}
    >>> relations = [Relation("Id", "A", "A", (("a0", "a0"), ("a1", "a1")))]
    >>> print(check_helly(sorts, relations).to_text())
    Helly-2 slice property holds for all sorts.
    Computed closure: 4 relations across 1 sorts.

The module also exposes a simple CLI that loads a Python module containing `sorts` and
`relations` definitions:

    python3 -m elimrel.helly_checker elimrel.examples.helly_violation
"""

from __future__ import annotations

import argparse
import importlib
from collections import deque
from dataclasses import dataclass, field
from html import escape
from pathlib import Path
from typing import Iterable, Mapping, MutableMapping, Optional, Sequence, Tuple, Union

Pair = Tuple[str, str]

__all__ = [
    "Relation",
    "SliceWitness",
    "HellyViolation",
    "HellyResult",
    "check_helly",
    "create_helly_report",
]


class HellyCheckError(ValueError):
    """Raised when the family description is inconsistent."""


@dataclass(frozen=True)
class Relation:
    """Named typed binary relation."""

    name: str
    source: str
    target: str
    pairs: Sequence[Pair]


@dataclass(frozen=True)
class SliceWitness:
    members: Tuple[str, ...]
    origins: Tuple[str, ...]


@dataclass(frozen=True)
class HellyViolation:
    sort: str
    slices: Tuple[SliceWitness, SliceWitness, SliceWitness]


@dataclass(frozen=True)
class HellyResult:
    ok: bool
    closure_size: int
    num_sorts: int
    violations: Tuple[HellyViolation, ...]

    def to_text(self) -> str:
        lines = []
        if self.ok:
            lines.append("Helly-2 slice property holds for all sorts.")
        else:
            lines.append("Helly-2 slice property fails.")
            for violation in self.violations:
                lines.append(
                    f"- Sort {violation.sort}: pairwise intersections are non-empty but the triple intersection is empty."
                )
                for idx, witness in enumerate(violation.slices, start=1):
                    members = ", ".join(witness.members) if witness.members else "∅"
                    lines.append(f"  Slice {idx}: {{{members}}}")
                    for origin in witness.origins:
                        lines.append(f"    from {origin}")
        lines.append(f"Computed closure: {self.closure_size} relations across {self.num_sorts} sorts.")
        return "\n".join(lines)

    def raise_for_status(self) -> None:
        if not self.ok:
            raise HellyCheckError("Helly-2 slice property does not hold")


def _wrap_label(label: str) -> str:
    if not label:
        return "(?)"
    if label.startswith("(") and label.endswith(")") and len(label) >= 2:
        return label
    return f"({label})"


def _display_label(label: str) -> str:
    return label or "(anonymous)"


@dataclass(frozen=True)
class _TypedRelation:
    source: str
    target: str
    pairs: frozenset[Pair]
    label: str = field(default="", compare=False)

    def converse(self) -> "_TypedRelation":
        flipped = frozenset((b, a) for (a, b) in self.pairs)
        return _TypedRelation(self.target, self.source, flipped, f"{_wrap_label(self.label)}ᵗ")

    def diagonal(self) -> Optional["_TypedRelation"]:
        if self.source != self.target:
            return None
        diag = frozenset((a, a) for (a, b) in self.pairs if a == b)
        return _TypedRelation(self.source, self.target, diag, f"{_wrap_label(self.label)}*")

    def intersection(self, other: "_TypedRelation") -> "_TypedRelation":
        if self.source != other.source or self.target != other.target:
            raise ValueError("intersection requires like-typed relations")
        inter = self.pairs & other.pairs
        new_label = f"{_wrap_label(self.label)}∩{_wrap_label(other.label)}"
        return _TypedRelation(self.source, self.target, inter, new_label)

    def compose(self, other: "_TypedRelation") -> "_TypedRelation":
        if self.target != other.source:
            raise ValueError("composition requires matching inner sorts")
        lookup: MutableMapping[str, list[str]] = {}
        for b, c in other.pairs:
            lookup.setdefault(b, []).append(c)
        composed = {(a, c) for (a, b) in self.pairs for c in lookup.get(b, ())}
        new_label = f"{_wrap_label(self.label)}⋅{_wrap_label(other.label)}"
        return _TypedRelation(self.source, other.target, frozenset(composed), new_label)


def check_helly(
    sorts: Mapping[str, Sequence[str]],
    relations: Iterable[Relation | Tuple[str, str, str, Iterable[Pair]]],
) -> HellyResult:
    _, _, _, result = _analyze(sorts, relations)
    return result


def _analyze(
    sorts: Mapping[str, Sequence[str]],
    relations: Iterable[Relation | Tuple[str, str, str, Iterable[Pair]]],
) -> Tuple[dict[str, Tuple[str, ...]], Tuple[_TypedRelation, ...], Tuple[_TypedRelation, ...], HellyResult]:
    carriers = _normalize_sorts(sorts)
    typed_relations = tuple(_normalize_relation(carriers, rel) for rel in relations)
    if not typed_relations:
        raise HellyCheckError("at least one relation is required")
    closure = _compute_closure(carriers, typed_relations)
    registry = _build_slice_registry(carriers, closure)
    violations = _find_violations(registry)
    result = HellyResult(
        ok=not violations,
        closure_size=len(closure),
        num_sorts=len(carriers),
        violations=violations,
    )
    return carriers, typed_relations, closure, result


def _normalize_sorts(sorts: Mapping[str, Sequence[str]]) -> dict[str, Tuple[str, ...]]:
    if not sorts:
        raise HellyCheckError("at least one sort is required")
    carriers: dict[str, Tuple[str, ...]] = {}
    for name, values in sorts.items():
        if not isinstance(name, str) or not name:
            raise HellyCheckError("sort names must be non-empty strings")
        if name in carriers:
            raise HellyCheckError(f"duplicate sort {name!r}")
        values_tuple = tuple(values)
        if not values_tuple:
            raise HellyCheckError(f"carrier for sort {name!r} must be non-empty")
        if len(set(values_tuple)) != len(values_tuple):
            raise HellyCheckError(f"carrier for sort {name!r} contains duplicates")
        carriers[name] = values_tuple
    return carriers


def _normalize_relation(
    carriers: Mapping[str, Tuple[str, ...]],
    rel: Relation | Tuple[str, str, str, Iterable[Pair]],
) -> _TypedRelation:
    if isinstance(rel, Relation):
        name, source, target, pairs_iter = rel.name, rel.source, rel.target, rel.pairs
    elif all(
        hasattr(rel, attr) for attr in ("name", "source", "target", "pairs")
    ):
        name = getattr(rel, "name")
        source = getattr(rel, "source")
        target = getattr(rel, "target")
        pairs_iter = getattr(rel, "pairs")
    else:
        try:
            name, source, target, pairs_iter = rel
        except Exception as exc:  # noqa: BLE001
            raise HellyCheckError("relations must provide name, source, target, pairs") from exc
    if source not in carriers:
        raise HellyCheckError(f"relation {name!r} references unknown source sort {source!r}")
    if target not in carriers:
        raise HellyCheckError(f"relation {name!r} references unknown target sort {target!r}")

    source_values = set(carriers[source])
    target_values = set(carriers[target])
    pairs: set[Pair] = set()
    for pair in pairs_iter:
        try:
            a, b = pair  # type: ignore[misc]
        except Exception as exc:  # noqa: BLE001
            raise HellyCheckError(
                f"relation {name!r} contains an element that is not a pair: {pair!r}"
            ) from exc
        if a not in source_values:
            raise HellyCheckError(f"value {a!r} in relation {name!r} not present in carrier V_{source}")
        if b not in target_values:
            raise HellyCheckError(f"value {b!r} in relation {name!r} not present in carrier V_{target}")
        pairs.add((a, b))

    return _TypedRelation(source, target, frozenset(pairs), name)


RelationKey = Tuple[str, str, frozenset[Pair]]


def _should_replace_label(old: str, new: str) -> bool:
    if not old:
        return bool(new)
    if not new:
        return False
    return len(new) < len(old)


def _compute_closure(
    carriers: Mapping[str, Tuple[str, ...]],
    relations: Sequence[_TypedRelation],
) -> Tuple[_TypedRelation, ...]:
    relation_map: dict[RelationKey, _TypedRelation] = {}
    queue: deque[RelationKey] = deque()
    by_type: dict[Tuple[str, str], set[RelationKey]] = {}
    by_source: dict[str, set[RelationKey]] = {}
    by_target: dict[str, set[RelationKey]] = {}

    def add(rel: _TypedRelation) -> None:
        key: RelationKey = (rel.source, rel.target, rel.pairs)
        bucket_type = by_type.setdefault((rel.source, rel.target), set())
        bucket_source = by_source.setdefault(rel.source, set())
        bucket_target = by_target.setdefault(rel.target, set())
        existing = relation_map.get(key)
        if existing is not None and not _should_replace_label(existing.label, rel.label):
            return
        relation_map[key] = rel
        bucket_type.add(key)
        bucket_source.add(key)
        bucket_target.add(key)
        queue.append(key)

    for rel in relations:
        add(rel)

    while queue:
        key = queue.popleft()
        rel = relation_map.get(key)
        if rel is None:
            continue

        add(rel.converse())
        diag = rel.diagonal()
        if diag is not None:
            add(diag)

        for other_key in list(by_type.get((rel.source, rel.target), ())):
            if other_key == key:
                continue
            other = relation_map.get(other_key)
            if other is None:
                continue
            add(rel.intersection(other))

        for right_key in list(by_source.get(rel.target, ())):
            other = relation_map.get(right_key)
            if other is None:
                continue
            add(rel.compose(other))

        for left_key in list(by_target.get(rel.source, ())):
            other = relation_map.get(left_key)
            if other is None:
                continue
            add(other.compose(rel))

    return tuple(relation_map.values())


class _SliceRegistry:
    def __init__(self, carriers: Mapping[str, Tuple[str, ...]]):
        self._data: dict[str, dict[frozenset[str], SliceWitness]] = {
            sort: {} for sort in carriers
        }

    def add(self, sort: str, members: frozenset[str], origin: str) -> None:
        bucket = self._data.setdefault(sort, {})
        witness = bucket.get(members)
        if witness is None:
            bucket[members] = SliceWitness(tuple(sorted(members)), (origin,))
        else:
            bucket[members] = SliceWitness(
                witness.members,
                witness.origins + (origin,),
            )

    def slices(self, sort: str) -> Tuple[SliceWitness, ...]:
        return tuple(self._data.get(sort, {}).values())

    def sorts(self) -> Tuple[str, ...]:
        return tuple(self._data.keys())


def _build_slice_registry(
    carriers: Mapping[str, Tuple[str, ...]],
    relations: Sequence[_TypedRelation],
) -> _SliceRegistry:
    registry = _SliceRegistry(carriers)
    for rel in relations:
        target_carrier = carriers[rel.target]
        grouped: dict[str, list[str]] = {value: [] for value in target_carrier}
        for a, b in rel.pairs:
            grouped.setdefault(b, []).append(a)
        for b in target_carrier:
            members = frozenset(grouped.get(b, []))
            origin = f"{rel.label}[_, {b}] : {rel.source}→{rel.target}"
            registry.add(rel.source, members, origin)
    return registry


def _find_violations(registry: _SliceRegistry) -> Tuple[HellyViolation, ...]:
    violations: list[HellyViolation] = []
    for sort in registry.sorts():
        slices = registry.slices(sort)
        if len(slices) < 3:
            continue
        found = False
        for i in range(len(slices) - 2):
            for j in range(i + 1, len(slices) - 1):
                for k in range(j + 1, len(slices)):
                    trio = (slices[i], slices[j], slices[k])
                    sets = [set(w.members) for w in trio]
                    if not (sets[0] & sets[1] and sets[1] & sets[2] and sets[2] & sets[0]):
                        continue
                    if sets[0] & sets[1] & sets[2]:
                        continue
                    violations.append(
                        HellyViolation(sort, (trio[0], trio[1], trio[2]))
                    )
                    found = True
                    break
                else:
                    continue
                break
            if found:
                break
        # continue scanning remaining sorts
    return tuple(violations)


def create_helly_report(
    path: Union[str, Path],
    sorts: Mapping[str, Sequence[str]],
    relations: Iterable[Relation | Tuple[str, str, str, Iterable[Pair]]],
    *,
    title: str = "Helly-2 Report",
) -> HellyResult:
    carriers, typed_inputs, closure, result = _analyze(sorts, relations)
    html = _render_report(title, carriers, typed_inputs, closure, result)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(html, encoding="utf-8")
    return result


def _sorted_pairs(pairs: Iterable[Pair]) -> Tuple[Pair, ...]:
    return tuple(sorted(pairs, key=lambda p: (p[0], p[1])))


def _render_pairs_html(pairs: Iterable[Pair]) -> str:
    formatted = ", ".join(
        f"({escape(a)}, {escape(b)})" for a, b in _sorted_pairs(pairs)
    )
    return formatted or "∅"


def _render_report(
    title: str,
    carriers: Mapping[str, Sequence[str]],
    inputs: Sequence[_TypedRelation],
    closure: Sequence[_TypedRelation],
    result: HellyResult,
) -> str:
    def section(header: str, body: str) -> str:
        return f"<section><h2>{escape(header)}</h2>{body}</section>"

    status_text = (
        "Helly-2 slice property holds for all sorts."
        if result.ok
        else "Helly-2 slice property fails."
    )
    summary_lines = [
        f"<p>{escape(status_text)}</p>",
        f"<p>Closure size: {result.closure_size} relation{'s' if result.closure_size != 1 else ''} across {result.num_sorts} sort{'s' if result.num_sorts != 1 else ''}.</p>",
    ]

    if not result.ok:
        for violation in result.violations:
            rows = []
            for idx, witness in enumerate(violation.slices, start=1):
                members = ", ".join(escape(m) for m in witness.members) or "∅"
                origins = "<br>".join(escape(origin) for origin in witness.origins)
                rows.append(
                    f"<tr><td>{idx}</td><td>{members}</td><td>{origins}</td></tr>"
                )
            summary_lines.append(
                "<div class='violation'>"
                f"<h3>Counterexample for sort {escape(violation.sort)}</h3>"
                "<p>The following slices intersect pairwise but have empty triple intersection.</p>"
                "<table><thead><tr><th>#</th><th>Members</th><th>Origins</th></tr></thead>"
                f"<tbody>{''.join(rows)}</tbody></table>"
                "</div>"
            )

    summary_section = section("Summary", "".join(summary_lines))

    sort_rows = "".join(
        f"<tr><td>{escape(sort)}</td><td>{', '.join(escape(v) for v in values)}</td></tr>"
        for sort, values in sorted(carriers.items(), key=lambda item: item[0])
    )
    sorts_section = section(
        "Sorts",
        "<table><thead><tr><th>Sort</th><th>Elements</th></tr></thead>"
        f"<tbody>{sort_rows}</tbody></table>",
    )

    input_rows = "".join(
        "<tr>"
        f"<td>{escape(_display_label(rel.label))}</td>"
        f"<td>{escape(rel.source)}</td>"
        f"<td>{escape(rel.target)}</td>"
        f"<td>{_render_pairs_html(rel.pairs)}</td>"
        "</tr>"
        for rel in sorted(inputs, key=lambda r: (r.source, r.target, _display_label(r.label)))
    )
    inputs_section = section(
        "Input Relations",
        "<table><thead><tr><th>Name</th><th>Source</th><th>Target</th><th>Pairs</th></tr></thead>"
        f"<tbody>{input_rows}</tbody></table>",
    )

    closure_rows = "".join(
        "<tr>"
        f"<td>{escape(_display_label(rel.label))}</td>"
        f"<td>{escape(rel.source)}</td>"
        f"<td>{escape(rel.target)}</td>"
        f"<td>{_render_pairs_html(rel.pairs)}</td>"
        "</tr>"
        for rel in sorted(closure, key=lambda r: (r.source, r.target, _display_label(r.label)))
    )
    closure_section = section(
        "Closure Relations",
        "<table><thead><tr><th>Label</th><th>Source</th><th>Target</th><th>Pairs</th></tr></thead>"
        f"<tbody>{closure_rows}</tbody></table>",
    )

    style = """
    body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; margin: 2em; }
    h1 { margin-bottom: 0.5em; }
    section { margin-bottom: 2em; }
    table { border-collapse: collapse; width: 100%; margin-top: 0.5em; }
    th, td { border: 1px solid #ccc; padding: 0.4em 0.6em; text-align: left; vertical-align: top; }
    th { background-color: #f5f5f5; }
    .violation { border: 1px solid #f2a; padding: 0.75em; background: #fff5fb; margin-top: 1em; }
    """

    html = (
        "<!DOCTYPE html>"
        "<html lang='en'>"
        "<head>"
        "<meta charset='utf-8'/>"
        f"<title>{escape(title)}</title>"
        f"<style>{style}</style>"
        "</head>"
        "<body>"
        f"<h1>{escape(title)}</h1>"
        f"{summary_section}"
        f"{sorts_section}"
        f"{inputs_section}"
        f"{closure_section}"
        "</body>"
        "</html>"
    )
    return html


def _load_module_family(module_name: str) -> Tuple[Mapping[str, Sequence[str]], Iterable]:
    module = importlib.import_module(module_name)
    if hasattr(module, "build"):
        data = module.build()  # type: ignore[attr-defined]
        if isinstance(data, tuple) and len(data) == 2:
            return data  # type: ignore[return-value]
        raise HellyCheckError("build() must return (sorts, relations)")
    sorts = getattr(module, "sorts", None)
    relations = getattr(module, "relations", None)
    if sorts is None or relations is None:
        raise HellyCheckError(
            f"module {module_name!r} must define `sorts` and `relations`, or a build() function"
        )
    return sorts, relations


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the Helly-2 slice property for a relation family module."
    )
    parser.add_argument("module", nargs="?", help="Import path exposing `sorts` and `relations`.")
    parser.add_argument(
        "--report",
        help="Write an HTML report to the given path.",
    )
    args = parser.parse_args(argv)

    if not args.module:
        parser.print_help()
        return 0

    try:
        sorts, relations = _load_module_family(args.module)
        if args.report:
            result = create_helly_report(
                args.report,
                sorts,
                relations,
                title=f"Helly-2 Report — {args.module}",
            )
        else:
            result = check_helly(sorts, relations)
    except (HellyCheckError, ModuleNotFoundError) as exc:
        print(f"Error: {exc}", flush=True)
        return 2

    print(result.to_text(), flush=True)
    if args.report:
        print(f"Report written to {args.report}", flush=True)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
