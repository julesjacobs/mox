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
    "Predicate",
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
class Predicate:
    """Named unary predicate on a sort."""

    name: str
    sort: str
    members: Sequence[str]


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
    # if label.startswith("(") and label.endswith(")") and len(label) >= 2:
        # return label
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
        new_label = f"{self.label}∩{other.label}"
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
    predicates: Optional[Iterable[Predicate]] = None,
) -> HellyResult:
    *_, result = _analyze(sorts, relations, predicates)
    return result


def _analyze(
    sorts: Mapping[str, Sequence[str]],
    relations: Iterable[Relation | Tuple[str, str, str, Iterable[Pair]]],
    predicates: Optional[Iterable[Predicate]] = None,
) -> Tuple[
    dict[str, Tuple[str, ...]],
    Tuple[_TypedRelation, ...],
    Tuple[_TypedRelation, ...],
    Tuple[_TypedRelation, ...],
    Tuple[_TypedRelation, ...],
    "_SliceRegistry",
    HellyResult,
]:
    carriers = _normalize_sorts(sorts)
    typed_relations = tuple(_normalize_relation(carriers, rel) for rel in relations)
    if not typed_relations:
        raise HellyCheckError("at least one relation is required")
    predicates = tuple(predicates or ())
    typed_predicates = tuple(_normalize_predicate(carriers, pred) for pred in predicates)
    initial = typed_relations + typed_predicates
    closure = _compute_closure(carriers, initial)
    registry = _build_slice_registry(carriers, closure)
    violations = _find_violations(registry)
    relation_keys = {(rel.source, rel.target, rel.pairs) for rel in typed_relations}
    predicate_keys = {(rel.source, rel.target, rel.pairs) for rel in typed_predicates}
    closure_relations = tuple(
        rel
        for rel in closure
        if not _is_predicate(rel) and (rel.source, rel.target, rel.pairs) not in relation_keys
    )
    closure_predicates = tuple(
        rel
        for rel in closure
        if _is_predicate(rel) and (rel.source, rel.target, rel.pairs) not in predicate_keys
    )
    result = HellyResult(
        ok=not violations,
        closure_size=len(closure),
        num_sorts=len(carriers),
        violations=violations,
    )
    return (
        carriers,
        typed_relations,
        typed_predicates,
        closure_relations,
        closure_predicates,
        registry,
        result,
    )


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


def _normalize_predicate(
    carriers: Mapping[str, Tuple[str, ...]],
    predicate: Predicate,
) -> _TypedRelation:
    sort = predicate.sort
    if sort not in carriers:
        raise HellyCheckError(f"predicate {predicate.name!r} references unknown sort {sort!r}")
    carrier_values = set(carriers[sort])
    members: set[Pair] = set()
    for value in predicate.members:
        if value not in carrier_values:
            raise HellyCheckError(
                f"value {value!r} in predicate {predicate.name!r} not present in carrier V_{sort}"
            )
        members.add((value, value))
    return _TypedRelation(sort, sort, frozenset(members), predicate.name)


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


def _is_predicate(rel: _TypedRelation) -> bool:
    if rel.source != rel.target:
        return False
    return all(a == b for a, b in rel.pairs)


def _is_outer_product(rel: _TypedRelation) -> bool:
    if not rel.pairs:
        return True
    rows = {a for (a, _) in rel.pairs}
    cols = {b for (_, b) in rel.pairs}
    product = {(a, b) for a in rows for b in cols}
    return rel.pairs == product


def create_helly_report(
    path: Union[str, Path],
    sorts: Mapping[str, Sequence[str]],
    relations: Iterable[Relation | Tuple[str, str, str, Iterable[Pair]]],
    predicates: Optional[Iterable[Predicate]] = None,
    *,
    title: str = "Helly-2 Report",
    include_outer_products: bool = False,
) -> HellyResult:
    (
        carriers,
        input_relations,
        input_predicates,
        closure_relations,
        closure_predicates,
        registry,
        result,
    ) = _analyze(sorts, relations, predicates)
    html = _render_report(
        title,
        carriers,
        input_relations,
        input_predicates,
        closure_relations,
        closure_predicates,
        registry,
        result,
        hide_outer_products=not include_outer_products,
    )
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


def _relation_matrix_html(
    rel: _TypedRelation,
    carriers: Mapping[str, Sequence[str]],
    *,
    is_transpose: bool = False,
    is_restricted: bool = False,
    element_id: Optional[str] = None,
    parent_id: Optional[str] = None,
    is_outer_product: bool = False,
) -> str:
    rows = carriers[rel.source]
    cols = carriers[rel.target]
    body_rows = []
    pair_set = rel.pairs
    for row in rows:
        cells = []
        for col in cols:
            present = (row, col) in pair_set
            css_class = "present" if present else "absent"
            symbol = "•" if present else ""
            cells.append(f"<td class='{css_class}'>{symbol}</td>")
        body_rows.append(
            "<tr>"
            f"<th>{escape(row)}</th>"
            f"{''.join(cells)}"
            "</tr>"
        )
    header_cells = "".join(f"<th>{escape(col)}</th>" for col in cols)
    classes = ["relation-grid"]
    if is_transpose:
        classes.append("transpose")
    if is_restricted:
        classes.append("restricted")
    if is_outer_product:
        classes.append("outer-product")

    attributes = [f"class=\"{' '.join(classes)}\""]
    if element_id:
        attributes.append(f"id=\"{element_id}\"")
    if parent_id:
        attributes.append(f"data-parent=\"{parent_id}\"")
    if is_outer_product:
        attributes.append("data-outer-product=\"true\"")
    attributes.append(f"title=\"{escape(_display_label(rel.label))}\"")

    return (
        f"<table {' '.join(attributes)}>"
        f"<thead><tr><th></th>{header_cells}</tr></thead>"
        f"<tbody>{''.join(body_rows)}</tbody>"
        "</table>"
    )


def _predicate_table_html(
    rel: _TypedRelation,
    carriers: Mapping[str, Sequence[str]],
) -> str:
    values = carriers[rel.source]
    members = {a for a, b in rel.pairs if a == b}
    return (
        f"<table class='predicate-list' title=\"{escape(_display_label(rel.label))}\">"
        "<tbody>"
        + "".join(
            f"<tr><td class='{'present' if value in members else 'absent'}'>{escape(value)}</td></tr>"
            for value in values
        )
        + "</tbody>"
        "</table>"
    )


def _render_report(
    title: str,
    carriers: Mapping[str, Sequence[str]],
    inputs: Sequence[_TypedRelation],
    input_predicates: Sequence[_TypedRelation],
    closure_relations: Sequence[_TypedRelation],
    closure_predicates: Sequence[_TypedRelation],
    registry: "_SliceRegistry",
    result: HellyResult,
    *,
    hide_outer_products: bool = True,
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

    sort_rows = "".join(
        f"<tr><td>{escape(sort)}</td><td>{', '.join(escape(v) for v in values)}</td></tr>"
        for sort, values in sorted(carriers.items(), key=lambda item: item[0])
    )
    sorts_section = section(
        "Sorts",
        "<table><thead><tr><th>Sort</th><th>Elements</th></tr></thead>"
        f"<tbody>{sort_rows}</tbody></table>",
    )

    carrier_sets = {sort: set(values) for sort, values in carriers.items()}

    predicate_lookup: dict[str, dict[frozenset[str], str]] = {}
    for pred in (*input_predicates, *closure_predicates):
        members = frozenset(a for (a, b) in pred.pairs if a == b)
        if not members:
            continue
        entry = predicate_lookup.setdefault(pred.source, {})
        label = _display_label(pred.label)
        existing = entry.get(members)
        if existing is None or len(label) < len(existing):
            entry[members] = label

    def describe_predicate_restriction(
        rel: _TypedRelation,
        previous: Sequence[Tuple[RelationKey, _TypedRelation, str]],
    ) -> Optional[Tuple[str, str]]:
        row_set = {a for (a, _) in rel.pairs}
        col_set = {b for (_, b) in rel.pairs}

        source_full = row_set == carrier_sets[rel.source]
        target_full = col_set == carrier_sets[rel.target]

        row_label = None
        if not source_full:
            row_label = predicate_lookup.get(rel.source, {}).get(frozenset(row_set))
        col_label = None
        if not target_full:
            col_label = predicate_lookup.get(rel.target, {}).get(frozenset(col_set))

        if not row_label and not col_label:
            return None

        for _, base, base_id in previous:
            if base.source != rel.source or base.target != rel.target:
                continue
            restricted = {
                (a, b)
                for (a, b) in base.pairs
                if (row_label is None or a in row_set)
                and (col_label is None or b in col_set)
            }
            if restricted == rel.pairs:
                parts = []
                if row_label:
                    parts.append(f"{row_label} on source")
                if col_label:
                    parts.append(f"{col_label} on target")
                label_text = f"restricted from {_display_label(base.label)}"
                if parts:
                    label_text += f" ({'; '.join(parts)})"
                return label_text, base_id
        return None

    has_outer_products = False
    relation_entries: list[Tuple[RelationKey, _TypedRelation, str]] = []
    transpose_keys: set[RelationKey] = set()
    input_tables_bucket: list[Tuple[int, int, str]] = []
    idx_counter = 0
    for rel in sorted(inputs, key=lambda r: (r.source, r.target, _display_label(r.label))):
        is_outer = _is_outer_product(rel)
        if is_outer:
            has_outer_products = True
        key = (rel.source, rel.target, rel.pairs)
        transpose_key = (
            rel.target,
            rel.source,
            frozenset((b, a) for (a, b) in rel.pairs),
        )
        is_transpose = transpose_key in transpose_keys
        parent_id = describe_predicate_restriction(rel, relation_entries)
        element_id = f"rel-input-{len(relation_entries)}"
        relation_entries.append((key, rel, element_id))
        transpose_keys.add(key)
        table_html = _relation_matrix_html(
            rel,
            carriers,
            is_transpose=is_transpose,
            is_restricted=parent_id is not None,
            element_id=element_id,
            parent_id=parent_id,
            is_outer_product=is_outer,
        )
        weight = 0
        if is_transpose:
            weight = max(weight, 1)
        if parent_id is not None:
            weight = max(weight, 2)
        if is_outer:
            weight = max(weight, 3)
        input_tables_bucket.append((weight, idx_counter, table_html))
        idx_counter += 1
    input_grids: list[str] = []
    if input_tables_bucket:
        ordered_tables = [
            html for _, _, html in sorted(input_tables_bucket, key=lambda item: (item[0], item[1]))
        ]
        input_grids.append(f"<div class='grid'>{''.join(ordered_tables)}</div>")
    inputs_section = section(
        "Input Relations",
        "".join(input_grids) if input_grids else "<p>(none)</p>",
    )

    input_pred_tables = [
        _predicate_table_html(rel, carriers)
        for rel in sorted(input_predicates, key=lambda r: (r.source, _display_label(r.label)))
    ]
    predicate_section = section(
        "Input Predicates",
        f"<div class='predicate-grid'>{''.join(input_pred_tables)}</div>" if input_pred_tables else "<p>(none)</p>",
    )

    closure_tables_bucket: list[Tuple[int, int, str]] = []
    closure_entries = relation_entries.copy()
    closure_transpose = transpose_keys.copy()
    closure_idx = 0
    for rel in sorted(closure_relations, key=lambda r: (r.source, r.target, _display_label(r.label))):
        is_outer = _is_outer_product(rel)
        if is_outer:
            has_outer_products = True
        key = (rel.source, rel.target, rel.pairs)
        transpose_key = (
            rel.target,
            rel.source,
            frozenset((b, a) for (a, b) in rel.pairs),
        )
        is_transpose = transpose_key in closure_transpose
        parent_id = describe_predicate_restriction(rel, closure_entries)
        element_id = f"rel-closure-{len(closure_entries)}"
        closure_entries.append((key, rel, element_id))
        closure_transpose.add(key)
        table_html = _relation_matrix_html(
            rel,
            carriers,
            is_transpose=is_transpose,
            is_restricted=parent_id is not None,
            element_id=element_id,
            parent_id=parent_id,
            is_outer_product=is_outer,
        )
        weight = 0
        if is_transpose:
            weight = max(weight, 1)
        if parent_id is not None:
            weight = max(weight, 2)
        if is_outer:
            weight = max(weight, 3)
        closure_tables_bucket.append((weight, closure_idx, table_html))
        closure_idx += 1
    closure_grids: list[str] = []
    if closure_tables_bucket:
        ordered_tables = [
            html for _, _, html in sorted(closure_tables_bucket, key=lambda item: (item[0], item[1]))
        ]
        closure_grids.append(f"<div class='grid'>{''.join(ordered_tables)}</div>")
    closure_section = section(
        "Closure Relations",
        "".join(closure_grids) if closure_grids else "<p>(none)</p>",
    )

    closure_pred_tables = [
        _predicate_table_html(rel, carriers)
        for rel in sorted(closure_predicates, key=lambda r: (r.source, _display_label(r.label)))
    ]
    closure_pred_section = section(
        "Closure Predicates",
        f"<div class='predicate-grid'>{''.join(closure_pred_tables)}</div>" if closure_pred_tables else "<p>(none)</p>",
    )

    slice_sections = []
    for sort in sorted(registry.sorts()):
        slices = sorted(
            registry.slices(sort),
            key=lambda w: (len(w.members), w.members),
        )
        slice_rows = "".join(
            "<tr>"
            f"<td>{idx}</td>"
            f"<td>{', '.join(escape(m) for m in witness.members) or '∅'}</td>"
            f"<td>{'<br>'.join(escape(origin) for origin in witness.origins)}</td>"
            "</tr>"
            for idx, witness in enumerate(slices, start=1)
        )
        rows_html = slice_rows or '<tr><td colspan="3">(no slices)</td></tr>'
        slice_sections.append(
            f"<section class='slices'><h3>{escape(sort)}</h3>"
            "<table><thead><tr><th>#</th><th>Members</th><th>Origins</th></tr></thead>"
            f"<tbody>{rows_html}</tbody></table>"
            "</section>"
        )
    slices_section = section(
        "Slices by Sort",
        "".join(slice_sections),
    )

    if has_outer_products:
        checked_attr = "" if hide_outer_products else " checked"
        summary_lines.append(
            "<div class='controls'>"
            f"<label><input type='checkbox' id='outer-product-toggle'{checked_attr}> Show outer-product relations</label>"
            "</div>"
        )

    summary_section = section("Summary", "".join(summary_lines))

    style = """
    body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; margin: 1.5em; font-size: 0.5em; }
    h1 { margin-bottom: 0.6em; }
    section { margin-bottom: 1.5em; }
    table { border-collapse: collapse; margin-top: 0.5em; }
    th, td { border: 1px solid #ccc; padding: 0.4em 0.6em; text-align: left; vertical-align: top; }
    th { background-color: #f5f5f5; }
    .violation { border: 1px solid #f2a; padding: 0.75em; background: #fff5fb; margin-top: 1em; }
    .grid { display: flex; flex-wrap: wrap; gap: 1.2em; align-items: flex-start; }
    .predicate-grid { display: flex; flex-wrap: wrap; gap: 1.2em; align-items: flex-start; }
    .relation-grid { border-collapse: collapse; font-size: 0.9em; order: 0; }
    .relation-grid th, .relation-grid td { border: 1px solid #ccc; padding: 0.25em; text-align: center; width: 1.6em; height: 1.6em; }
    .relation-grid th:first-child { text-align: right; background: #f0f0f0; width: auto; padding-right: 0.3em; }
    .relation-grid th:not(:first-child) { background: #fafafa; writing-mode: vertical-rl; text-orientation: mixed; transform: rotate(180deg); transform-origin: center; white-space: nowrap; padding: 0.5em 0.2em 0.15em 0.1em; width: 1.6em; height: auto; vertical-align: bottom; text-align: left; }
    .relation-grid td.present { background: #d6f5d6; font-weight: 600; color: #135b13; }
    .relation-grid td.absent { background: #fbfbfb; color: #c7c7c7; }
    .relation-grid.outer-product { border: 1px dashed #bbb; opacity: 0.7; order: 3; }
    .relation-grid.transpose { opacity: 0.5; border: 1px dashed #88a; order: 1; }
    .relation-grid.restricted { opacity: 0.5; border: 1px dashed #88a; order: 2; }
    .relation-grid.highlight { outline: 2px solid #f0a500; }
    body.hide-outer-products .relation-grid.outer-product { display: none; }
    .predicate-list { border-collapse: collapse; font-size: 0.9em; display: inline-table; width: auto; }
    .predicate-list td { border: 1px solid #ccc; padding: 0.3em 0.6em; text-align: center; }
    .predicate-list td.present { background: #d6f5d6; font-weight: 600; color: #135b13; }
    .predicate-list td.absent { background: #fbfbfb; color: #c7c7c7; }
    .controls { margin-top: 1em; font-size: 1.1em; }
    .controls input[type='checkbox'] { margin-right: 0.35em; }
    """

    script = """
    <script>
    (function(){
      var body = document.body;
      var toggle = document.getElementById('outer-product-toggle');
      if (toggle) {
        var sync = function(){
          if (toggle.checked) {
            body.classList.remove('hide-outer-products');
          } else {
            body.classList.add('hide-outer-products');
          }
        };
        toggle.addEventListener('change', sync);
        sync();
      }
      var tables = document.querySelectorAll('table.relation-grid[data-parent]');
      tables.forEach(function(tbl){
        var parentId = tbl.getAttribute('data-parent');
        if (!parentId) return;
        var parent = document.getElementById(parentId);
        if (!parent) return;
        tbl.addEventListener('mouseenter', function(){ parent.classList.add('highlight'); });
        tbl.addEventListener('mouseleave', function(){ parent.classList.remove('highlight'); });
      });
    })();
    </script>
    """

    body_classes: list[str] = []
    if hide_outer_products:
        body_classes.append("hide-outer-products")
    body_attr = f" class=\"{' '.join(body_classes)}\"" if body_classes else ""

    html = (
        "<!DOCTYPE html>"
        "<html lang='en'>"
        "<head>"
        "<meta charset='utf-8'/>"
        f"<title>{escape(title)}</title>"
        f"<style>{style}</style>"
        "</head>"
        f"<body{body_attr}>"
        f"<h1>{escape(title)}</h1>"
        f"{summary_section}"
        f"{sorts_section}"
        f"{predicate_section}"
        f"{inputs_section}"
        f"{closure_pred_section}"
        f"{closure_section}"
        f"{slices_section}"
        f"{script}"
        "</body>"
        "</html>"
    )
    return html


def _load_module_family(module_name: str) -> Tuple[Mapping[str, Sequence[str]], Iterable, Optional[Iterable]]:
    module = importlib.import_module(module_name)
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
        raise HellyCheckError(
            f"module {module_name!r} must define `sorts` and `relations`, or a build() function"
        )
    return sorts, relations, predicates


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check the Helly-2 slice property for a relation family module."
    )
    parser.add_argument("module", nargs="?", help="Import path exposing `sorts` and `relations`.")
    parser.add_argument(
        "--report",
        help="Write an HTML report to the given path.",
    )
    parser.add_argument(
        "--include-outer-products",
        action="store_true",
        help="Show relations whose matrices are full outer products (normally hidden).",
    )
    args = parser.parse_args(argv)

    if not args.module:
        parser.print_help()
        return 0

    try:
        sorts, relations, predicates = _load_module_family(args.module)
        if args.report:
            result = create_helly_report(
                args.report,
                sorts,
                relations,
                predicates=predicates,
                title=f"Helly-2 Report — {args.module}",
                include_outer_products=args.include_outer_products,
            )
        else:
            result = check_helly(sorts, relations, predicates=predicates)
    except (HellyCheckError, ModuleNotFoundError) as exc:
        print(f"Error: {exc}", flush=True)
        return 2

    print(result.to_text(), flush=True)
    if args.report:
        print(f"Report written to {args.report}", flush=True)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
