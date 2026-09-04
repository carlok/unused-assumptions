#!/usr/bin/env python3
"""Derive the weakening table from Mathlib's own class declarations.

The hand-written table has 48 edges over 27 classes. It was written by reading
the algebraic hierarchy and typing out the edges that looked right, which is why
every count in the note is a lower bound by a factor nobody could estimate --
and why `CategoryTheory` has never been swept at all: the table does not contain
one categorical class.

`class X ... extends Y` says exactly what we need. X carries everything Y does
and more, so X -> Y is a weakening, and the library states it about itself.
There is no judgement here and no list to keep up to date.

Two restrictions, both from the sweep rather than from the mathematics:

Single-argument classes only. `Algebra R A` relates two types and the
substitution machinery replaces one binder over one variable, so a
multi-argument parent cannot be dropped in as a target. 374 of the 525 parent
edges survive this.

Parents that are themselves classes. `extends Div, Inv, Monoid` names operation
carriers as well as structures, and those are legitimate weakenings -- Best's
table is full of them, and they are precisely the edges a table of named
structures cannot reach -- but only when they are declared classes in their own
right, which is what the scan already records.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

# A class header runs from `class X` to whichever comes first: `where`, `:=`,
# or a blank line. It is NOT one line. Mathlib writes
#
#     class DivisionRing (K : Type*)
#       extends Ring K, DivInvMonoid K, Nontrivial K, ... where
#
# and a line-by-line scan sees `class DivisionRing` with no `extends` at all.
# That cost 89 classes and 171 edges, DivisionRing and LinearOrderedField among
# them, and left the derived table claiming those classes extend nothing.
CLASS_START = re.compile(r"^class\s+([A-Za-z_][\w'.]*)\b", re.M)
HEAD_END = re.compile(r"\bwhere\b|\n\n|^\s*\S+\s*:=", re.M)
EXTENDS = re.compile(r"\bextends\s+(.+)", re.S)
PARENT = re.compile(r"\s*(?:[\w'✝]+\s*:\s*)?([A-Za-z_][\w'.]*)")
# A binder group in the class head: `(R : Type*)`, `{n : ℕ}`, `[Ring R]`.
BINDER = re.compile(r"[({\[]\s*[\w'\s]+\s*:")


def scan(root: Path) -> tuple[dict[str, int], dict[str, set[str]]]:
    """Every `class` declaration in the library: how many arguments it takes,
    and what it extends. Read from source rather than from the environment,
    because the answer is a fact about the declaration."""
    arity: dict[str, int] = {}
    edges: dict[str, set[str]] = collections.defaultdict(set)
    for path in root.rglob("*.lean"):
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        for start in CLASS_START.finditer(text):
            name = start.group(1)
            rest = text[start.end():]
            stop = HEAD_END.search(rest)
            head = rest[: stop.start()] if stop else rest[:400]
            arity[name] = len(BINDER.findall(head.split(" extends ")[0])) or 1
            found = EXTENDS.search(head)
            if not found:
                continue
            for chunk in found.group(1).split(","):
                parent = PARENT.match(chunk)
                if parent and parent.group(1) != name:
                    edges[name].add(parent.group(1))
    return arity, edges


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    arity, edges = scan(args.mathlib / "Mathlib")
    single = {name for name, count in arity.items() if count <= 1}
    table: dict[str, list[str]] = {}
    for source, parents in edges.items():
        if source not in single:
            continue
        keep = sorted(p for p in parents if p in single)
        if keep:
            table[source] = keep

    args.out.write_text(json.dumps(table, indent=1, sort_keys=True), encoding="utf-8")
    print(json.dumps({
        "classes_declared": len(arity),
        "classes_with_parents": len(edges),
        "parent_edges": sum(len(v) for v in edges.values()),
        "single_argument_classes": len(single),
        "table_classes": len(table),
        "table_edges": sum(len(v) for v in table.values()),
        "written": str(args.out),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
