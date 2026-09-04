#!/usr/bin/env python3
"""Find how far down a weakening actually goes, rather than where our table stopped.

The sweep reports the edge it was given, not the edge the proof needs. Its
headline survivor came back as `Field -> CommRing` because `CommRing` is what the
weakening table contains; the proof in fact holds over a `Semiring`, three steps
further down. That gap is a whole failure mode -- a result that is correct and
not sharp -- and it is invisible to every filter in the pipeline, because
everything else asks whether a compilation succeeded and this asks whether a
different one would have succeeded too.

Descent settles it without any judgement. Take a survivor, substitute each
candidate class in turn, compile, and report the weakest that holds. A class is
tried whether or not the hierarchy makes it comparable to the others: the
compiler decides, and incomparable classes simply both appear or both fail.

The cost is one compilation per candidate per survivor, which is small because
survivors are few. It is the cheapest sharpening available and the pipeline
should have done it from the start.
"""

from __future__ import annotations

import argparse
import json
import re
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from leanrun import (run_bounded, wait_for_memory, opened, errors_in,
                        HEADER, AXIOMS_RE)
from triage import STRENGTH, FAMILY, reaches_conclusion, actually_weakened

# Every class worth trying beneath a given family. Ordered strongest first only
# for legibility; all of them are attempted, since the hierarchy is a lattice
# rather than a chain and "weakest that compiles" is decided afterwards.
FLOORS: dict[str, list[str]] = {
    "mul": ["Field", "DivisionRing", "CommRing", "Ring", "CommSemiring", "Semiring",
            "NonUnitalRing", "NonUnitalSemiring", "CommMonoidWithZero",
            "MonoidWithZero", "MulZeroClass", "NonUnitalNonAssocSemiring"],
    "group": ["CommGroup", "Group", "CommMonoid", "Monoid", "CommSemigroup",
              "Semigroup", "MulOneClass"],
    "add": ["AddCommGroup", "AddGroup", "AddCommMonoid", "AddMonoid",
            "AddCommSemigroup", "AddSemigroup", "AddZeroClass"],
    "order": ["LinearOrder", "Lattice", "PartialOrder", "Preorder"],
    "finite": ["Fintype", "Finite"],
    "topology": ["MetricSpace", "PseudoMetricSpace"],
}


def compiles_at(repo: Path, row: dict, target: str, timeout: int) -> bool:
    argument = row["binder"].strip("[]").split()[-1]
    current = row["to_class"]
    pattern = rf"\[\s*{re.escape(current)}\s+{re.escape(argument)}\s*\]"
    source, count = re.subn(pattern, f"[{target} {argument}]", row["source"])
    if count != 1:
        return False
    directives = "\n".join(dict.fromkeys(
        line for line in (row.get("opens") or "").splitlines() if line.strip()))
    name = f"w{row['id']}"
    text = (HEADER + "\n"
            + (directives + "\n\n" if directives else "")
            + opened(row) + source + f"\n\n#print axioms {name}\n")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        out, err = run_bounded(["lake", "env", "lean", str(path)], repo, timeout)
    except (OSError, subprocess.TimeoutExpired):
        return False
    finally:
        path.unlink(missing_ok=True)
    report = out + err
    if errors_in(report):
        return False
    match = AXIOMS_RE.search(report)
    return bool(match) and "sorryAx" not in (match.group(2) or "")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()

    connection = sqlite3.connect(args.db)
    connection.row_factory = sqlite3.Row
    columns = {c[1] for c in connection.execute("PRAGMA table_info(weakening)")}
    if "floor" not in columns:
        connection.execute("ALTER TABLE weakening ADD COLUMN floor TEXT")
        connection.commit()

    rows = [dict(r) for r in connection.execute(
        "SELECT * FROM weakening WHERE subsumed = 'new' AND floor IS NULL")]
    rows = [r for r in rows if reaches_conclusion(r) and actually_weakened(r)]
    print(json.dumps({"survivors": len(rows)}), flush=True)

    for index, row in enumerate(rows, start=1):
        family = FAMILY.get(row["to_class"])
        candidates = [c for c in FLOORS.get(family, [])
                      if STRENGTH.get(c, 99) < STRENGTH.get(row["to_class"], 0)]
        held: list[str] = []
        for target in candidates:
            wait_for_memory()
            if compiles_at(args.repo, row, target, args.timeout):
                held.append(target)
        floor = min(held, key=lambda c: STRENGTH.get(c, 99)) if held else row["to_class"]
        connection.execute("UPDATE weakening SET floor = ? WHERE id = ?",
                           (floor, row["id"]))
        connection.commit()
        moved = floor != row["to_class"]
        print(json.dumps({
            "at": index, "of": len(rows), "theorem": row["theorem"],
            "reported": row["to_class"], "floor": floor,
            "sharpened": moved, "also_held": held}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
