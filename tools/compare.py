#!/usr/bin/env python3
"""Compare assumption slack between corpora, area against matched area.

Comparing a whole AI-authored library against a whole human-authored one invites
the obvious objection: they are not doing the same mathematics, so any
difference might be the subject rather than the authorship. Both corpora happen
to carry areas of the same name -- Algebra, RingTheory, Analysis, NumberTheory --
so the comparison can be made within each, and the objection loses its grip.

Rates are reported with a Wilson interval, because the per-area samples on the
smaller side are thin and a bare percentage invites reading noise as signal.
Where an interval spans the other corpus's estimate, that is said rather than
left for the reader to notice.
"""

from __future__ import annotations

import argparse
import collections
import json
import math
import sqlite3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from triage import reaches_conclusion, actually_weakened


def wilson(hits: int, total: int, z: float = 1.96) -> tuple[float, float]:
    """A proportion's interval that stays sane at small counts and zero hits."""
    if not total:
        return (0.0, 0.0)
    p = hits / total
    d = 1 + z * z / total
    centre = (p + z * z / (2 * total)) / d
    spread = z * math.sqrt(p * (1 - p) / total + z * z / (4 * total * total)) / d
    return (max(0.0, centre - spread), min(1.0, centre + spread))


def area_of(module: str) -> str:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 and parts[0] in ("Mathlib", "TauCeti") else parts[0]


def load(dbs: list[Path], sampled_only: bool) -> dict[str, list[dict]]:
    groups: dict[str, list[dict]] = collections.defaultdict(list)
    for db in dbs:
        if not db.exists():
            continue
        connection = sqlite3.connect(db)
        connection.row_factory = sqlite3.Row
        query = "SELECT * FROM weakening WHERE verdict IS NOT NULL"
        if sampled_only:
            query += " AND verdict != 'out_of_sample'"
        for row in connection.execute(query):
            item = dict(row)
            item.setdefault("subsumed", None)
            item.setdefault("floor", None)
            groups[area_of(item["module"])].append(item)
    return groups


def measure(rows: list[dict]) -> dict:
    total = len(rows)
    incoherent = sum(1 for r in rows if r["verdict"] == "incoherent")
    weakens = [r for r in rows if r["verdict"] == "weakens"]
    real = [r for r in weakens if reaches_conclusion(r) and actually_weakened(r)]
    return {"n": total, "incoherent": incoherent, "weakens": len(weakens),
            "real": len(real)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--human", type=Path, action="append", required=True)
    parser.add_argument("--machine", type=Path, action="append", required=True)
    args = parser.parse_args()

    human = load(args.human, sampled_only=False)
    machine = load(args.machine, sampled_only=True)
    shared = sorted(set(human) & set(machine), key=lambda a: -len(machine[a]))

    print(f"  areas in both corpora: {', '.join(shared) or 'none'}\n")
    header = (f"  {'area':<16} {'corpus':<8} {'n':>6} {'incoherent':>22} "
              f"{'weakens':>20} {'real':>6}")
    print(header)
    print("  " + "-" * (len(header) - 2))
    verdicts = []
    for area in shared:
        for label, rows in (("human", human[area]), ("machine", machine[area])):
            m = measure(rows)
            if not m["n"]:
                continue
            lo, hi = wilson(m["incoherent"], m["n"])
            wlo, whi = wilson(m["weakens"], m["n"])
            print(f"  {area if label == 'human' else '':<16} {label:<8} {m['n']:>6}"
                  f" {100*m['incoherent']/m['n']:>7.1f}% [{100*lo:>5.1f},{100*hi:>5.1f}]"
                  f" {100*m['weakens']/m['n']:>6.2f}% [{100*wlo:>4.2f},{100*whi:>4.2f}]"
                  f" {m['real']:>6}")
        h, mm = measure(human[area]), measure(machine[area])
        if h["n"] and mm["n"]:
            hlo, hhi = wilson(h["incoherent"], h["n"])
            mlo, mhi = wilson(mm["incoherent"], mm["n"])
            overlap = not (hhi < mlo or mhi < hlo)
            verdicts.append((area, overlap, mm["n"]))
        print()
    print("  incoherence, per area:")
    for area, overlap, n in verdicts:
        note = ("intervals overlap -- no difference established"
                if overlap else "intervals disjoint -- a real difference")
        thin = "  (machine sample thin)" if n < 200 else ""
        print(f"    {area:<18} {note}{thin}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
