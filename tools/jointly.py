#!/usr/bin/env python3
"""Can a theorem's weakenings hold all at once?

Every survivor was verified alone. Where one theorem has several, the sweep
records `breadth` and moves on -- but breadth counts binders that weaken
*independently*, each with the others left at full strength. Whether they hold
together has never been asked, and it is not implied: two weakenings can fail
jointly where each succeeds alone, because a sibling instance may need one of
the two original classes to be stateable.

525 theorems have one weakening and nothing to ask. 41 have two or three, which
is 47 subsets to compile. That is small enough that this enumerates them
exhaustively rather than searching.

Worth saying why there is no cleverness here. Finding a maximal jointly-holding
set is the shape that minimal-unsatisfiable-subset algorithms exist for, and
they exist because enumeration is infeasible. Enumeration costs 47 compiles.
The expensive oracle keeps the search space small by construction, which is the
opposite of the situation those algorithms were built for.
"""

from __future__ import annotations

import argparse
import collections
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from catalogue import survivors, full_name
from leanrun import AXIOMS_RE, errors_in, run_bounded, wait_for_memory
from typeclass import compile_once


def weakened(row: dict) -> str:
    """The binder as the sweep rewrote it: same variable, weaker class."""
    original, floor = row["binder"], row["floor"] or row["to_class"]
    return original.replace(row["from_class"], floor, 1)


def combined(rows: list[dict]) -> str | None:
    """One source with every weakening in `rows` applied.

    Start from the first row's source, which already carries its own weakening
    and leaves the others at full strength, then rewrite each remaining binder
    in place. Returns None if a binder cannot be located, which would mean the
    reconstruction is not what we think it is -- better to skip than to compile
    something we cannot account for.
    """
    source = rows[0]["source"]
    for row in rows[1:]:
        if row["binder"] not in source:
            return None
        source = source.replace(row["binder"], weakened(row), 1)
    return source


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stores", default="scrutiny/*.db")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    grouped: dict[tuple, list[dict]] = collections.defaultdict(list)
    for row in survivors(args.stores):
        grouped[(row["module"], full_name(row))].append(row)
    many = {key: group for key, group in grouped.items() if len(group) > 1}
    if args.limit:
        many = dict(itertools.islice(many.items(), args.limit))

    print(json.dumps({"theorems_with_several": len(many),
                      "compiles": sum(2 ** len(g) - len(g) - 1
                                      for g in many.values())}), flush=True)

    results = []
    for (module, theorem), group in many.items():
        group.sort(key=lambda r: r["binder"])
        # Every subset of size >= 2. Singletons are already known to hold.
        for size in range(len(group), 1, -1):
            for subset in itertools.combinations(group, size):
                source = combined(list(subset))
                if source is None:
                    continue
                wait_for_memory()
                probe = dict(subset[0])
                probe["source"] = source
                verdict, detail = compile_once(args.repo, probe,
                                               probe["opens"] or "", args.timeout)
                held = verdict == "weakens"
                results.append({
                    "module": module, "theorem": theorem,
                    "binders": [r["binder"] for r in subset],
                    "to": [r["floor"] or r["to_class"] for r in subset],
                    "jointly": held, "verdict": verdict,
                })
                print(f"  {'HOLDS ' if held else 'FAILS '} {theorem[:44]:<44} "
                      f"{' + '.join(r['from_class'] for r in subset)}"
                      + ("" if held else f"  [{verdict}]"), flush=True)

    holds = sum(1 for r in results if r["jointly"])
    print(f"\n  {holds} of {len(results)} subsets hold jointly")
    if args.out:
        args.out.write_text(
            "\n".join(json.dumps(r, ensure_ascii=False) for r in results) + "\n",
            encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
