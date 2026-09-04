#!/usr/bin/env python3
"""The survivors worth offering to Mathlib, one at a time.

Mathlib generalises when a use appears, deliberately. A batch of several hundred
unsolicited generalisation pull requests would be unwelcome and would deserve to
be. So this narrows to a shortlist a person can carry individually, each with
the compile evidence attached.

Four filters, in decreasing order of how much they prove:

`magnitude >= 3`. Below that the weakening is one or two steps and the change is
cosmetic; half of all survivors sit at one step.

Not auxiliary. A name ending `_aux` is scaffolding for the lemma after it, and
its conclusion often barely involves the weakened structure -- two of the
deepest survivors conclude an inequality in the reals whose ring hypothesis
exists only to state another hypothesis. Deep by the ordinal, empty as
mathematics.

Signature known. If Lean would not print the theorem's type for us, we cannot
show a maintainer what the statement says, and a pull request that cannot state
its own claim should not be opened.

Ranked, not chosen. This produces an ordering and a count. Which ones are worth
a maintainer's attention is a judgement no filter here can make, and the reading
still has to be done by a person.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from catalogue import survivors, area_of, full_name, INVERTIBLE, PLAIN
from triage import magnitude, UNRANKED


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stores", default="scrutiny/*.db")
    parser.add_argument("--signatures", type=Path,
                        default=Path("scrutiny/signatures.json"))
    parser.add_argument("--floor", type=int, default=3,
                        help="minimum magnitude (default 3)")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    known = json.loads(args.signatures.read_text(encoding="utf-8")) \
        if args.signatures.exists() else {}

    picked = []
    for row in survivors(args.stores):
        target = row["floor"] or row["to_class"]
        depth = magnitude(row["from_class"], target)
        if depth == UNRANKED or depth < args.floor:
            continue
        name = full_name(row)
        if row["theorem"].endswith("_aux") or ".aux" in name:
            continue
        signature = known.get(name, "")
        if not signature:
            continue
        picked.append({
            "magnitude": depth,
            "area": area_of(row["module"]),
            "theorem": name,
            "module": row["module"],
            "stated": row["from_class"],
            "holds_over": target,
            "loses_invertibility":
                row["from_class"] in INVERTIBLE and target in PLAIN,
            "signature": " ".join(signature.split()),
        })
    picked.sort(key=lambda item: (-item["magnitude"], item["area"], item["theorem"]))

    print(f"  {len(picked)} candidates at magnitude >= {args.floor}\n")
    for area, count in collections.Counter(p["area"] for p in picked).most_common():
        print(f"    {area:<20} {count}")
    print("\n  Offer them individually. A batch is a different thing to receive "
          "than\n  a suggestion, and Mathlib generalises reactively on purpose.")

    if args.out:
        args.out.write_text(
            "\n".join(json.dumps(p, ensure_ascii=False) for p in picked) + "\n",
            encoding="utf-8")
        print(f"\n  written to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
