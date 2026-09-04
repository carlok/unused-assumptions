#!/usr/bin/env python3
"""Split the weakenings that compiled into the two buckets that matter.

A successful weakening is usually library value and nothing more: the same
proof, running in a weaker setting, saying nothing new. `cardPowDegree_anti_
archimedean` holds over `DivisionRing` rather than `Field`, and nobody is going
to instantiate a non-commutative `Fq` in class number theory.

The bucket worth a conjecture is narrower -- the theorem was never about the
structure it was stated over. Reporting one number for both would overstate the
result, and the overstatement would be invisible afterwards, so the split
happens here and mechanically.

Two signals, neither a judgement about mathematics:

`magnitude` how far down the weakening reaches. `Field -> DivisionRing` gives
            up commutativity and little else; `Field -> CommRing` gives up
            inverses, and a theorem about fields that holds over any
            commutative ring was not a theorem about fields. Measured as a
            drop in an ordinal within one hierarchy, and fixed at 4 for an
            edge that forgets an operation outright, since those ordinals are
            not comparable across hierarchies.
`breadth`   how many of a theorem's binders weaken at once. All of them
            weakening usually means the proof never touched any structure --
            a plumbing lemma, not a discovery.

The output is a ranked JSONL for whatever judges these. The ranking is a prior
on where to look, not a verdict; a reader overrules it and the reasons matter
before the outcome, as `prompts/DELIBERATION.md` requires.
"""

from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from typeclass import WEAKENINGS

# Ordinals within one hierarchy, not across. Ring and AddCommGroup are not
# comparable -- an edge between them forgets an operation rather than weakening
# one -- so those are scored separately below.
STRENGTH = {
    "LinearOrderedField": 11, "Field": 10, "NormedField": 10,
    "DivisionRing": 9, "EuclideanDomain": 9, "LinearOrderedRing": 9,
    "CommRing": 7, "NormedRing": 7, "LinearOrderedSemiring": 7, "OrderedRing": 7,
    "Ring": 6, "GroupWithZero": 6,
    "CommSemiring": 5, "IsDomain": 5, "NonUnitalNormedRing": 5,
    "Semiring": 4, "NonUnitalRing": 4, "CommMonoidWithZero": 4,
    "NonUnitalSemiring": 3, "MonoidWithZero": 3, "NoZeroDivisors": 2,
    "CommGroup": 7, "Group": 6, "CommMonoid": 5, "DivInvMonoid": 4,
    "Monoid": 4, "CommSemigroup": 3, "Semigroup": 2, "MulOneClass": 2,
    "AddCommGroup": 7, "AddGroup": 6, "AddCommMonoid": 5, "SubNegMonoid": 4,
    "AddMonoid": 4, "AddCommSemigroup": 3, "AddSemigroup": 2, "AddZeroClass": 2,
    "CompleteLattice": 7, "LinearOrder": 6, "Lattice": 5, "PartialOrder": 4,
    "Preorder": 3,
    "MetricSpace": 6, "PseudoMetricSpace": 5,
    "NormedAddCommGroup": 7, "SeminormedAddCommGroup": 6,
    "Fintype": 5, "Finite": 3,
    # Added once the derived table began proposing them as targets. Placed from
    # the library's own `extends`: NontriviallyNormedField extends NormedField,
    # so it sits one above; the bare carriers extend nothing and sit at the
    # bottom of their hierarchy.
    "NontriviallyNormedField": 11,
    "NonUnitalNonAssocRing": 3, "NonUnitalNonAssocSemiring": 2,
    "CommMagma": 1, "MulOne": 1, "Mul": 0, "One": 0,
    "AddCommMagma": 1, "AddZero": 1, "Add": 0, "Zero": 0,
    # The metric hierarchy, placed from `extends`: MetricSpace -> Pseudo -> Dist,
    # and the extended-valued mirror of it. Both chains are linear, so a depth
    # ordinal is exact here in a way it is not for `mul`.
    "EMetricSpace": 6, "PseudoEMetricSpace": 5, "EDist": 0, "Dist": 0,
    # Separation axioms. T3 extends RegularSpace and T0; the rest are roots and
    # are NOT comparable to each other, which is why they all sit at 1 -- a
    # weakening between two of them is a sideways move, not a descent.
    "T3Space": 2, "RegularSpace": 1, "T0Space": 1, "T1Space": 1,
    "T2Space": 1, "T25Space": 1,
    "SemilatticeInf": 5, "SemilatticeSup": 5,
    "StarMul": 2, "InvolutiveStar": 1, "Star": 0,
}

FAMILY = {
    "Field": "mul", "DivisionRing": "mul", "CommRing": "mul", "Ring": "mul",
    "CommSemiring": "mul", "Semiring": "mul", "NonUnitalRing": "mul",
    "NonUnitalSemiring": "mul", "MonoidWithZero": "mul", "CommMonoidWithZero": "mul",
    "GroupWithZero": "mul", "EuclideanDomain": "mul", "IsDomain": "mul",
    "NoZeroDivisors": "mul", "NormedField": "mul", "NormedRing": "mul",
    "NonUnitalNormedRing": "mul", "LinearOrderedField": "mul",
    "LinearOrderedRing": "mul", "LinearOrderedSemiring": "mul", "OrderedRing": "mul",
    "CommGroup": "group", "Group": "group", "CommMonoid": "group",
    "Monoid": "group", "Semigroup": "group", "MulOneClass": "group",
    "DivInvMonoid": "group", "CommSemigroup": "group",
    "AddCommGroup": "add", "AddGroup": "add", "AddCommMonoid": "add",
    "AddMonoid": "add", "AddSemigroup": "add", "AddZeroClass": "add",
    "SubNegMonoid": "add", "AddCommSemigroup": "add",
    "NormedAddCommGroup": "add", "SeminormedAddCommGroup": "add",
    "LinearOrder": "order", "PartialOrder": "order", "Preorder": "order",
    "Lattice": "order", "CompleteLattice": "order",
    "MetricSpace": "topology", "PseudoMetricSpace": "topology",
    "Fintype": "finite", "Finite": "finite",
    "NontriviallyNormedField": "mul",
    "NonUnitalNonAssocRing": "mul", "NonUnitalNonAssocSemiring": "mul",
    "CommMagma": "group", "MulOne": "group", "Mul": "group", "One": "group",
    "AddCommMagma": "add", "AddZero": "add", "Add": "add", "Zero": "add",
    "EMetricSpace": "topology", "PseudoEMetricSpace": "topology",
    "EDist": "topology", "Dist": "topology",
    "T3Space": "separation", "RegularSpace": "separation", "T0Space": "separation",
    "T1Space": "separation", "T2Space": "separation", "T25Space": "separation",
    "SemilatticeInf": "order", "SemilatticeSup": "order",
    "StarMul": "star", "InvolutiveStar": "star", "Star": "star",
}

# A pair one of whose classes the tables do not list cannot be ranked. Saying so
# is the honest answer; scoring it FORGETS_AN_OPERATION is a guess wearing a
# measurement's clothes, and it made 40 of 64 survivors look deep.
UNRANKED = -1

FORGETS_AN_OPERATION = 4


def magnitude(from_class: str, to_class: str) -> int:
    """How much structure the weakening gives up, or UNRANKED.

    Different hierarchies means an operation is forgotten outright, the top of
    the scale. But a class the tables have never heard of has no hierarchy, and
    treating "unknown" as "different" gives every unlisted target maximum depth.
    That is how 40 of 64 apparently deep survivors got there.
    """
    left, right = FAMILY.get(from_class), FAMILY.get(to_class)
    if left is None or right is None:
        return UNRANKED
    if left != right:
        return FORGETS_AN_OPERATION
    return max(STRENGTH.get(from_class, 0) - STRENGTH.get(to_class, 0), 0)


def _statement_of(source: str) -> str:
    """Binders and conclusion, cut at the `:=` that introduces the proof.

    The one at bracket depth zero, not the first one. A named argument writes
    `:=` inside the statement -- `(R := R)` -- and a structure instance ends
    the statement with `where` and no `:=` at all. Cutting at the first `:=`
    leaves proof text in the head, and then the conclusion is read out of the
    proof: that is how a binder the conclusion never mentions passed this
    filter and was reported as a deep survivor.
    """
    depth = 0
    for i, ch in enumerate(source):
        if ch in "([{\u2983": depth += 1
        elif ch in ")]}\u2984": depth -= 1
        elif depth == 0 and source.startswith(":=", i):
            return source[:i]
        elif depth == 0 and source.startswith("where", i) and (i == 0 or source[i - 1].isspace()):
            return source[:i]
    return source


def _conclusion_of(head: str) -> str:
    """Everything after the statement's own colon, found at depth zero so a
    colon inside a binder cannot be mistaken for it."""
    depth = 0
    for i, ch in enumerate(head):
        if ch in "([{\u2983": depth += 1
        elif ch in ")]}\u2984": depth -= 1
        elif ch == ":" and depth == 0 and not head.startswith(":=", i):
            return head[i + 1:]
    return head


def reaches_conclusion(row: dict) -> bool:
    """Does the weakened binder's variable carry anything at all?

    A variable can appear in a signature and still be inert. `Ne.isUnit_C` is
    stated over `{k R : Type*}` with three instance binders about `R`, and its
    conclusion is `IsUnit (C u)` with `u : k`. `R` reaches nothing, so every
    class on it weakens for free -- three of this set's twenty-one items were
    that one theorem.

    Occurrences in `R`'s own declaration and in instance binders about `R` are
    both circular and do not count. What counts is the conclusion, or a value
    binder that mentions `R` while not declaring it.

    Found by reading the list and naming the failure the sweep's
    single `weakens` verdict was flattening.
    """
    argument = row["binder"].strip("[]").split()[-1]
    head = _statement_of(row["source"])
    conclusion = _conclusion_of(head)
    if re.search(rf"\b{re.escape(argument)}\b", conclusion):
        return True
    for binder in re.findall(r"[\[\(\{][^\[\]\(\)\{\}]*[\]\)\}]", head):
        if binder.startswith("["):
            continue
        names, _, body = binder[1:-1].partition(":")
        if argument in names.split():
            continue
        if re.search(rf"\b{re.escape(argument)}\b", body):
            return True
    return False


def actually_weakened(row: dict) -> bool:
    """Is the class we removed really gone from the signature?

    `needed()` reconstructs a declaration's file-level binders by following
    names through the statement, and it can emit the same class twice -- once
    from the theorem's own binder block and once from a `variable` line. The
    generator then weakens one copy and leaves the other, so the signature
    carries `[DivisionRing K]` and `[Field K]` side by side. It compiles, of
    course it compiles: nothing was weakened. Four of the sixteen survivors
    were this.

    Cheaper and more decisive than reasoning about which classes imply which:
    if the original class still appears applied to the same variable, there is
    nothing to judge.
    """
    argument = row["binder"].strip("[]").split()[-1]
    head = row["source"][: row["source"].find(":=")]
    pattern = rf"\[\s*(?:\w+\s*:\s*)?{re.escape(row['from_class'])}\s+{re.escape(argument)}\s*\]"
    return re.search(pattern, head) is None


def triage(rows: list[dict]) -> list[dict]:
    by_theorem: dict[tuple[str, str], list[dict]] = {}
    for row in rows:
        by_theorem.setdefault((row["module"], row["theorem"]), []).append(row)

    out: list[dict] = []
    for (module, theorem), group in by_theorem.items():
        breadth = len(group)
        for row in group:
            # The floor when descent has found one: the nominated edge is where
            # our table stopped, which is a fact about the table.
            target = row.get("floor") or row["to_class"]
            depth = magnitude(row["from_class"], target)
            # Every binder weakening at once is the signature of a lemma whose
            # proof is plumbing. One binder falling a long way is the signature
            # of a theorem that was never about the structure it was stated
            # over, which is the only bucket worth a conjecture.
            bucket = "structural" if depth >= 3 and breadth <= 2 else "reusability"
            score = round(min(depth / 4.0, 1.0) * 0.7
                          + (0.3 if breadth <= 2 else 0.0)
                          - (0.2 if breadth >= 4 else 0.0), 3)
            out.append({**row, "bucket": bucket, "breadth": breadth,
                        "magnitude": depth, "edge_to": target, "score": score})
    out.sort(key=lambda item: (-item["score"], item["module"], item["theorem"]))
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--export", type=Path, help="ranked JSONL for review")
    args = parser.parse_args()

    connection = sqlite3.connect(args.db)
    connection.row_factory = sqlite3.Row
    rows = [dict(r) for r in connection.execute(
        "SELECT * FROM weakening WHERE verdict = 'weakens'")]
    inert = [r for r in rows if not reaches_conclusion(r)]
    rows = [r for r in rows if reaches_conclusion(r)]
    duplicated = [r for r in rows if not actually_weakened(r)]
    rows = [r for r in rows if actually_weakened(r)]
    if inert or duplicated:
        print(json.dumps({"dropped_inert_binder": len(inert),
                          "dropped_class_still_present": len(duplicated)}))
    if not rows:
        print(json.dumps({"weakens": 0}))
        return 0
    ranked = triage(rows)
    counts: dict[str, int] = {}
    for item in ranked:
        counts[item["bucket"]] = counts.get(item["bucket"], 0) + 1
    print(json.dumps({"weakens": len(ranked), **counts}, indent=2))
    print()
    for item in ranked[:20]:
        print(f"  {item['score']:>5}  {item['bucket']:<12} "
              f"{item['theorem'][:38]:<38} {item['from_class']} -> {item['to_class']}")
    if args.export:
        with args.export.open("w", encoding="utf-8") as sink:
            for item in ranked:
                sink.write(json.dumps(item, ensure_ascii=False) + "\n")
        print(f"\n  wrote {len(ranked)} to {args.export}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
