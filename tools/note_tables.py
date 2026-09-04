#!/usr/bin/env python3
"""Generate the note's numbers from the stores, so prose cannot go stale.

The note argues from counts -- how many survivors, how many of them give up
invertibility, how deep the deepest go -- and those counts change every time an
area finishes. Prose that spells them out is wrong the moment the next sweep
lands, and wrong quietly, because nothing rereads a paragraph.

Every figure the note quotes is emitted here as a macro. An area counts as
complete only when every attempt has a verdict and the prior-art gate has run
over it; a half-swept area contributes nothing rather than contributing a
misleading fraction.
"""

from __future__ import annotations

import argparse
import collections
import json
import math
import re
import sqlite3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from catalogue import survivors as gated_survivors
from triage import magnitude, reaches_conclusion, actually_weakened
from typeclass import WEAKENINGS

# Classes that hand you a subtraction or an inverse, and classes that do not.
# The note's central claim is about the boundary between these two sets, so it
# is written out rather than derived: a reader should be able to check it.
INVERTIBLE = {"Field", "DivisionRing", "CommRing", "Ring", "NonUnitalRing",
              "LinearOrderedField", "LinearOrderedRing", "EuclideanDomain",
              "AddCommGroup", "AddGroup", "SubNegMonoid", "CommGroup", "Group",
              "DivInvMonoid", "GroupWithZero", "NormedAddCommGroup",
              "SeminormedAddCommGroup", "NormedField", "NormedRing"}
PLAIN = {"Semiring", "CommSemiring", "NonUnitalSemiring", "MonoidWithZero",
         "CommMonoidWithZero", "MulZeroClass", "NonUnitalNonAssocSemiring",
         "AddMonoid", "AddCommMonoid", "AddZeroClass", "AddSemigroup",
         "AddCommSemigroup", "Monoid", "MulOneClass", "Semigroup", "CommSemigroup"}

# Best's Table 1 (CICM 2021), Lean 3 names, paired with the Lean 4 edge our
# table contains -- or None where our hand-written list has no counterpart at
# all. The Nones are the point: they are the edges a term-inspection pass
# reaches and a fixed substitution table cannot.
#
# SELECTION RULE: every (original, replacement) pair in his Table 1 with a count
# of ten or more. His table is 14 originals against about fifty replacements, so
# a rule is needed and the note states this one.
#
# An outside referee could not reproduce our earlier count of 21 from his table
# at any threshold, and was right: at ten or more it is 25. Four pairs had been
# dropped in transcription, and all four are ones we cannot reach, so the error
# understated our own point. Re-derived against the published PDF, pair by pair.
BEST_TOP = [
    ("add_comm_group -> add_comm_monoid", 96, ("AddCommGroup", "AddCommMonoid")),
    ("ring -> semiring", 55, ("Ring", "Semiring")),
    ("semiring -> non_assoc_semiring", 53, None),
    ("add_monoid -> add_zero_class", 51, ("AddMonoid", "AddZeroClass")),
    ("comm_ring -> comm_semiring", 42, ("CommRing", "CommSemiring")),
    ("comm_ring -> ring", 40, ("CommRing", "Ring")),
    ("normed_space -> seminormed_space", 38, None),
    ("preorder -> has_lt", 36, None),
    ("normed_group -> seminormed_group", 36,
     ("NormedAddCommGroup", "SeminormedAddCommGroup")),
    ("monoid -> mul_one_class", 34, ("Monoid", "MulOneClass")),
    ("partial_order -> preorder", 33, ("PartialOrder", "Preorder")),
    ("preorder -> has_le", 31, None),
    ("comm_ring -> semiring", 27, None),
    ("comm_semiring -> semiring", 26, ("CommSemiring", "Semiring")),
    ("field -> division_ring", 23, ("Field", "DivisionRing")),
    ("semiring -> non_unital_non_assoc_semiring", 23,
     ("Semiring", "NonUnitalNonAssocSemiring")),
    ("semiring -> {add_comm_semigroup, has_one}", 13, None),
    ("field -> integral_domain", 12, None),
    ("normed_space -> module", 23, None),
    ("normed_group -> has_norm", 10, None),
    ("module -> has_scalar", 20, None),
    ("integral_domain -> comm_ring", 15, None),
    ("field -> comm_ring", 12, ("Field", "CommRing")),
    ("monoid -> has_mul", 11, None),
    ("comm_semiring -> monoid", 10, None),
]

WORDS = {0: "no", 1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
         6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten"}


def _wilson_pair(hits: int, total: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson bounds as numbers, where `wilson` above returns a formatted string."""
    if not total:
        return (0.0, 0.0)
    p = hits / total
    d = 1 + z * z / total
    centre = (p + z * z / (2 * total)) / d
    spread = z * math.sqrt(p * (1 - p) / total + z * z / (4 * total * total)) / d
    return (max(0.0, centre - spread), min(1.0, centre + spread))


def fisher(a: int, b: int, c: int, d: int) -> float:
    """Two groups, one binary outcome. Reported instead of a bare percentage
    because the baseline rate is itself an estimate and a percentage hides it."""
    n1, n2, k = a + b, c + d, a + c
    total = n1 + n2
    observed = math.comb(n1, a) * math.comb(n2, k - a) / math.comb(total, k)
    return sum(math.comb(n1, i) * math.comb(n2, k - i) / math.comb(total, k)
               for i in range(0, min(n1, k) + 1)
               if math.comb(n1, i) * math.comb(n2, k - i) / math.comb(total, k)
               <= observed + 1e-12)


def wilson(hits: int, total: int, z: float = 1.96) -> str:
    """A percentage on a small sample invites reading noise as signal.

    The control below rests on two intervals overlapping, so the interval is
    the claim and has to be printed rather than asserted.
    """
    if not total:
        return "---"
    p = hits / total
    d = 1 + z * z / total
    centre = (p + z * z / (2 * total)) / d
    half = z * math.sqrt(p * (1 - p) / total + z * z / (4 * total * total)) / d
    return f"[{100 * max(0.0, centre - half):.2f}, {100 * min(1.0, centre + half):.2f}]"


def area_of(module: str) -> str:
    parts = module.split(".")
    return parts[1] if parts[0] == "Mathlib" and len(parts) > 1 else parts[0]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", type=Path, action="append", required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--predicted", type=Path,
                        help="the pre-registered test areas, kept in their own "
                             "store: folding them into the main counts would "
                             "destroy the comparison they exist to make")
    parser.add_argument("--coverage", type=Path, action="append", default=[],
                        help="stores that count toward coverage but not toward "
                             "the pattern: areas swept after the pattern was "
                             "found and after the test that checked it")
    parser.add_argument("--dense", type=Path,
                        help="a store holding an area built ON invertible "
                             "structures, the opposite end of the gradient from "
                             "--predicted")
    parser.add_argument("--dense-area", default="LinearAlgebra")
    parser.add_argument("--rerun", type=Path,
                        help="a store holding one area swept a second time with "
                             "a different table, so the two can be compared on "
                             "the same mathematics")
    parser.add_argument("--rerun-area", action="append", default=[])
    parser.add_argument("--rerun-against", type=Path, action="append", default=[],
                        help="stores holding the FIRST table's sweep of the "
                             "rerun areas. Defaults to --db, which is right "
                             "only while the rerun areas are all discovery "
                             "areas. They are not any more, and the fix is not "
                             "to widen --db: --db is the pattern set, and "
                             "folding the confirmation areas into it destroys "
                             "the separation the note is built on")
    parser.add_argument("--categorical", type=Path,
                        help="store holding the sweep of an area the hand table "
                             "could not reach at all")
    parser.add_argument("--categorical-area", default="CategoryTheory")
    parser.add_argument("--derived-table", type=Path,
                        help="the table derived from class ... extends")
    parser.add_argument("--gradient-area", action="append", default=[],
                        help="areas placed on the invertibility scale by "
                             "prediction, right or wrong; repeatable")
    parser.add_argument("--citations", type=Path,
                        help="citations.jsonl from the companion project")
    parser.add_argument("--patches", type=Path,
                        help="patches/REPORT.json from tools/patches.py")
    parser.add_argument("--classification", type=Path,
                        help="replaceable.jsonl; the unused/replaceable split")
    parser.add_argument("--tauceti-source", type=Path,
                        help="the Tau Ceti source tree, for its declaration count")
    parser.add_argument("--tauceti", type=Path,
                        help="a sweep of a corpus no human wrote, kept in its "
                             "own store so it can never join the Mathlib counts")
    args = parser.parse_args()

    # A store named on the command line and not present used to be skipped, so
    # a typo or a store that had moved produced a full macro file of zeros and
    # exit 0 -- the failure mode ENGINEERING.md is named after, in the tool that
    # generates the numbers reporting it. Anything explicitly named must exist.
    named = [("--db", p) for p in args.db]
    for flag in ("predicted", "coverage", "dense", "rerun", "rerun_against",
                 "categorical", "tauceti", "derived_table", "citations",
                 "patches", "classification"):
        value = getattr(args, flag, None)
        if value is None:
            continue
        for path in (value if isinstance(value, list) else [value]):
            named.append(("--" + flag.replace("_", "-"), path))
    missing = [f"{flag} {path}" for flag, path in named if not Path(path).exists()]
    if missing:
        print("named but not found:\n  " + "\n  ".join(missing), file=sys.stderr)
        return 2

    rows: list[dict] = []
    for db in args.db:
        connection = sqlite3.connect(db)
        connection.row_factory = sqlite3.Row
        cols = {c[1] for c in connection.execute("PRAGMA table_info(weakening)")}
        for row in connection.execute("SELECT * FROM weakening"):
            item = dict(row)
            item.setdefault("subsumed", None)
            item.setdefault("floor", None)
            rows.append(item)

    grouped: dict[str, list[dict]] = collections.defaultdict(list)
    for row in rows:
        grouped[area_of(row["module"])].append(row)

    complete = {}
    for area, members in grouped.items():
        if any(m["verdict"] is None for m in members):
            continue
        if not any(m["subsumed"] for m in members):
            continue          # the gate has not run; the area is not finished
        complete[area] = members

    attempts = sum(len(m) for m in complete.values())
    # Deduplicate survivors the way the catalogue does, and only survivors:
    # (module, theorem, binder) identifies a finding, but NOT an attempt --
    # every binder is tried against several target classes, so applying this
    # key to the whole table collapses the attempt count itself.
    found: dict[tuple, dict] = {}
    for members in complete.values():
        for r in members:
            if (r["verdict"] == "weakens" and r["subsumed"] == "new"
                    and reaches_conclusion(r) and actually_weakened(r)):
                found.setdefault((r["module"], r["theorem"], r["binder"]), r)
    survivors = list(found.values())

    nominated = [r for members in complete.values() for r in members
                 if r["verdict"] == "weakens"]

    def target(row):
        # The class the shipped source is verified to carry, not the descent's
        # floor. The descent searched below `to_class` and recorded only the
        # name of what it reached; the store kept no source for it, so the
        # export publishes `to_class` and marks the floor unverified. Depth and
        # invertibility statistics computed from the floor would rest on a
        # class the artifact itself says it cannot check.
        return row["to_class"]

    lost = [r for r in survivors
            if r["from_class"] in INVERTIBLE and target(r) in PLAIN]
    ranked = sorted(survivors, key=lambda r: -magnitude(r["from_class"], target(r)))
    deepest = [r for r in ranked if magnitude(r["from_class"], target(r)) >= 4]
    deep_lost = [r for r in deepest if r in lost]

    root = args.mathlib / "Mathlib"
    files = list(root.rglob("*.lean"))
    swept_files = sum(len(list((root / area).rglob("*.lean")))
                      for area in complete if (root / area).is_dir())

    # --- the comparison against Best's published table -------------------
    all_rows = [r for members in complete.values() for r in members]
    edge_tried = collections.Counter()
    edge_found = collections.Counter()
    for r in all_rows:
        edge_tried[(r["from_class"], r["to_class"])] += 1
    for r in survivors:
        edge_found[(r["from_class"], r["to_class"])] += 1

    best_missing = sum(1 for _, _, ours in BEST_TOP if ours is None)
    head_label, head_count, head_edge = BEST_TOP[0]
    head_rows = [r for r in all_rows
                 if (r["from_class"], r["to_class"]) == head_edge]
    head_nab = sum(1 for r in head_rows if r["verdict"] == "not_a_binder")
    head_real = [r for r in head_rows if r["verdict"] != "not_a_binder"]
    head_inc = sum(1 for r in head_real if r["verdict"] == "incoherent")

    # What a pass that only reads a proof term cannot see: the weakened
    # statement does not typecheck, because a sibling assumption demands the
    # class back. Measured over attempts that named a binder the theorem has.
    genuine = [r for r in all_rows if r["verdict"] != "not_a_binder"]
    incoherent = sum(1 for r in genuine if r["verdict"] == "incoherent")

    root = args.mathlib / "Mathlib"
    files = list(root.rglob("*.lean"))
    swept_files = sum(len(list((root / area).rglob("*.lean")))
                      for area in complete if (root / area).is_dir())

    # --- the pre-registered test ------------------------------------------
    # The prediction: areas where these weak structures are already the subject
    # should yield FEW deep survivors, because the author began in the right
    # setting. Reported with a Fisher exact test rather than a bare percentage,
    # because the baseline is itself an estimate from 324 survivors.
    pre = {}
    if args.predicted and args.predicted.exists():
        connection = sqlite3.connect(args.predicted)
        connection.row_factory = sqlite3.Row
        prows = [dict(r) for r in connection.execute("SELECT * FROM weakening")]
        for r in prows:
            r.setdefault("floor", None)
        pareas = sorted({area_of(r["module"]) for r in prows})
        pfound: dict[tuple, dict] = {}
        for r in prows:
            if (r["verdict"] == "weakens" and r["subsumed"] == "new"
                    and reaches_conclusion(r) and actually_weakened(r)):
                pfound.setdefault((r["module"], r["theorem"], r["binder"]), r)
        psurv = list(pfound.values())
        pdeep = [r for r in psurv if magnitude(r["from_class"], target(r)) >= 4]
        plost = [r for r in psurv
                 if r["from_class"] in INVERTIBLE and target(r) in PLAIN]
        base_deep, base_lost, base_n = len(deepest), len(lost), len(survivors)
        pre = {
            "predictedAreas": ", ".join(pareas),
            "predictedAttempts": f"{len(prows):,}".replace(",", "{,}"),
            "predictedSurvivors": len(psurv),
            "predictedDeep": len(pdeep),
            "predictedDeepExpected": f"{len(psurv) * base_deep / max(base_n, 1):.1f}",
            "predictedDeepP": f"{fisher(base_deep, base_n - base_deep, len(pdeep), len(psurv) - len(pdeep)):.3f}",
            "baseLostPercent": f"{100 * base_lost / max(base_n, 1):.1f}",
            "predictedLost": len(plost),
            "predictedLostPercent": f"{100 * len(plost) / max(len(psurv), 1):.1f}",
            "predictedLostExpected": f"{len(psurv) * base_lost / max(base_n, 1):.1f}",
            "predictedLostP": f"{fisher(base_lost, base_n - base_lost, len(plost), len(psurv) - len(plost)):.4f}",
        }
        # Coverage is coverage. These areas belong to neither the discovery
        # set nor the test set, but the library does not care which bucket a
        # file was swept under.
        cov_areas, cov_attempts = set(), 0
        cov_found: dict[tuple, dict] = {}
        for store in args.coverage:
            if not store.exists():
                continue
            link = sqlite3.connect(store)
            link.row_factory = sqlite3.Row
            grouped_cov = collections.defaultdict(list)
            for raw in link.execute("SELECT * FROM weakening"):
                item = dict(raw)
                item.setdefault("floor", None)
                item.setdefault("subsumed", None)
                if item["module"].startswith("Mathlib."):
                    grouped_cov[area_of(item["module"])].append(item)
            for name, members in grouped_cov.items():
                if any(m["verdict"] is None for m in members):
                    continue
                if not any(m["subsumed"] for m in members):
                    continue
                cov_areas.add(name)
                cov_attempts += len(members)
                # Findings, not rows: a binder surviving at two target classes
                # is one finding. Counting rows here put the note ten ahead of
                # its own catalogue.
                for m in members:
                    if (m["verdict"] == "weakens" and m["subsumed"] == "new"
                            and reaches_conclusion(m) and actually_weakened(m)):
                        cov_found.setdefault((m["module"], m["theorem"], m["binder"]), m)

        # Coverage is coverage, whichever set an area belongs to.
        pre_files = sum(len(list((root / a).rglob("*.lean")))
                        for a in set(pareas) | cov_areas if (root / a).is_dir())
        every = sorted(set(complete) | set(pareas) | cov_areas)
        pre["allAreas"] = len(every)
        pre["allAreasWord"] = WORDS.get(len(every), str(len(every)))
        # A sentence-initial number word has to be capitalised, and the note
        # opens two paragraphs with one. Rendered "seven subject areas" under
        # the Limits heading until somebody read the typeset page.
        pre["allAreasWordCap"] = WORDS.get(len(every), str(len(every))).capitalize()
        pre["allAreaNames"] = ", ".join(every)
        pre["allSurvivors"] = base_n + len(psurv) + len(cov_found)
        pre["allAttempts"] = f"{attempts + len(prows) + cov_attempts:,}".replace(",", "{,}")
        pre["allSweptFiles"] = f"{swept_files + pre_files:,}".replace(",", "{,}")
        pre["allSweptPercent"] = f"{100 * (swept_files + pre_files) / max(len(files), 1):.0f}"
        # The throughput sentence is about the whole sweep, so its per-file
        # figure must be too. It quoted the discovery set's 24 for a paragraph
        # counting 18 areas, and an outside referee recomputed it, got a
        # different number, and reported the paper as contradicting itself. The
        # arithmetic was right and the label was missing.
        # The control compares a rate against Mathlib's, and the rate it should
        # compare against is the whole hand-table sweep rather than the four
        # discovery areas: it is the larger sample, the more representative one,
        # and the more powerful comparison. The discovery yield stays for the
        # sections that are genuinely about the discovery set.
        _all_n = attempts + len(prows) + cov_attempts
        _all_k = base_n + len(psurv) + len(cov_found)
        pre["allYield"] = f"{100 * _all_k / max(_all_n, 1):.2f}"
        _lo, _hi = _wilson_pair(_all_k, _all_n)
        pre["allYieldCI"] = f"[{100 * _lo:.2f}, {100 * _hi:.2f}]"
        # Theorem-level counts, which is the unit a reader cares about. Rows
        # and attempts are the instrument's units: a theorem is tried with
        # several binders against several target classes, so "attempts" is a
        # number about us and "theorems" is a number about the library. The
        # paper leads with these and keeps the rest for the method section.
        _seen, _won = set(), set()
        for _store in list(args.db) + list(args.coverage or []) + (
                [args.predicted] if args.predicted else []):
            if not _store or not _store.exists():
                continue
            _link = sqlite3.connect(f"file:{_store}?mode=ro", uri=True)
            for _m, _t in _link.execute(
                    "SELECT DISTINCT module, theorem FROM weakening "
                    "WHERE verdict IS NOT NULL AND module LIKE 'Mathlib.%'"):
                _seen.add((_m, _t))
            _link.close()
            for _r in gated_survivors(str(_store)):
                _won.add((_r["module"], _r["theorem"]))
        pre["theoremsExamined"] = f"{len(_seen):,}".replace(",", "{,}")
        pre["theoremsWeakened"] = len(_won)
        pre["theoremRate"] = f"{100 * len(_won) / max(len(_seen), 1):.2f}"
        pre["theoremOneIn"] = len(_seen) // max(len(_won), 1)
        pre["theoremFiles"] = len({_m for _m, _ in _won})
        pre["allAttemptsPerFile"] = (
            f"{(attempts + len(prows) + cov_attempts) / max(swept_files + pre_files, 1):.0f}")

    # --- coverage of the second instrument ------------------------------
    # The hand table stopped at 18 areas. The derived-table pass went to the
    # end of the library, and that is the coverage claim the engineering
    # argument rests on -- so it is emitted separately and named, rather than
    # folded into the hand table's figure where it would silently inflate it.
    if args.rerun and args.rerun.exists() and files:
        link = sqlite3.connect(f"file:{args.rerun}?mode=ro", uri=True)
        done = [a for a, todo in link.execute(
            "SELECT substr(module, 9, instr(substr(module, 9), '.') - 1), "
            "SUM(verdict IS NULL) FROM weakening WHERE module LIKE 'Mathlib.%' "
            "GROUP BY 1") if not todo]
        attempts_2 = link.execute(
            "SELECT COUNT(*) FROM weakening WHERE verdict IS NOT NULL").fetchone()[0]
        link.close()
        swept_2 = sum(len(list((root / a).rglob("*.lean")))
                      for a in done if (root / a).is_dir())
        pre["derivedAreas"] = len(done)
        pre["derivedSweptFiles"] = f"{swept_2:,}".replace(",", "{,}")
        pre["derivedSweptPercent"] = f"{100 * swept_2 / max(len(files), 1):.0f}"
        pre["derivedAttempts"] = f"{attempts_2:,}".replace(",", "{,}")

    # --- the other end of the gradient -------------------------------------
    # The predicted-low areas have no invertibility to give up. An area built
    # entirely on modules over rings and fields has nothing but. If the reading
    # is right the two must fall on opposite sides of the baseline, and that is
    # a harder thing to get by accident than one comparison in one direction.
    dense = {}
    if args.dense and args.dense.exists() and pre:
        connection = sqlite3.connect(args.dense)
        connection.row_factory = sqlite3.Row
        drows = [dict(r) for r in connection.execute(
            "SELECT * FROM weakening WHERE verdict = 'weakens' AND module LIKE ?",
            (f"Mathlib.{args.dense_area}.%",))]
        for r in drows:
            r.setdefault("floor", None)
        dfound: dict[tuple, dict] = {}
        for r in drows:
            if (r["subsumed"] == "new" and reaches_conclusion(r)
                    and actually_weakened(r)):
                dfound.setdefault((r["module"], r["theorem"], r["binder"]), r)
        dsurv = list(dfound.values())
        dlost = [r for r in dsurv
                 if r["from_class"] in INVERTIBLE and target(r) in PLAIN]
        if dsurv:
            dense = {
                "denseArea": args.dense_area,
                "denseSurvivors": len(dsurv),
                "denseLost": len(dlost),
                "denseLostPercent": f"{100 * len(dlost) / len(dsurv):.0f}",
                "denseVsPredictedP": f"{fisher(len(dlost), len(dsurv) - len(dlost), len(plost), len(psurv) - len(plost)):.1e}".replace("e-0", r"\times 10^{-") + "}",
                "denseVsBaseP": f"{fisher(len(dlost), len(dsurv) - len(dlost), base_lost, base_n - base_lost):.4f}",
            }

    # --- the scale, including the area we placed wrongly --------------------
    # Every area named here was predicted before it was swept. One of them was
    # predicted wrongly, and it stays: a scale reported only where it worked is
    # not evidence, it is selection.
    grad_rows, grad_lost, grad_total = [], 0, 0
    if args.dense and args.dense.exists() and pre:
        connection = sqlite3.connect(args.dense)
        connection.row_factory = sqlite3.Row
        for name in args.gradient_area:
            arows = [dict(r) for r in connection.execute(
                "SELECT * FROM weakening WHERE verdict = 'weakens' AND module LIKE ?",
                (f"Mathlib.{name}.%",))]
            for r in arows:
                r.setdefault("floor", None)
            afound: dict[tuple, dict] = {}
            for r in arows:
                if (r["subsumed"] == "new" and reaches_conclusion(r)
                        and actually_weakened(r)):
                    afound.setdefault((r["module"], r["theorem"], r["binder"]), r)
            asurv = list(afound.values())
            alost = [r for r in asurv
                     if r["from_class"] in INVERTIBLE and target(r) in PLAIN]
            if not asurv:
                continue
            grad_lost += len(alost)
            grad_total += len(asurv)
            grad_rows.append((100 * len(alost) / len(asurv),
                              rf"{name} & {len(alost)}/{len(asurv)} & "
                              rf"{100 * len(alost) / len(asurv):.0f}\%"))
    if grad_rows:
        pre["gradientRows"] = r" \\ ".join(row for _, row in grad_rows)
        pre["gradientMax"] = f"{max(p for p, _ in grad_rows):.0f}"
        pre["gradientLost"] = grad_lost
        pre["gradientTotal"] = grad_total
        pre["gradientPercent"] = f"{100 * grad_lost / grad_total:.0f}"
        pre["gradientP"] = (f"{fisher(grad_lost, grad_total - grad_lost, len(plost), len(psurv) - len(plost)):.1e}"
                            .replace("e-1", r"\times 10^{-1").replace("e-0", r"\times 10^{-") + "}")

    # --- the same area, two tables ----------------------------------------
    # "The hand table is a lower bound" is the wrong shape. It is a different
    # sample: each table finds survivors the other cannot reach.
    rerun = {}
    if args.rerun and args.rerun.exists():
        def swept(store, area):
            # The trailing dot is load-bearing. `Mathlib.Algebra%` also matches
            # `Mathlib.AlgebraicGeometry` and `Mathlib.AlgebraicTopology`, which
            # folded 610 of their rows into Algebra's counts. It was invisible
            # for as long as those two areas were unswept and appeared the day
            # they were, which is the usual way here: the bug arrives with the
            # data rather than with the code.
            link = sqlite3.connect(f"file:{store}?mode=ro", uri=True)
            link.row_factory = sqlite3.Row
            out = {}
            for raw in link.execute(
                    "SELECT * FROM weakening WHERE verdict = 'weakens' AND module LIKE ?",
                    (f"Mathlib.{area}.%",)):
                item = dict(raw)
                item.setdefault("floor", None)
                if (item["subsumed"] == "new" and reaches_conclusion(item)
                        and actually_weakened(item)):
                    out.setdefault((item["module"], item["theorem"], item["binder"]), item)
            return out

        rows_out, hand_all, union_all = [], 0, 0
        against = args.rerun_against or args.db
        for name in args.rerun_area or ["Algebra"]:
            old_side = {}
            for store in against:
                if store.exists():
                    old_side.update(swept(store, name))
            new_side = swept(args.rerun, name)
            if not (old_side and new_side):
                continue
            both = len(set(old_side) & set(new_side))
            hand_all += len(old_side)
            union_all += len(set(old_side) | set(new_side))
            rows_out.append(rf"{name} & {len(old_side)} & {len(new_side)} & {both} & "
                            rf"{len(set(old_side) | set(new_side))}")
        if rows_out:
            rerun = {
                "rerunRows": r" \\ ".join(rows_out),
                "rerunHand": hand_all,
                "rerunUnion": union_all,
                "rerunGainPercent": f"{100 * (union_all - hand_all) / hand_all:.0f}",
            }

    # --- the area the hand table could not reach --------------------------
    categorical = {}
    if args.categorical and args.categorical.exists():
        link = sqlite3.connect(args.categorical)
        link.row_factory = sqlite3.Row
        crows = [dict(r) for r in link.execute(
            "SELECT * FROM weakening WHERE module LIKE ? AND verdict IS NOT NULL",
            (f"Mathlib.{args.categorical_area}.%",))]
        for r in crows:
            r.setdefault("floor", None)
        if crows:
            cfound = {}
            for r in crows:
                if (r["verdict"] == "weakens" and r["subsumed"] == "new"
                        and reaches_conclusion(r) and actually_weakened(r)):
                    cfound.setdefault((r["module"], r["theorem"], r["binder"]), r)
            ctx = sum(1 for r in crows if r["verdict"] == "context")
            root_area = args.mathlib / "Mathlib" / args.categorical_area
            categorical = {
                "catArea": args.categorical_area,
                "catFiles": f"{len(list(root_area.rglob('*.lean'))):,}".replace(",", "{,}"),
                "catAttempts": len(crows),
                "catSurvivors": len(cfound),
                "catContextPercent": f"{100 * ctx / len(crows):.0f}",
            }
    if args.derived_table and args.derived_table.exists():
        derived = json.loads(args.derived_table.read_text(encoding="utf-8"))
        categorical["derivedEdges"] = sum(len(v) for v in derived.values())
        categorical["derivedClasses"] = len(derived)

    # --- the control: the same instrument on a corpus no human wrote -------
    tau = {}
    if args.tauceti and args.tauceti.exists():
        connection = sqlite3.connect(args.tauceti)
        connection.row_factory = sqlite3.Row
        trows = [dict(r) for r in connection.execute(
            "SELECT * FROM weakening WHERE verdict IS NOT NULL "
            "AND verdict != 'out_of_sample'")]
        # The gate must have run on every nomination before a yield means
        # anything. Mid-census the denominator grows with each attempt while the
        # numerator only counts rows the prior-art stage has passed, so a yield
        # computed here reads as a collapse that is really a missing stage. This
        # very check would have put a threefold difference into the abstract.
        _ungated = [r for r in trows if r["verdict"] == "weakens"
                    and not r["subsumed"]]
        if _ungated:
            raise SystemExit(
                f"{args.tauceti}: {len(_ungated)} of "
                f"{sum(1 for r in trows if r['verdict'] == 'weakens')} nominations "
                f"have no prior-art verdict yet. Run the gate over this store "
                f"before generating macros -- a yield taken now divides a "
                f"gated numerator by an ungated denominator.")
        # Deduplicated by (module, theorem, binder), exactly as the Mathlib
        # side is. Without this the control compares a deduplicated 462 against
        # an undeduplicated 73 and flatters Tau Ceti by a few percent -- a
        # like-for-like comparison has to count the same thing on both sides.
        _tfound: dict[tuple, dict] = {}
        for r in trows:
            if (r["verdict"] == "weakens" and r["subsumed"] == "new"
                    and reaches_conclusion(r) and actually_weakened(r)):
                _tfound.setdefault((r["module"], r["theorem"], r["binder"]), r)
        tsurv = list(_tfound.values())
        # The comparison itself, not just the two rates: a null result is only
        # worth reading with its resolution attached.
        _mk = base_n + len(psurv) + len(cov_found)
        _mn = attempts + len(prows) + cov_attempts
        _p = fisher(len(tsurv), len(trows) - len(tsurv), _mk, _mn - _mk)
        tau = {
            "tauVsMathlibP": f"{_p:.2f}",
            "tauRatio": f"{(len(tsurv) / max(len(trows), 1)) / max(_mk / max(_mn, 1), 1e-12):.2f}",
            "tauAttempts": f"{len(trows):,}".replace(",", "{,}"),
            "tauSurvivors": len(tsurv),
            "tauYield": f"{100 * len(tsurv) / max(len(trows), 1):.2f}",
            "tauYieldCI": wilson(len(tsurv), len(trows)),
        }

    # --- population: how many declarations exist at all -------------------
    # The denominator a reader assumes. "1.47% of theorems examined" and
    # "0.23% of the library" are both true and mean different things, so both
    # are emitted and the paper prints them side by side.
    DECL_RE = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)?"
        r"(?:theorem|lemma)\s+", re.M)

    def declarations(tree: Path) -> int:
        total = 0
        for path in tree.rglob("*.lean"):
            if ".lake" in path.relative_to(tree).parts:
                continue
            try:
                total += len(DECL_RE.findall(
                    path.read_text(encoding="utf-8", errors="ignore")))
            except OSError:
                pass
        return total

    # How much of the library the sieve can see at all, which is not the same
    # as how much it swept. Three disjoint groups: no instance binder in scope
    # (nothing to weaken, correctly out of scope), binders whose classes no
    # table covers (a table limitation), and binders we could weaken (the
    # reachable population). The gap between reachable and examined is coverage,
    # not design, and the paper has to say which is which.
    VAR_RE = re.compile(r"^\s*variable\s*(.*)$", re.M)
    INST_RE = re.compile(r"\[\s*(?:[A-Za-z_][\w']*\s*:\s*)?([A-Z][\w'.]*)")
    HEAD_RE = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)?"
        r"(?:theorem|lemma)\s+\S+([^:]*)", re.M)

    def reachability(tree: Path, table: set) -> tuple[int, int, int, int]:
        total = reach = covered = bare = 0
        for path in tree.rglob("*.lean"):
            if ".lake" in path.relative_to(tree).parts:
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            in_file = set()
            for v in VAR_RE.finditer(text):
                in_file |= set(INST_RE.findall(v.group(1)))
            file_hit = bool(in_file & table)
            for m in HEAD_RE.finditer(text):
                total += 1
                own = set(INST_RE.findall(m.group(1)))
                if (own & table) or file_hit:
                    reach += 1
                elif own or in_file:
                    covered += 1
                else:
                    bare += 1
        return total, reach, covered, bare

    population = {}
    _mb_tree = args.mathlib / "Mathlib"
    if _mb_tree.is_dir():
        _n = declarations(_mb_tree)
        population["mathlibTheorems"] = f"{_n:,}".replace(",", "{,}")
        population["mathlibExaminedPercent"] = f"{100 * len(_seen) / max(_n, 1):.1f}"
        population["mathlibWeakenablePercent"] = f"{100 * len(_won) / max(_n, 1):.2f}"
        _tbl = set(WEAKENINGS.keys()) if isinstance(WEAKENINGS, dict) else {
            a for a, _ in WEAKENINGS}
        if args.derived_table and args.derived_table.exists():
            _tbl |= set(json.loads(
                args.derived_table.read_text(encoding="utf-8")).keys())
        _tot, _reach, _cov, _bare = reachability(_mb_tree, _tbl)
        # Is the examined set representative? It is not a random sample -- the
        # areas were chosen and a theorem enters only if a binder could be
        # located -- so the composition is skewed. The test that matters is
        # whether the skew moves the answer: re-weight each area's own rate by
        # its share of the corpus rather than by its share of what we examined.
        _ex, _wn, _corp = collections.Counter(), collections.Counter(), collections.Counter()
        for _st in list(args.db) + list(args.coverage or []) + (
                [args.predicted] if args.predicted else []):
            if not _st or not _st.exists():
                continue
            _l = sqlite3.connect(f"file:{_st}?mode=ro", uri=True)
            for _m, _t in _l.execute(
                    "SELECT DISTINCT module, theorem FROM weakening "
                    "WHERE verdict IS NOT NULL AND module LIKE 'Mathlib.%'"):
                _ex[_m.split(".")[1]] += 1
            _l.close()
            for _r in gated_survivors(str(_st)):
                if _r["module"].startswith("Mathlib."):
                    _wn[_r["module"].split(".")[1]] += 1
        for _p in _mb_tree.rglob("*.lean"):
            _rel = _p.relative_to(_mb_tree).parts
            if ".lake" in _rel or len(_rel) < 2:
                continue
            try:
                _corp[_rel[0]] += len(DECL_RE.findall(
                    _p.read_text(encoding="utf-8", errors="ignore")))
            except OSError:
                pass
        _big = [a for a in _ex if _ex[a] >= 200]
        if _big:
            _r = {a: _wn[a] / _ex[a] for a in _big}
            _we, _wc = sum(_ex[a] for a in _big), sum(_corp[a] for a in _big)
            _obs = sum(_r[a] * _ex[a] for a in _big) / max(_we, 1)
            _rew = sum(_r[a] * _corp[a] for a in _big) / max(_wc, 1)
            population["reweightedRate"] = f"{100 * _rew:.2f}"
            population["reweightAreas"] = len(_big)
        population["reachablePercent"] = f"{100 * _reach / max(_tot, 1):.0f}"
        population["noTableClassPercent"] = f"{100 * _cov / max(_tot, 1):.0f}"
        population["noBinderPercent"] = f"{100 * _bare / max(_tot, 1):.0f}"
    if args.tauceti_source and args.tauceti_source.is_dir():
        _tn = declarations(args.tauceti_source)
        population["tauTheorems"] = f"{_tn:,}".replace(",", "{,}")
        if tau:
            _texam = len({(r["module"], r["theorem"]) for r in trows})
            _twon = len({(r["module"], r["theorem"]) for r in tsurv})
            population["tauExamined"] = f"{_texam:,}".replace(",", "{,}")
            population["tauWeakenable"] = _twon
            population["tauExaminedPercent"] = f"{100 * _texam / max(_tn, 1):.1f}"
            population["tauOfExaminedPercent"] = f"{100 * _twon / max(_texam, 1):.2f}"
            population["tauWeakenablePercent"] = f"{100 * _twon / max(_tn, 1):.2f}"

    # --- did the proof never use it, or merely not need it? ---------------
    split = {}
    if args.classification and args.classification.exists():
        _v = collections.Counter(
            json.loads(l)["verdict"]
            for l in args.classification.read_text(encoding="utf-8").splitlines()
            if l.strip())
        _known = _v["unused"] + _v["replaceable"]
        split = {
            "unusedCount": _v["unused"],
            "replaceableCount": _v["replaceable"],
            "unclassifiedCount": _v["unreadable"],
            "classifiedCount": _known,
            "unusedPercent": f"{100 * _v['unused'] / max(_known, 1):.1f}",
            "replaceablePercent": f"{100 * _v['replaceable'] / max(_known, 1):.1f}",
        }

    # Are the survivors classical results or working lemmas? Three proxies from
    # the source text, all about naming, which is a convention rather than a
    # measurement -- the honest way to report it is with the locator's own miss
    # rate beside it.
    naming = {}
    if _mb_tree.is_dir() and "_won" in dir():
        _doc = _bold = _found = 0
        _cache: dict[str, str] = {}
        # The published survivors, one entry per (module, theorem) -- not the
        # raw attempt rows, which are two orders of magnitude more numerous and
        # gave a "located" count of 49,214 from 645 survivors.
        for _mod, _thm in sorted(_won):
            _r = {"module": _mod, "theorem": _thm}
            # One read per module, not one per row: 645 rows share 325 files and
            # re-reading each was slow enough to time the generator out.
            if _r["module"] not in _cache:
                _f = _mb_tree.parent / (_r["module"].replace(".", "/") + ".lean")
                try:
                    _cache[_r["module"]] = _f.read_text(encoding="utf-8",
                                                        errors="ignore")
                except OSError:
                    _cache[_r["module"]] = ""
            _txt = _cache[_r["module"]]
            if not _txt:
                continue
            _leaf = _r["theorem"].split(".")[-1]
            _m = re.search(
                r"(/--(?:(?!-/).)*?-/)?\s*(?:@\[[^\]]*\]\s*)?"
                r"(?:private\s+|protected\s+|nonrec\s+)?"
                r"(?:theorem|lemma)\s+" + re.escape(_leaf) + r"\b", _txt, re.S)
            if not _m:
                continue
            _found += 1
            if _m.group(1):
                _doc += 1
                if re.search(r"\*\*[^*]{3,60}\*\*", _m.group(1)):
                    _bold += 1
        naming = {
            "namedLocated": _found,
            "namedDocumented": _doc,
            "namedClassical": _bold,
            "namedDocumentedPercent": f"{100 * _doc / max(_found, 1):.0f}",
        }

    # The compiled patch set. Kept separate from every other count because it
    # is the one number here a maintainer can act on without reading anything.
    patches = {}
    if args.patches and args.patches.exists():
        _p = json.loads(args.patches.read_text(encoding="utf-8"))
        patches = {
            "patchGroups": _p["candidates"],
            "patchTested": _p["kept"] + _p["rejected"],
            "patchKept": _p["kept"],
            "patchRejected": _p["rejected"],
        }

    # Citation counts measured by the companion project, clustered here. Their
    # unclustered interval is narrower than the truth because survivors share
    # modules and authors; this applies the same Rao-Scott correction the
    # per-area rates get, and the comparison is against non-survivors in the
    # survivors' own modules rather than against the library at large -- the
    # wider baseline includes machinery that is genuinely never cited and
    # accounts for about half the raw gap.
    citations = {}
    if args.citations and args.citations.exists():
        _by = {}
        for _l in args.citations.read_text(encoding="utf-8").splitlines():
            if not _l.strip():
                continue
            _r = json.loads(_l)
            if _r["theorem"] not in _by or _r.get("found_in_corpus"):
                _by[_r["theorem"]] = _r
        _m = [r for r in _by.values() if r.get("found_in_corpus")]
        _n = len(_m)
        _k = sum(1 for r in _m if r["cited_by"] == 0)
        _mods = {r["module"] for r in _m}
        _pn = collections.Counter(r["module"] for r in _m if r["cited_by"] == 0)
        _c = [_pn.get(x, 0) for x in _mods]
        _mean = sum(_c) / max(len(_mods), 1)
        _var = sum((x - _mean) ** 2 for x in _c) / max(len(_mods), 1)
        _deff = max(1.0, _var / _mean) if _mean else 1.0
        _lo, _hi = _wilson_pair(round(_k / _deff), round(_n / _deff))
        _cnt = [r["cited_by"] for r in _m]
        _p1, _p2, _bn = _k / _n, 0.377, 20125
        _se = math.sqrt(_p1 * (1 - _p1) / (_n / _deff) + _p2 * (1 - _p2) / _bn)
        _z = (_p1 - _p2) / _se
        _pv = 2 * (1 - 0.5 * (1 + math.erf(abs(_z) / math.sqrt(2))))
        citations = {
            "citedN": _n,
            "citedNever": _k,
            "citedNeverPercent": f"{100 * _p1:.1f}",
            "citedNeverCI": f"[{100 * _lo:.1f}, {100 * _hi:.1f}]",
            "citedDeff": f"{_deff:.2f}",
            "citedControlPercent": f"{100 * _p2:.1f}",
            "citedControlN": f"{_bn:,}".replace(",", "{,}"),
            "citedGap": f"{100 * (_p2 - _p1):.1f}",
            "citedP": f"{_pv:.4f}",
            "citedMean": f"{sum(_cnt) / max(_n, 1):.2f}",
            "citedMax": max(_cnt) if _cnt else 0,
            # Baseline moments and the two wider gaps are the companion
            # project's, over populations we do not hold: they are constants
            # here for the same reason 0.377/20125 above are.
            "citedControlMean": "4.28",
            "citedControlMax": "4{,}249",
            "citedGapClean": "12.4",
            "citedGapAll": "15.7",
            "citedGenerated": "22{,}854",
        }

    macros = {
        **population,
        **citations,
        **patches,
        **naming,
        **split,
        "areasSwept": len(complete),
        "areasSweptWord": WORDS.get(len(complete), str(len(complete))),
        "areaNames": ", ".join(sorted(complete)),
        "attempts": f"{attempts:,}".replace(",", "{,}"),
        "survivors": len(survivors),
        "lostInvertibility": len(lost),
        "deepest": len(deepest),
        "deepestLost": len(deep_lost),
        "libraryFiles": f"{len(files):,}".replace(",", "{,}"),
        "sweptFiles": f"{swept_files:,}".replace(",", "{,}"),
        "sweptPercent": f"{100 * swept_files / max(len(files), 1):.0f}",
        # Written out because the note states it in prose. A hand-written
        # fraction here said "three quarters" when the stores said a half.
        "filterRejectPercent": f"{100 * (1 - len(survivors) / max(len(nominated), 1)):.0f}",
        "ourYield": f"{100 * len(survivors) / max(attempts, 1):.2f}",
        "ourYieldCI": wilson(len(survivors), attempts),
        "incoherentPercent": f"{100 * incoherent / max(len(genuine), 1):.0f}",
        # 27 source classes, 48 edges. The note said "twenty-seven possible
        # weakenings", which counted the classes and called them edges.
        "tableEdges": sum(len(v) for v in WEAKENINGS.values()),
        # Density varies from 2 to 39 attempts per file across areas, so this
        # is an average over what has actually been swept, not a constant.
        "attemptsPerFile": f"{attempts / max(swept_files, 1):.0f}",
        # Measured from the sprint logs rather than typed: 29,338 attempts in
        # 19.1 hours on one laptop, the run that answers Best's objection.
        "decisionsPerMinute": "26",
        "freeVerdictPercent": f"{100 * sum(1 for r in all_rows if r['verdict'] == 'not_a_binder') / max(len(all_rows), 1):.0f}",
        "bestTotal": "2{,}877",
        "bestTop": len(BEST_TOP),
        "bestMissing": best_missing,
        "bestHeadCount": head_count,
        "bestHeadAttempts": f"{len(head_rows):,}".replace(",", "{,}"),
        "bestHeadFound": edge_found.get(head_edge, 0),
        "bestHeadNotABinder": f"{100 * head_nab / max(len(head_rows), 1):.0f}",
        "bestHeadIncoherent": f"{100 * head_inc / max(len(head_real), 1):.0f}",
        "bestFieldDR": 23,
        "ourFieldDR": edge_found.get(("Field", "DivisionRing"), 0),
        **pre,
        **rerun,
        **categorical,
        **dense,
        **tau,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        "\n".join(f"\\newcommand{{\\{k}}}{{{v}}}" for k, v in macros.items()) + "\n")
    print(json.dumps({**macros, "complete_areas": sorted(complete)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
