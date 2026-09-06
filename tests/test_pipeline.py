#!/usr/bin/env python3
"""Regression tests, one per defect this pipeline actually shipped.

    python3 -m unittest discover -s tests -v
    python3 tests/coverage.py            # if `coverage` is installed

Every test below encodes a bug that produced a plausible number and survived
review. They are written as the failing case, not as an abstract property,
because that is the form in which each was found: somebody opened one example
and read what the machine actually said.

Stdlib `unittest` only. This repository has no dependencies and the point of it
is that a stranger can run one command; adding a test framework to check the
thing that must run without one would be a poor trade.
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))

import catalogue
import density
import derive_edges
import leanrun
import priorart
import signatures
import triage
import verify


class StatementSplitting(unittest.TestCase):
    """Cutting a declaration at the first `:=` truncates any statement with a
    named argument. It made 129 of 129 rows read as novel, and separately let a
    filter read its "conclusion" out of the proof."""

    def test_named_argument_does_not_end_the_statement(self):
        source = ("theorem w {R H} [Semiring H] : "
                  "(regularMul (R := R) (H := H)).toLinearMap = f := rfl")
        head = triage._statement_of(source)
        self.assertIn("toLinearMap", head, "cut before the statement ended")
        self.assertNotIn("rfl", head, "proof leaked into the statement")

    def test_structure_instance_ends_at_where(self):
        source = ("theorem w (n : ℕ) {R} [CommRing R] : StableUnder P "
                  "where left R S _ hf := trivial")
        head = triage._statement_of(source)
        self.assertNotIn("where", head)

    def test_inert_binder_is_rejected(self):
        """The conclusion mentions neither R nor S; the proof body does."""
        row = {"binder": "[CommRing R]",
               "source": ("theorem w (n : ℕ) {R : Type u} {S : Type v} "
                          "[Ring R] [CommRing S] :StableUnderComposition P "
                          "where left R S _ _ r hf")}
        self.assertFalse(triage.reaches_conclusion(row))

    def test_ordinary_binder_is_kept(self):
        row = {"binder": "[Field K]",
               "source": "theorem w {K} [Field K] (x : K) :x + 0 = x := by simp"}
        self.assertTrue(triage.reaches_conclusion(row))


class Magnitude(unittest.TestCase):
    """Depth is an ordinal within a family, and differing families short to the
    maximum. A class the tables do not list therefore scores maximum depth,
    which inflated one area's deep count from 12 to 30."""

    def test_within_family_is_a_difference(self):
        self.assertEqual(triage.magnitude("Field", "CommRing"),
                         triage.STRENGTH["Field"] - triage.STRENGTH["CommRing"])

    def test_a_class_nobody_listed_is_unranked_not_deep(self):
        """"Unknown" is not "different family". Treating it as such gave every
        unlisted target maximum depth and made 40 of 64 survivors look deep."""
        # A name no library will ever declare, so placing more classes cannot
        # make this test stale. The first version used StarMul, which was
        # unlisted at the time and got listed two commits later.
        self.assertEqual(triage.magnitude("Field", "NoSuchClassEverDeclared"),
                         triage.UNRANKED)
        self.assertLess(triage.UNRANKED, triage.FORGETS_AN_OPERATION,
                        "an unranked pair must not pass a `>= 4` deep test")

    def test_forgetting_an_operation_still_scores_the_maximum(self):
        """The genuine case survives: both listed, different hierarchies."""
        self.assertEqual(triage.magnitude("Field", "PartialOrder"),
                         triage.FORGETS_AN_OPERATION)

    def test_carriers_added_from_the_library(self):
        """CommMagma and friends are now placed, so a weakening into one is a
        measured two steps rather than an unmeasured four."""
        self.assertEqual(triage.magnitude("CommSemigroup", "CommMagma"), 2)


class PriorArtClassification(unittest.TestCase):
    """`why` compared a citation's leaf against a theorem's full name, so an
    own-name citation on a dotted theorem was filed as genuine prior art."""

    def test_own_name_on_a_dotted_theorem(self):
        self.assertEqual(
            priorart.why("IsComplexLinearMap.add", "exact IsComplexLinearMap.add hF hG"),
            "not_a_weakening")

    def test_a_different_theorem_is_prior_art(self):
        self.assertEqual(priorart.why("comap_mono", "exact comap_le_comap_iff.mpr hI"),
                         "known")


class SignatureCapture(unittest.TestCase):
    """Lean writes diagnostics into the `#check` stream, so an error following a
    check was absorbed into the preceding signature -- and a temp-file path was
    printed in a published document."""

    def test_diagnostics_are_cut(self):
        dirty = ("∀ {R} [CommRing R], P R /var/folders/ck/x/T/tmp.lean:11:8: "
                 "error(lean.unknownIdentifier): Unknown identifier `foo`")
        clean = signatures.cut_diagnostics(dirty)
        self.assertNotIn("/var/folders", clean)
        self.assertNotIn("error(", clean)
        self.assertIn("CommRing", clean)

    def test_a_clean_signature_is_untouched(self):
        good = "∀ {R : Type u_1} [inst : CommRing R], P R"
        self.assertEqual(signatures.cut_diagnostics(good), good)

    def test_imports_precede_set_option(self):
        """An `import` after any command is a syntax error, which resolves the
        whole batch to zero and reads exactly like a corpus with no
        declarations."""
        header = signatures.header_for_modules(["Other.Foo"])
        self.assertLess(header.index("import Other.Foo"), header.index("set_option"))


class DerivedTable(unittest.TestCase):
    """A line-by-line scan misses `class X (a : T)\\n  extends Y` and reports
    that X extends nothing. That lost 89 classes and 171 edges."""

    def test_extends_on_a_following_line(self):
        """Drives scan() over a real tree, not its regexes. The first version of
        this test poked at the patterns and reported 0% coverage of the function
        it was supposed to protect."""
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "Mathlib" / "Algebra"
            root.mkdir(parents=True)
            (root / "Defs.lean").write_text(
                "class Mul (a : Type u) where\n  mul : a\n\n"
                "class Semigroup (G : Type u) extends Mul G where\n  assoc : True\n\n"
                "class DivisionRing (K : Type*)\n"
                "  extends Ring K, DivInvMonoid K, Nontrivial K where\n"
                "  inv_ne : True\n",
                encoding="utf-8")
            arity, edges = derive_edges.scan(Path(tmp) / "Mathlib")

        self.assertIn("DivisionRing", edges,
                      "a class whose `extends` sits on the next line was missed; "
                      "that cost 89 classes and 171 edges")
        self.assertEqual(edges["DivisionRing"],
                         {"Ring", "DivInvMonoid", "Nontrivial"})
        self.assertEqual(edges["Semigroup"], {"Mul"}, "same-line form still works")
        self.assertNotIn("Mul", edges, "a class extending nothing has no entry")
        self.assertEqual(arity["DivisionRing"], 1)


class Signatures(unittest.TestCase):
    """Rendering only. Lean invents binder names and writes each universe
    separately; neither is in the source and neither means anything."""

    def test_auto_binder_names_go(self):
        self.assertEqual(
            catalogue.readable("∀ {R : Type u_1} [inst_3 : Module R M], P"),
            "∀ {R : Type*} [Module R M], P")

    def test_adjacent_universes_collapse(self):
        self.assertEqual(
            catalogue.readable("∀ {F : Type u_1} {G : Type u_2}, P"),
            "∀ {F G : Type*}, P")

    def test_tex_specials_are_escaped(self):
        self.assertNotIn("_", catalogue.escape("Nat.succ_le").replace("\\_", ""))


class Density(unittest.TestCase):
    """Per-area yield rests on a chi-square tail and a rank correlation, both
    written here because this repository has no dependencies. A statistic
    nobody has checked against a known value is a decoration."""

    def test_the_chi_square_tail_matches_published_critical_values(self):
        """Five points from the 5% column of any chi-square table. An
        approximation good enough for a headline is not good enough here: the
        homogeneity p-value is quoted in the paper."""
        for df, critical in ((1, 3.8415), (2, 5.9915), (5, 11.070),
                             (10, 18.307), (20, 31.410)):
            self.assertAlmostEqual(density.gammaincc(df / 2, critical / 2),
                                   0.05, places=4, msg=f"df={df}")

    def test_identical_areas_are_homogeneous(self):
        g, df, p = density.homogeneity([(10, 1000)] * 3)
        self.assertAlmostEqual(g, 0.0, places=9)
        self.assertEqual(df, 2)
        self.assertAlmostEqual(p, 1.0, places=9)

    def test_opposite_areas_are_not(self):
        g, _, p = density.homogeneity([(0, 500), (100, 500)])
        self.assertGreater(g, 100)
        self.assertLess(p, 1e-20)

    def test_an_area_with_no_hits_at_all_cannot_be_tested(self):
        """Every cell zero means no rate to compare, not a significant result."""
        self.assertEqual(density.homogeneity([(0, 100), (0, 200)]), (0.0, 0, 1.0))

    def test_rank_correlation_handles_ties(self):
        """Several areas share a shot count, so ties are the normal case and
        not an edge one."""
        self.assertAlmostEqual(density.spearman([1, 2, 3, 4], [10, 20, 30, 40]), 1.0)
        self.assertAlmostEqual(density.spearman([1, 2, 3, 4], [40, 30, 20, 10]), -1.0)
        self.assertAlmostEqual(density.spearman([1, 2, 3, 4], [10, 20, 20, 40]),
                               0.9487, places=3)

    def test_a_constant_column_correlates_with_nothing(self):
        """Not 1.0, and not a ZeroDivisionError."""
        self.assertEqual(density.spearman([1, 2, 3], [5, 5, 5]), 0.0)

    def test_the_two_published_tables_are_different_instruments(self):
        """They were not, once. A glob written to mean the hand-table sweeps
        also matched the derived-table store, so the cross-table agreement was
        one instrument against a union of both. The counts differ per area,
        which is the cheapest available evidence that two sweeps are in fact
        two."""
        derived = {r["area"]: r for r in
                   density.read_rows(ROOT / "data" / "areas-derived.csv")}
        hand = {r["area"]: r for r in
                density.read_rows(ROOT / "data" / "areas-hand.csv")}
        shared = set(derived) & set(hand)
        self.assertGreaterEqual(len(shared), 5)
        # Not "no area coincides": a tiny area legitimately can. Condensed has
        # four declarations and twelve attempts under both tables, which is a
        # coincidence rather than a copy, and asserting otherwise failed the
        # day the sweep finished. What must hold is that the two files disagree
        # broadly -- a copy would agree everywhere.
        identical = [a for a in shared
                     if derived[a]["attempts"] == hand[a]["attempts"]]
        self.assertLess(len(identical), len(shared) / 2,
                        f"{len(identical)} of {len(shared)} areas have identical "
                        f"attempt counts, so one file is likely a copy of the "
                        f"other or a superset of it")
        for area in identical:
            self.assertLessEqual(derived[area]["decls"], 50,
                                 f"{area} matches on attempts and is not small, "
                                 f"which is not a coincidence")

    def test_a_break_ships_the_source_that_failed(self):
        """breaks.jsonl.gz attached the *holding* attempt's source to the
        *failing* row, so for exactly the rows a consumer needs -- a binder that
        both held and broke -- the failing compile had no source and the row was
        actively misleading. Found by a downstream project that had to rebuild
        them by hand. Each row now declares which class its source carries."""
        import gzip
        rows = [json.loads(l) for l in
                gzip.open(ROOT / "data" / "breaks.jsonl.gz", "rt", encoding="utf-8")]
        self.assertGreater(len(rows), 1000)
        wrong = [r for r in rows if r["source_class"] not in r["source"]]
        self.assertEqual(wrong, [], f"{len(wrong)} rows carry a source that does "
                                    f"not contain the class they say it does")
        both = [r for r in rows if r.get("hold_class")]
        self.assertGreater(len(both), 0)
        for r in both:
            self.assertEqual(r["source_class"], r["fails_at"],
                             f"{r['theorem']}: the shipped source is not the "
                             f"failing one")

    def test_the_published_counts_replay_the_published_statistic(self):
        """The stores are not published, so the tool that produced the headline
        must run against what is. If this fails, the repository is quoting a
        number nobody outside it can recompute."""
        rows = density.read_rows(ROOT / "data" / "areas-derived.csv")
        complete = [r for r in rows if not r["todo"] and r["decls"] >= 50]
        self.assertGreaterEqual(len(complete), 5, "too few areas to test")
        _, df, p = density.homogeneity([(r["hits"], r["decls"]) for r in complete])
        self.assertEqual(df, len(complete) - 1)
        self.assertLess(p, 0.001, "one rate now explains every area; the claim "
                                  "in FINDINGS and the paper has changed")

    def test_the_student_t_tail_matches_published_critical_values(self):
        """Seven points from the 5% column of any t table. The first version of
        this function returned negative p-values at every df above 1, and a
        check against a single critical value would have been at df = 1."""
        for df, critical in ((1, 12.706), (2, 4.303), (5, 2.571), (10, 2.228),
                             (20, 2.086), (30, 2.042), (100, 1.984)):
            self.assertAlmostEqual(
                density.betainc(df / 2, 0.5, df / (df + critical * critical)),
                0.05, places=4, msg=f"df={df}")

    def test_an_area_that_found_nothing_is_kept_and_not_divided_by(self):
        """An area at zero is a real measurement and belongs in the table. It
        is not a denominator: the first empty area crashed the macro pass on
        the spread, because a ratio against zero is not a number."""
        rows = density.read_rows(ROOT / "data" / "areas-derived.csv")
        empty = [r for r in rows if r["hits"] == 0 and not r["todo"]]
        self.assertTrue(empty, "no empty area in the published counts; this "
                               "test has stopped covering the case it was "
                               "written for")
        for row in empty:
            self.assertEqual(row["rate"], 0.0)
            self.assertGreater(row["decls"], 0, "an area with no declarations "
                                                "was not asked, not answered")

    def test_a_correlation_of_zero_is_not_evidence(self):
        self.assertAlmostEqual(density.spearman_p(0.0, 10), 1.0, places=6)

    def test_the_ranking_does_not_track_the_shot_count(self):
        """The first objection to the ranking, answered from published data.
        Near +1 would mean it is a picture of the weakening table."""
        complete = [r for r in density.read_rows(ROOT / "data" / "areas-derived.csv")
                    if not r["todo"] and r["decls"] >= 50]
        rho = density.spearman([r["rate"] for r in complete],
                               [r["shots"] for r in complete])
        self.assertLess(rho, 0.4, f"rate now tracks shots at {rho:+.2f}; the "
                                  f"ranking may be a picture of the weakening "
                                  f"table rather than of the library")

    def test_the_two_instruments_agree_on_the_order(self):
        derived = [r for r in density.read_rows(ROOT / "data" / "areas-derived.csv")
                   if not r["todo"] and r["decls"] >= 50]
        hand = {r["area"]: r for r
                in density.read_rows(ROOT / "data" / "areas-hand.csv")
                if not r["todo"] and r["decls"] >= 50}
        shared = [r for r in derived if r["area"] in hand]
        self.assertGreaterEqual(len(shared), 5)
        rho = density.spearman([r["rate"] for r in shared],
                               [hand[r["area"]]["rate"] for r in shared])
        # Published at +0.73. The threshold sits well below it because the
        # test exists to catch the claim breaking, not to pin a third decimal.
        self.assertGreater(rho, 0.5, f"the orders no longer agree ({rho:+.2f}); "
                                     f"the ranking would be the instrument's "
                                     f"rather than the library's, and the "
                                     f"README says otherwise")

    def test_rates_are_recomputed_not_read(self):
        """A rate column in the CSV would be a second copy of the truth. There
        is none: the file carries integers and everything else is derived."""
        import csv as _csv
        with (ROOT / "data" / "areas-derived.csv").open(encoding="utf-8") as h:
            header = next(_csv.reader(h))
        self.assertEqual(header, list(density.FIELDS))
        for banned in ("rate", "per_1k", "percent"):
            self.assertNotIn(banned, header)

    def test_an_empty_glob_raises_here_too(self):
        """The repository's own failure mode, in the newest tool."""
        with self.assertRaises(SystemExit):
            density.considered(str(ROOT / "no-such-directory" / "*.db"))


class EmptyIsNotZero(unittest.TestCase):
    """The shape of every defect here: something that resolved nothing looked
    exactly like something that contained nothing."""

    def test_a_glob_matching_no_store_raises(self):
        with self.assertRaises(SystemExit):
            catalogue.survivors(str(ROOT / "no-such-directory" / "*.db"))


class PublishedData(unittest.TestCase):
    """The data must agree with itself, and every row must be checkable."""

    @classmethod
    def setUpClass(cls):
        data = ROOT / "data"
        cls.rows = [json.loads(l) for l
                    in (data / "survivors.jsonl").read_text(encoding="utf-8").splitlines()
                    if l.strip()]
        cls.manifest = json.loads((data / "MANIFEST.json").read_text(encoding="utf-8"))

    def test_counts_agree(self):
        self.assertEqual(len(self.rows), self.manifest["survivors"])

    def test_every_row_can_be_recompiled(self):
        for row in self.rows:
            self.assertTrue(row["source"].strip(), f"{row['theorem']} has no source")
            self.assertIn(f"w{row['id']}", row["source"],
                          f"{row['theorem']}: source does not declare its own id, so "
                          f"`#print axioms` would name something else")

    def test_every_row_proves_the_class_it_publishes(self):
        """`holds_over` was the descent's floor while `source` sat one step
        above it, so 43 rows recompiled a weaker statement than the table
        printed -- ten of them among the eleven deepest, which are the rows the
        invertibility argument is built from. verify.py reported PASS on all of
        them. Recompiling proves something; this asserts it is the advertised
        something."""
        import verify
        wrong = [(r["theorem"], why) for r in self.rows
                 if (why := verify.claims_what_it_proves(r))]
        self.assertEqual(wrong, [], f"{len(wrong)} rows publish a class absent "
                                    f"from their own source")

    def test_the_selfcheck_refuses_an_empty_export(self):
        """Zero equals zero equals zero, no duplicate ids, no blank source: an
        empty export passes every other consistency check. It once printed
        'ok 0 rows' over data that had just been overwritten with nothing."""
        import contextlib
        import io
        import verify
        with contextlib.redirect_stdout(io.StringIO()) as noise:
            result = verify.selfcheck(ROOT / "data", {"survivors": 0}, [])
        self.assertEqual(result, 1)
        self.assertIn("empty", noise.getvalue(),
                      "it failed, but not for the reason that matters")

    def test_no_tool_imports_the_private_modules(self):
        """The public copies import leanrun where the private originals import a
        differently named module. A copied file that still imports the private
        name fails only at runtime, in a stage a stranger reaches after an hour
        of compiling. Four tools drifted from their originals at once and this
        is the cheap half of the check."""
        import pathlib
        # Assembled rather than written out: these are the names of a private
        # sibling project and its driver, and a deny-list is a poor reason to
        # publish them. The test is unaffected -- it scans tools/, not itself.
        private_names = ("scrutin" + "ize", "concl" + "ave", "/Users" + "/")
        for path in sorted((ROOT / "tools").glob("*.py")):
            text = path.read_text(encoding="utf-8")
            for private in private_names:
                self.assertNotIn(private, text,
                                 f"{path.name} references {private!r}")

    def test_the_export_columns_match_the_shipped_csv(self):
        """export.py once had eight columns while data/survivors.csv had nine,
        because the public copy of the tool was a revision behind the data it
        was supposed to have produced."""
        import csv as _csv
        import export
        with (ROOT / "data" / "survivors.csv").open(encoding="utf-8") as h:
            header = next(_csv.reader(h))
        self.assertEqual(header, export.COLUMNS,
                         "the shipped CSV and the shipping tool disagree on columns")

    def test_a_store_list_matching_nothing_raises(self):
        """The empty-glob guard lived in this copy of catalogue.py and never
        landed in the private one, so the export ran there with no guard and
        wrote an empty artifact. Comma-separated lists go through the same
        check as a single pattern."""
        with self.assertRaises(SystemExit):
            catalogue.survivors(str(ROOT / "nope-*.db") + ", " +
                                str(ROOT / "also-nope-*.db"))

    def test_the_verifier_output_matches_the_published_rows(self):
        """verified.txt is the artifact's central claim in a file. If it counts
        a different number of rows than the data holds, one of them is stale and
        a reader cannot tell which."""
        text = (ROOT / "data" / "verified.txt").read_text(encoding="utf-8")
        lines = [l for l in text.splitlines() if l.startswith(("PASS", "FAIL"))]
        self.assertEqual(len(lines), len(self.rows),
                         "verified.txt and survivors.jsonl disagree on row count")
        import re
        tally = re.search(r"(\d+) of (\d+) verified, (\d+) failed", text)
        self.assertIsNotNone(tally, "verified.txt has no summary line")
        passed, total, failed = (int(g) for g in tally.groups())
        self.assertEqual(total, len(self.rows))
        self.assertEqual(passed + failed, total)
        self.assertEqual(failed, sum(1 for l in lines if l.startswith("FAIL")))

    def test_every_unreproduced_row_is_published_not_dropped(self):
        """A row the verifier rejects is still evidence, and deleting it makes
        the artifact look cleaner than the work was."""
        import csv as _csv
        with (ROOT / "data" / "unreproduced.csv").open(encoding="utf-8") as h:
            listed = {r["theorem"] for r in _csv.DictReader(h)}
        failed = {l.split(None, 2)[1] for l
                  in (ROOT / "data" / "verified.txt").read_text(encoding="utf-8").splitlines()
                  if l.startswith("FAIL")}
        self.assertEqual(listed, failed,
                         "the failures in verified.txt and the rows in "
                         "unreproduced.csv are not the same set")

    def test_borrowed_numbers_stay_marked_until_they_are_ours(self):
        """The paper quotes a figure measured by another project. Two colours,
        two meanings: red marks something believed wrong, orange marks something
        believed right and not yet in hand. A borrowed number must carry its
        marker until the merged data lands here, because a figure that arrives
        by email and loses its box reads exactly like one we computed."""
        tex = (ROOT / "paper" / "note.tex").read_text(encoding="utf-8")
        borrowed = "99.15" in tex
        marked = "Pending: a second measurement" in tex
        joined = (ROOT / "data" / "root-invariance.jsonl").exists()
        if joined:
            # The join must actually be a join, and the impossible cell must
            # still be empty: a moved root with an unchanged citation set would
            # mean one of the two pipelines is wrong.
            rows = [json.loads(l) for l
                    in (ROOT / "data" / "root-invariance.jsonl")
                    .read_text(encoding="utf-8").splitlines() if l.strip()]
            impossible = [r for r in rows
                          if r.get("root_moved") and r["cited_set_verdict"] == "unused"]
            self.assertEqual(impossible, [],
                             f"{len(impossible)} rows have a moved proof-term root "
                             f"and an unchanged citation set, which cannot both be "
                             f"true; one of the two measurements is wrong")
        if borrowed:
            self.assertTrue(marked or joined,
                            "the paper quotes 99.15% without the pending box "
                            "and without data/root-invariance.jsonl to back it; "
                            "either restore the marker or ship the joined data")

    def test_the_paper_reads_only_what_this_repository_ships(self):
        """A test that reads a sibling directory passes here and fails for
        everyone else. One did: it gated the paper's provisional-title box on a
        design note in a private repository, so a fresh clone failed a test
        about a decision it could not see. The decision is settled and the test
        is gone; this one keeps its replacement honest."""
        needle = "ROOT" + ".parent"          # not a literal, or this test finds itself
        for path in (ROOT / "tests").rglob("*.py"):
            body = path.read_text(encoding="utf-8").replace(
                '"ROOT" + ".parent"', "")
            self.assertNotIn(needle, body,
                             f"{path.name} reads outside the repository, so it "
                             "cannot pass on a clean clone")

    def test_a_revision_is_recorded(self):
        self.assertTrue(self.manifest["mathlib"]["revision"],
                        "without it every row is unfalsifiable")

    def test_no_private_paths_in_the_export(self):
        blob = json.dumps(self.rows) + json.dumps(self.manifest)
        for leak in ("/Users/", "/var/folders", "/private/"):
            self.assertNotIn(leak, blob)


class OpenDirectiveForms(unittest.TestCase):
    """`open` has several syntactic forms and only one of them chains."""

    ROW = {
        "opens": "open Module Polynomial\n"
                 "open FractionalIdeal (coeIdeal_mul)\n"
                 "open Ideal hiding map_mul\n"
                 "open scoped nonZeroDivisors",
        "namespace": "",
    }

    def _emitted(self, text):
        return [l[len("open "):].removesuffix(" in")
                for l in text.splitlines() if l.startswith("open ")]

    def test_a_selector_open_is_not_chained_with_other_namespaces(self):
        """`open A (x) B hiding y C in` does not parse, and splitting the
        directives on whitespace first turns `hiding` and the hidden name into
        namespaces of their own. Every emitted command that carries a selector
        or `hiding` must name exactly one namespace.

        24 rows of the breaks export never parsed for a consumer because of
        this. Found by the `unstated-conclusions` project, which recompiled
        them and sent back the error blocks; every one failed at the generated
        `open` line, not in the proof."""
        for opened in (verify.opened, leanrun.opened):
            for command in self._emitted(opened(self.ROW)):
                if "(" in command or " hiding " in command:
                    head = command.split("(")[0].split(" hiding ")[0]
                    self.assertEqual(
                        len(head.split()), 1,
                        f"{opened.__module__}.opened emitted {command!r}, which "
                        "chains a selector or `hiding` with other namespaces")

    def test_no_directive_is_dropped_while_separating_them(self):
        """Splitting the forms apart must not lose one. The first attempt
        classified them into a third list and never emitted it."""
        for opened in (verify.opened, leanrun.opened):
            out = opened(self.ROW)
            for name in ("Module", "Polynomial", "FractionalIdeal",
                         "coeIdeal_mul", "Ideal", "map_mul", "nonZeroDivisors"):
                self.assertIn(name, out,
                              f"{opened.__module__}.opened dropped {name}")

    def test_scoped_still_comes_last(self):
        """`open scoped sigma` resolves as `ArithmeticFunction.sigma` and is an
        unknown namespace until `ArithmeticFunction` is open."""
        for opened in (verify.opened, leanrun.opened):
            commands = self._emitted(opened(self.ROW))
            scoped = [i for i, c in enumerate(commands) if c.startswith("scoped")]
            plain = [i for i, c in enumerate(commands) if not c.startswith("scoped")]
            self.assertTrue(min(scoped) > max(plain),
                            f"{opened.__module__}.opened put a scoped clause "
                            "before a plain one")


class Verifier(unittest.TestCase):
    """It decides what counts as verified, so its own predicates are worth
    pinning down."""

    def test_wait_for_memory_can_actually_wait(self):
        """It calls json.dumps and time.sleep, and leanrun imported neither.
        Six tools call it. The bug never fired because available_gb() normally
        clears the threshold on the first poll, so the loop is never entered --
        a code path that never runs looks exactly like one that works. Found by
        a downstream project that runs it against a live sweep, where memory is
        tight and the loop does get entered."""
        import leanrun
        with self.assertRaises(SystemExit):
            # Force the loop with an unreachable threshold and no patience.
            def stop(*_a, **_k):
                raise SystemExit
            real_sleep, leanrun.time.sleep = leanrun.time.sleep, stop
            try:
                leanrun.wait_for_memory(minimum_gb=10 ** 9, poll=0)
            finally:
                leanrun.time.sleep = real_sleep

    def test_leanrun_and_verify_agree_on_clause_order(self):
        """verify.py was corrected to emit the plain clause before the scoped
        one; leanrun.py kept the old order, masked because the sweep also emits
        every directive raw. Two copies of one rule is how it drifted."""
        import leanrun
        row = {"opens": "open Lean SubExpr\nopen scoped Pointwise",
               "namespace": "A.B"}
        self.assertEqual(leanrun.opened(row), verify.opened(row))

    def test_scope_is_bound_to_the_declaration_not_the_file(self):
        """Bare `open` commands are file-scoped and permanent, and bring enough
        into scope to create ambiguities the scoped form does not.
        SetLike.lt_iff_le_and_exists compiles under `open ... in` and dies under
        bare opens on an ambiguous `instSubtypeSet`; it was written up as an
        unreproducible row for a day. `open scoped` cannot be folded into the
        same clause and stays its own command."""
        text = verify.opened({"opens": "open Lean SubExpr\nopen scoped Pointwise",
                              "namespace": "A.B"})
        for line in text.splitlines():
            self.assertTrue(line.endswith(" in"),
                            f"{line!r} is a bare open and leaks to the whole file")
        self.assertIn("open scoped Pointwise in", text)
        lines = text.splitlines()
        names = [l for l in lines if not l.startswith("open scoped")][0]
        for wanted in ("Lean", "SubExpr", "A", "A.B"):
            self.assertIn(wanted, names)
        # Plain before scoped. A scoped notation namespace is often reachable
        # only through one of the plain ones: `open scoped sigma` resolves as
        # ArithmeticFunction.sigma and is unknown until ArithmeticFunction is
        # open. Emitting scoped first cost a row that had compiled for weeks.
        self.assertLess(lines.index(names),
                        lines.index("open scoped Pointwise in"),
                        "scoped clause emitted before the plain one; a scoped "
                        "namespace reachable only through a plain one will not "
                        "resolve")

    def test_the_directives_are_not_also_emitted_raw(self):
        """source_for once emitted row["opens"] as bare commands *and* passed
        them to opened(). The duplicate is what leaked."""
        row = {"id": "x", "opens": "open Lean", "namespace": "", "source": "theorem wx : True := trivial"}
        text = verify.source_for(row)
        self.assertEqual(text.count("open Lean"), 1, "the directives appear twice")
        self.assertIn("open Lean in", text)

    def test_the_verifier_mirrors_the_sweep_two_shot_procedure(self):
        """The sweep compiles with the file's `open` directives and retries
        without them on a context error, because some directives name a
        notation namespace that does not resolve outside their own file. The
        store records nothing about which attempt won. A verifier that always
        includes them fails rows the sweep passed, for a reason that is about
        our preamble rather than about the weakening.

        Checked without Lean: the second attempt must be made, and must be made
        on a row whose directives have been stripped."""
        seen = []

        def fake(repo, row, timeout):
            seen.append(row.get("opens", ""))
            return (len(seen) > 1, "ok" if len(seen) > 1 else "context error")

        original = verify.attempt
        verify.attempt = fake
        try:
            ok, why = verify.check(None, {"opens": "open Foo\nopen scoped Bar",
                                          "holds_over": "X", "source": "X",
                                          "binder": "[X a]"}, 1)
        finally:
            verify.attempt = original
        self.assertTrue(ok, "the retry without directives was never made")
        self.assertEqual(len(seen), 2)
        self.assertEqual(seen[1], "", "the retry kept the directives")
        self.assertIn("without", why, "a row needing the retry should say so")

    def test_a_row_with_no_directives_is_not_retried(self):
        """Nothing to strip, so a second identical compile would only cost
        time and would report a failure twice."""
        calls = []

        def fake(repo, row, timeout):
            calls.append(1)
            return (False, "genuine failure")

        original = verify.attempt
        verify.attempt = fake
        try:
            ok, _ = verify.check(None, {"opens": "", "holds_over": "X",
                                        "source": "X", "binder": "[X a]"}, 1)
        finally:
            verify.attempt = original
        self.assertFalse(ok)
        self.assertEqual(len(calls), 1, "retried a row that had nothing to retry")

    def test_tagged_errors_are_caught(self):
        """A scan for the literal `error:` reads a file full of instance
        failures as clean."""
        self.assertTrue(verify.ERROR_RE.search("error(lean.synthInstanceFailed): x"))

    def test_warnings_are_not_errors(self):
        self.assertIsNone(verify.ERROR_RE.search("warning: unused variable `h`"))

    def test_fewer_axioms_is_still_clean(self):
        """A proof avoiding Classical.choice prints two axioms and is better
        for it. Demanding all three failed a good row."""
        match = verify.AXIOMS_RE.search("'w1' depends on axioms: [propext, Quot.sound]")
        used = {a.strip() for a in match.group("axioms").split(",")}
        self.assertTrue(used <= verify.STANDARD_AXIOMS)

    def test_no_axioms_at_all_is_the_cleanest_result(self):
        """Lean spells this one differently and it is not a list. 40 of 645
        published rows were reported as failures by a verifier that could only
        recognise the "depends on axioms: [...]" form -- every one of them a
        proof needing nothing at all, which is better than the standard three,
        not worse. The second time this check has been strict in the wrong
        direction; the first demanded all three and failed proofs using two."""
        match = verify.AXIOMS_RE.search("'w1' does not depend on any axioms")
        self.assertIsNotNone(match, "the cleanest possible proof was unreadable")
        self.assertTrue(match.group("none"))
        used = set() if match.group("none") else {
            a.strip() for a in (match.group("axioms") or "").split(",")}
        self.assertEqual(used, set())
        self.assertTrue(used <= verify.STANDARD_AXIOMS)

    def test_sorry_is_not_clean(self):
        match = verify.AXIOMS_RE.search("'w1' depends on axioms: [propext, sorryAx]")
        used = {a.strip() for a in match.group("axioms").split(",")}
        self.assertFalse(used <= verify.STANDARD_AXIOMS)


if __name__ == "__main__":
    unittest.main(verbosity=2)
