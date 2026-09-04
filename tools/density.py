#!/usr/bin/env python3
"""How dense is the phenomenon, per area, and is that density the same everywhere?

Counting survivors rewards big areas for being big. Algebra leads every table in
this project, and Algebra is also the largest thing swept. The question worth
asking is whether a theorem in Algebra is *more likely* to carry an unused
assumption than a theorem in Order, and that needs a denominator.

Three are available and they answer different questions.

**Files** is area size as a human means it, and it is the only denominator
independent of the weakening table. It is also the worst of the three: files
differ in length by an order of magnitude, and a file of definitions offers the
sweep nothing to try.

**Declarations considered** -- distinct theorems for which at least one
weakening was proposed -- is the denominator for the claim about the library.
It is table-dependent, because a theorem whose classes the table cannot weaken
never enters the store at all. Comparing this rate across two tables is
meaningless; comparing areas under one table is exactly what it is for.

`reach` -- declarations considered per file -- separates an area the method
cannot ask about from one it asked and found nothing in. Those are different
results and a rate alone conflates them.

**Attempts** measures the instrument, not the library. A table with more edges
per class produces more attempts per theorem and a lower rate at identical
yield. Reported because it is the cost side of the engineering claim.

The headline rate is `hits / declarations`, where a hit is a theorem with at
least one surviving weakening. Not findings/declarations: a theorem can yield
three findings, so findings are not Bernoulli trials and an interval computed
over them would be too narrow. Findings are reported beside it as a count.

The homogeneity test asks whether one rate explains every area. If it does, the
phenomenon is a property of formalisation rather than of a subject, which is
the more interesting answer and the one that makes the sweep's coverage matter.

The first objection to any ranking here is that a dense area simply got more
shots: more edges apply to its classes, so more attempts per declaration, so
more chances to hit. `shots` is printed beside the rate to answer that without
a second run. If the densest areas are also the ones with the most attempts per
declaration, the ranking is measuring the table and should be thrown away.
"""

from __future__ import annotations

import argparse
import collections
import csv
import glob
import math
import sqlite3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from catalogue import area_of, survivors, full_name
from compare import wilson


def gammaincc(a: float, x: float) -> float:
    """Regularized upper incomplete gamma, so a p-value needs no scipy.

    Series below the crossover, continued fraction above, as in Numerical
    Recipes. This repository has no dependencies and a chi-square tail is not a
    good reason to acquire one.
    """
    if x <= 0:
        return 1.0
    if x < a + 1:
        term, total = 1.0 / a, 1.0 / a
        for n in range(1, 300):
            term *= x / (a + n)
            total += term
            if abs(term) < abs(total) * 1e-14:
                break
        return 1.0 - total * math.exp(-x + a * math.log(x) - math.lgamma(a))
    tiny = 1e-300
    b, c, d = x + 1 - a, 1 / tiny, 1 / (x + 1 - a)
    h = d
    for i in range(1, 300):
        an = -i * (i - a)
        b += 2
        d = an * d + b
        if abs(d) < tiny:
            d = tiny
        c = b + an / c
        if abs(c) < tiny:
            c = tiny
        d = 1 / d
        step = d * c
        h *= step
        if abs(step - 1) < 1e-14:
            break
    return h * math.exp(-x + a * math.log(x) - math.lgamma(a))


def betainc(a: float, b: float, x: float) -> float:
    """Regularized incomplete beta, for a Student t tail.

    Same reasoning as the chi-square tail above: a correlation quoted as
    evidence needs a p-value, and a p-value is not a good enough reason to
    acquire a dependency.

    Two things the first attempt got wrong, both invisible at df = 1 and both
    caught by checking five critical values instead of one. The guard against a
    vanishing denominator must substitute the floor and *then* invert, so the
    reciprocal comes out large; returning the floor itself flips the sign of
    everything downstream. And the recurrence takes two half-steps per
    iteration, which do not collapse into one loop over `i // 2`.
    """
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    front = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
                     + a * math.log(x) + b * math.log(1 - x))
    if x > (a + 1) / (a + b + 2):
        return 1.0 - betainc(b, a, 1 - x)

    tiny = 1e-300
    c = 1.0
    d = 1.0 - (a + b) * x / (a + 1)
    if abs(d) < tiny:
        d = tiny
    d = 1.0 / d
    h = d
    for m in range(1, 300):
        m2 = 2 * m
        for num in (m * (b - m) * x / ((a - 1 + m2) * (a + m2)),
                    -(a + m) * (a + b + m) * x / ((a + m2) * (a + 1 + m2))):
            d = 1.0 + num * d
            if abs(d) < tiny:
                d = tiny
            d = 1.0 / d
            c = 1.0 + num / c
            if abs(c) < tiny:
                c = tiny
            h *= d * c
        if abs(d * c - 1.0) < 1e-14:
            break
    return front * h / a


def spearman_p(rho: float, n: int) -> float:
    """Two-sided p for a rank correlation, by the usual t approximation.

    Approximate at these sample sizes -- ten areas is ten -- and quoted to one
    significant figure for that reason. It is here so that "the orders agree"
    is a claim with a number attached rather than a look at two columns.
    """
    if n < 4 or abs(rho) >= 1:
        return 0.0 if abs(rho) >= 1 and n >= 4 else 1.0
    t = rho * math.sqrt((n - 2) / (1 - rho * rho))
    df = n - 2
    return betainc(df / 2, 0.5, df / (df + t * t))


def design_effect(modules: int, hit_modules: int, hit_sq: int, hits: int) -> float:
    """How much a file's worth of shared hypotheses inflates the G statistic.

    Mathlib writes `variable [Field K]` at the head of a file and every theorem
    below inherits it, so the thing being weakened is a property of the file at
    least as much as of the theorem. Counting theorems as independent trials
    therefore overstates the evidence, and the G statistic is too large by
    roughly the ratio of the observed variance in hits-per-file to the variance
    a Poisson process would give.

    This is the same mistake as counting rows instead of findings, one level up.
    Moving from survivors to theorems was right and was not far enough.

    Returns 1.0 when there is nothing to correct, so an uncorrected caller and a
    corrected one agree on data with no clustering.
    """
    if modules <= 0 or hits <= 0:
        return 1.0
    mean = hits / modules
    variance = hit_sq / modules - mean * mean
    return max(1.0, variance / mean) if mean else 1.0


def homogeneity(counts: list[tuple[int, int]], deff: float = 1.0
                ) -> tuple[float, int, float]:
    """G-test: does one pooled rate explain every area's hits?

    `deff` divides the statistic, which is the Rao-Scott correction in its
    simplest form. Pass the design effect from `design_effect` to get the test
    the data supports rather than the one that assumes theorems are independent.

    The likelihood-ratio form rather than Pearson's, because several areas have
    single-figure expected counts and G behaves better there. Cells with zero
    observed contribute nothing, which is the standard convention and the reason
    an area with no survivors at all cannot by itself produce significance.
    """
    hits = sum(h for h, _ in counts)
    total = sum(n for _, n in counts)
    if not total or not hits or hits == total:
        return (0.0, 0, 1.0)
    p = hits / total
    g = 0.0
    for hit, n in counts:
        for observed, expected in ((hit, n * p), (n - hit, n * (1 - p))):
            if observed > 0 and expected > 0:
                g += 2 * observed * math.log(observed / expected)
    df = len(counts) - 1
    g /= deff
    return (g, df, gammaincc(df / 2, g / 2))


def spearman(left: list[float], right: list[float]) -> float:
    """Rank correlation, to check the ranking against the obvious confound.

    Ranks rather than values because both quantities are bounded and skewed,
    and because the question is only whether the two orderings agree. Ties get
    their average rank, which matters here: several areas sit at the same shot
    count.
    """
    def ranked(values: list[float]) -> list[float]:
        order = sorted(range(len(values)), key=lambda i: values[i])
        out = [0.0] * len(values)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and values[order[j + 1]] == values[order[i]]:
                j += 1
            share = (i + j) / 2 + 1
            for k in range(i, j + 1):
                out[order[k]] = share
            i = j + 1
        return out

    a, b = ranked(left), ranked(right)
    n = len(a)
    mean_a, mean_b = sum(a) / n, sum(b) / n
    top = sum((x - mean_a) * (y - mean_b) for x, y in zip(a, b))
    scale = math.sqrt(sum((x - mean_a) ** 2 for x in a)
                      * sum((y - mean_b) ** 2 for y in b))
    return top / scale if scale else 0.0


def files_per_area(source: Path) -> dict[str, int]:
    """Area size as a human means it, counted from the library rather than the
    store, so an area the sweep never reached still has a denominator."""
    sizes: collections.Counter = collections.Counter()
    root = source / "Mathlib"
    for path in root.rglob("*.lean"):
        relative = path.relative_to(root).parts
        # Two files sit directly in Mathlib/ and belong to no area. They are
        # counted under a name of their own rather than dropped, so this total
        # matches note_tables' library count instead of falling two short --
        # the two tools disagreed by exactly those two files, which made the
        # note's swept and unswept figures fail to add up.
        sizes[relative[0] if len(relative) > 1 else "(root)"] += 1
    return dict(sizes)


def stores_for(pattern: str) -> list[str]:
    """The stores a pattern names, printed by every caller before use.

    Comma-separated patterns, because the alternative is a clever glob and a
    clever glob is how this tool first went wrong: `s[wp]*.db` was written to
    mean the two hand-table sweeps and quietly also matched `sprint-3.db`, the
    derived-table store it was being compared against. The comparison ran, the
    numbers looked plausible, and one instrument was being compared with a
    union of both.

    So the fix is not a better pattern. It is that the store list is an output:
    a glob that matches too much looks exactly like a glob that matches right,
    and the only defence is printing what was read.
    """
    found: list[str] = []
    for part in pattern.split(","):
        found += sorted(glob.glob(part.strip()))
    return [s for s in dict.fromkeys(found)
            if "-before-" not in s and "-artefact" not in s]


def considered(pattern: str) -> dict[str, dict]:
    """Attempts and distinct declarations per area, plus what is still undecided.

    Reads every store the pattern names, including ones a sweep is still
    writing. A partial area is reported as partial rather than dropped: seeing
    that Order is at 41% is more use than seeing nothing.
    """
    seen: dict[str, dict] = collections.defaultdict(
        lambda: {"attempts": 0, "decls": set(), "todo": 0})
    stores = stores_for(pattern)
    if not stores:
        raise SystemExit(f"no store matched {pattern!r} -- nothing to measure. "
                         f"An empty glob is not an empty result.")
    for store in stores:
        link = sqlite3.connect(f"file:{store}?mode=ro", uri=True)
        for module, theorem, todo, rows in link.execute(
                "SELECT module, theorem, SUM(verdict IS NULL), COUNT(*) "
                "FROM weakening WHERE module LIKE 'Mathlib.%' "
                "GROUP BY module, theorem"):
            entry = seen[area_of(module)]
            entry["attempts"] += rows
            entry["decls"].add((module, theorem))
            entry["todo"] += todo
        link.close()
    return seen


def measure(pattern: str, sizes: dict[str, int], label: str = "") -> list[dict]:
    """Every area's counts under one instrument.

    Names the stores it read. One instrument means one weakening table, and
    nothing in a store records which table produced it -- that lives in how the
    sweep was invoked. The store list is therefore the only evidence that a
    comparison is between two instruments rather than between one and a union,
    and it belongs in the output rather than in the caller's memory.
    """
    stores = stores_for(pattern)
    print(f"  {label or 'reading'}: {', '.join(Path(s).name for s in stores)}")
    pool = considered(pattern)
    findings: collections.Counter = collections.Counter()
    hits: dict[str, set] = collections.defaultdict(set)
    seen: dict[tuple, dict] = {}
    for store in stores:
        for row in survivors(store):
            seen.setdefault((row["module"], row["theorem"], row["binder"]), row)
    for row in seen.values():
        area = area_of(row["module"])
        findings[area] += 1
        hits[area].add((row["module"], full_name(row)))

    per_module: dict[str, collections.Counter] = collections.defaultdict(
        collections.Counter)
    for area, keys in hits.items():
        for module, _ in keys:
            per_module[area][module] += 1

    rows = []
    for area, entry in pool.items():
        decls = len(entry["decls"])
        counts = per_module.get(area, collections.Counter())
        rows.append({
            "modules": len({m for (m, _) in entry["decls"]}),
            "hit_modules": len(counts),
            "hit_sq": sum(v * v for v in counts.values()),
            "area": area,
            "files": sizes.get(area, 0),
            "decls": decls,
            "attempts": entry["attempts"],
            "todo": entry["todo"],
            "hits": len(hits.get(area, ())),
            "findings": findings.get(area, 0),
            "rate": len(hits.get(area, ())) / decls if decls else 0.0,
            "shots": entry["attempts"] / decls if decls else 0.0,
            "reach": decls / sizes[area] if sizes.get(area) else 0.0,
            "per_attempt": (findings.get(area, 0) / entry["attempts"]
                            if entry["attempts"] else 0.0),
        })
    rows.sort(key=lambda r: r["rate"], reverse=True)
    return rows


FIELDS = ("area", "files", "decls", "attempts", "hits", "findings", "todo",
          "modules", "hit_modules", "hit_sq")


def write_rows(rows: list[dict], path: Path) -> None:
    """Publish the per-area counts, so the headline can be rechecked without
    the stores.

    The stores are gigabytes of compile results and are not published. A tool
    that ships beside the data and cannot run against the data is the failure
    this project keeps finding in itself, so the counts the test consumes are
    exported and the test can read them back.
    """
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row[key] for key in FIELDS})


def read_rows(path: Path, sizes: dict[str, int] | None = None) -> list[dict]:
    """The counts as published, with the rates recomputed rather than trusted.

    Only the integers are read back. Every rate, interval and statistic is
    derived here, so a hand-edited percentage in the CSV would change nothing
    and a hand-edited count would change the p-value -- which is the right way
    round for a file that exists to be checked.
    """
    rows = []
    with path.open(encoding="utf-8") as handle:
        for raw in csv.DictReader(handle):
            row = {key: int(raw[key]) for key in FIELDS if key != "area"}
            row["area"] = raw["area"]
            if sizes:
                row["files"] = sizes.get(row["area"], row["files"])
            decls = row["decls"]
            row["rate"] = row["hits"] / decls if decls else 0.0
            row["shots"] = row["attempts"] / decls if decls else 0.0
            row["reach"] = decls / row["files"] if row["files"] else 0.0
            row["per_attempt"] = (row["findings"] / row["attempts"]
                                  if row["attempts"] else 0.0)
            rows.append(row)
    rows.sort(key=lambda r: r["rate"], reverse=True)
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stores", default="scrutiny/*.db")
    parser.add_argument("--source", type=Path,
                        help="a Mathlib checkout, for the file counts. Not "
                             "needed with --from, which carries them")
    parser.add_argument("--from", dest="published", type=Path,
                        help="read the counts from a published CSV instead of "
                             "the stores, so the result can be rechecked "
                             "without them")
    parser.add_argument("--emit", type=Path,
                        help="write those counts, for publication")
    parser.add_argument("--min-decls", type=int, default=50,
                        help="areas below this are listed but left out of the test")
    parser.add_argument("--against", help="a second store glob or published "
                        "CSV, swept under the other weakening table, to test "
                        "whether the ranking is a property of the library or "
                        "of the instrument")
    parser.add_argument("--macros", type=Path, help="write LaTeX macros here")
    args = parser.parse_args()

    if args.published:
        sizes = files_per_area(args.source) if args.source else {}
        rows = read_rows(args.published, sizes)
    elif args.source:
        sizes = files_per_area(args.source)
        rows = measure(args.stores, sizes, "instrument")
    else:
        raise SystemExit("give --source (to read the stores) or --from "
                         "(to read published counts)")

    print(f"{'area':<20}{'files':>6}{'decls':>7}{'attempt':>9}{'shots':>7}{'reach':>7}"
          f"{'hits':>6}{'find':>6}{'/1k decl':>10}{'95% interval':>16}{'/1k att':>9}")
    for row in rows:
        low, high = wilson(row["hits"], row["decls"])
        mark = " *" if row["todo"] else ""
        print(f"{row['area'] + mark:<20}{row['files']:>6}{row['decls']:>7}"
              f"{row['attempts']:>9}{row['shots']:>7.1f}{row['reach']:>7.1f}"
              f"{row['hits']:>6}{row['findings']:>6}"
              f"{row['rate'] * 1000:>10.1f}"
              f"{f'{low * 1000:.1f}-{high * 1000:.1f}':>16}"
              f"{row['per_attempt'] * 1000:>9.1f}")

    complete = [r for r in rows if not r["todo"] and r["decls"] >= args.min_decls]
    cells = [(r["hits"], r["decls"]) for r in complete]
    g, df, p = homogeneity(cells)
    deff = design_effect(sum(r["modules"] for r in complete),
                         sum(r["hit_modules"] for r in complete),
                         sum(r["hit_sq"] for r in complete),
                         sum(r["hits"] for r in complete))
    g_c, _, p_c = homogeneity(cells, deff)
    pooled = (sum(r["hits"] for r in complete)
              / max(1, sum(r["decls"] for r in complete)))
    print(f"\n  {len(complete)} complete areas above {args.min_decls} declarations")
    print(f"  pooled rate {pooled * 1000:.1f} per 1000 declarations")
    print(f"  G = {g:.1f}, df = {df}, p = {p:.3g}   (theorems as independent trials)")
    print(f"  G = {g_c:.1f}, df = {df}, p = {p_c:.3g}   (clustered by file, "
          f"design effect {deff:.2f})")
    print(f"  {'one rate does not explain them' if p_c < 0.05 else 'CONSISTENT WITH ONE RATE once clustering is allowed for'}"
          f" -- the clustered test is the one to quote. A file heads its theorems"
          f" with shared `variable` binders, so the")
    print(f"  weakened assumption belongs to the file at least as much as to the"
          f" theorem, and counting theorems as independent overstates the evidence.")
    if len(complete) > 2:
        confound = spearman([r["rate"] for r in complete],
                            [r["shots"] for r in complete])
        print(f"  rank correlation of rate with shots per declaration: "
              f"{confound:+.2f} (n = {len(complete)}, "
              f"p = {spearman_p(confound, len(complete)):.2g})"
              f"  -- near +1 would mean the ranking is the table, not the library")
    if any(r["todo"] for r in rows):
        print("  * area still being swept; excluded from the test")

    if args.against:
        second = Path(args.against)
        other = {r["area"]: r for r in
                 (read_rows(second, sizes) if second.suffix == ".csv"
                  else measure(args.against, sizes, "against"))}
        shared = [r for r in rows
                  if r["area"] in other and not r["todo"]
                  and not other[r["area"]]["todo"]
                  and r["decls"] >= args.min_decls
                  and other[r["area"]]["decls"] >= args.min_decls]
        print(f"\n  {len(shared)} areas complete under both instruments")
        print(f"  {'area':<20}{'this /1k':>10}{'other /1k':>11}{'ratio':>8}")
        for row in shared:
            mine, theirs = row["rate"] * 1000, other[row["area"]]["rate"] * 1000
            ratio = f"{mine / theirs:.2f}" if theirs else "--"
            print(f"  {row['area']:<20}{mine:>10.1f}{theirs:>11.1f}{ratio:>8}")
        agreement = spearman([r["rate"] for r in shared],
                             [other[r["area"]]["rate"] for r in shared])
        cross = {"densityCrossRho": f"{agreement:+.2f}",
                 "densityCrossN": str(len(shared)),
                 "densityCrossP": f"{spearman_p(agreement, len(shared)):.1g}"}
        print(f"  rank correlation between the instruments: {agreement:+.2f}"
              f"  (n = {len(shared)}, p = {spearman_p(agreement, len(shared)):.2g})")
        print("  A ranking that survives a change of table is the library's. "
              "The two tables are not fully independent -- both order the same "
              "hierarchy -- so read this as agreement, not replication.")

    if args.macros and "cross" in dir():
        pass
    if args.emit:
        write_rows(rows, args.emit)
        print(f"  counts -> {args.emit}")

    if args.macros:
        lines = [f"\\newcommand{{\\densityAreas}}{{{len(complete)}}}",
                 f"\\newcommand{{\\densityPooled}}{{{pooled * 1000:.1f}}}",
                 f"\\newcommand{{\\densityG}}{{{g:.0f}}}",
                 f"\\newcommand{{\\densityDf}}{{{df}}}",
                 f"\\newcommand{{\\densityP}}{{{p:.2g}}}",
                 f"\\newcommand{{\\densityDeff}}{{{deff:.1f}}}",
                 f"\\newcommand{{\\densityGClustered}}{{{g_c:.0f}}}",
                 f"\\newcommand{{\\densityPClustered}}{{{p_c:.1g}}}"]
        # Coverage of the library by this instrument. Counted over areas the
        # sweep touched at all, not areas that yielded something: an area
        # attempted and empty is swept, and reporting it as unswept would
        # understate the pass in the direction that flatters it.
        touched = {r["area"] for r in rows}
        covered = sum(sizes.get(a, 0) for a in touched)
        every = sum(sizes.values())
        # "(root)" is the bucket for the handful of files sitting directly in
        # Mathlib/ rather than in an area. It counts toward the total, which is
        # what makes swept and unswept add up, but it is not the name of a
        # subject and printing it in a list of areas reads as a bug.
        skipped = sorted((a for a in sizes if a not in touched and a != "(root)"),
                         key=lambda a: -sizes[a])
        lines += [f"\\newcommand{{\\sweptAreas}}{{{len(touched)}}}",
                  f"\\newcommand{{\\sweptFilesAll}}{{{covered:,}}}".replace(",", "{,}"),
                  f"\\newcommand{{\\sweptPercentAll}}{{{100 * covered / max(every, 1):.0f}}}",
                  f"\\newcommand{{\\unsweptFiles}}{{{every - covered}}}",
                  f"\\newcommand{{\\unsweptAreas}}{{{', '.join(skipped)}}}"]
        # The headline pair is the widest gap the intervals actually support,
        # not the top and bottom of the ranking. The bottom row is whichever
        # area has fewest declarations -- CategoryTheory's 279 give an interval
        # spanning a factor of thirty -- and quoting it as "the sparsest" would
        # be reading rank order as a measurement.
        #
        # The sparsest must also have found something. An area at zero is a
        # real result and belongs in the table, but "a factor of infinity" is
        # not a sentence, and the first area to come back empty crashed this
        # branch on the division. A ratio needs a denominator that exists.
        pair = None
        if complete:
            top = complete[0]
            top_low, _ = wilson(top["hits"], top["decls"])
            for candidate in reversed(complete[1:]):
                _, high = wilson(candidate["hits"], candidate["decls"])
                if candidate["hits"] and high < top_low:
                    pair = (top, candidate)
                    break
        if pair:
            for tag, row in zip(("Densest", "Sparsest"), pair):
                lines += [f"\\newcommand{{\\density{tag}}}{{{row['area']}}}",
                          f"\\newcommand{{\\density{tag}Rate}}{{{row['rate'] * 1000:.1f}}}",
                          f"\\newcommand{{\\density{tag}Decls}}{{{row['decls']}}}"]
            lines.append(f"\\newcommand{{\\densitySpread}}"
                         f"{{{pair[0]['rate'] / pair[1]['rate']:.0f}}}")
        for name, value in (locals().get("cross") or {}).items():
            lines.append(f"\\newcommand{{\\{name}}}{{{value}}}")
        args.macros.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"  macros -> {args.macros}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
