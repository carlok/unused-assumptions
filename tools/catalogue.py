#!/usr/bin/env python3
"""Every survivor, grouped and readable, rather than the four the note argues from.

The note is an argument and quotes four statements. This is the map it keeps
promising: which theorems in the library carry an assumption their own proof
never uses, what they are stated over, and what they actually need.

Two decisions worth defending.

The signature shown is the one Lean prints for the *original* theorem, not our
reconstruction of it. `needed()` builds a superset of the file-level variables a
declaration takes, which is right for compiling a candidate standalone and wrong
for showing a reader what the theorem says. Asking Lean costs one `#check` per
declaration and removes a whole class of "that is not what it says" objection.

Nothing here is filtered for interest, because the filters cannot judge it. Two
of the deepest survivors conclude an inequality in the reals whose ring
hypothesis exists only to state another hypothesis: deep by the ordinal and
empty as mathematics. A catalogue that silently dropped them would be claiming a
judgement the machine did not make, so they are present and the preamble says
so.
"""

from __future__ import annotations

import argparse
import collections
import glob
import json
import re
import sqlite3
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from triage import magnitude, reaches_conclusion, actually_weakened, UNRANKED

INVERTIBLE = {"Field", "DivisionRing", "CommRing", "Ring", "NonUnitalRing",
              "LinearOrderedField", "LinearOrderedRing", "EuclideanDomain",
              "AddCommGroup", "AddGroup", "SubNegMonoid", "CommGroup", "Group",
              "DivInvMonoid", "GroupWithZero", "NormedAddCommGroup",
              "SeminormedAddCommGroup", "NormedField", "NormedRing"}
PLAIN = {"Semiring", "CommSemiring", "NonUnitalSemiring", "MonoidWithZero",
         "CommMonoidWithZero", "MulZeroClass", "NonUnitalNonAssocSemiring",
         "AddMonoid", "AddCommMonoid", "AddZeroClass", "AddSemigroup",
         "AddCommSemigroup", "Monoid", "MulOneClass", "Semigroup", "CommSemigroup"}


def survivors(pattern: str) -> list[dict]:
    """Every gated survivor in every store, deduplicated by declaration.

    A theorem can be reached from more than one store when areas were swept by
    parallel runners, and can carry several weakenings of its own. Keyed by
    (module, theorem, binder) so a genuine second weakening of the same theorem
    survives and a duplicate sweep does not.
    """
    stores = [s for part in pattern.split(",")
              for s in sorted(glob.glob(part.strip()))]
    if not stores:
        # A glob that matches nothing must not read as a corpus containing
        # nothing. That is the failure this project has hit seven times, and
        # shipping it in the tool that documents it would be absurd: the
        # default pattern points at a directory that exists only on the machine
        # which produced the data.
        raise SystemExit(
            f"no stores matched {pattern!r}. This tool reads the sweep's own "
            f"SQLite stores, which are not published -- they are a quarter of a "
            f"gigabyte of intermediate verdicts. The published residue is in "
            f"data/survivors.csv and data/survivors.jsonl; use verify.py to "
            f"check it. Pass --stores if you have run the sweep yourself.")

    seen: dict[tuple, dict] = {}
    for store in stores:
        # A backup taken before a repair holds superseded verdicts. It happens
        # to carry no Mathlib survivors today, which is luck rather than
        # design, and a future backup of a Mathlib store would be counted.
        if "-before-" in store or "-artefact" in store:
            continue
        try:
            link = sqlite3.connect(f"file:{store}?mode=ro", uri=True)
        except sqlite3.Error:
            continue
        link.row_factory = sqlite3.Row
        try:
            rows = link.execute(
                "SELECT * FROM weakening WHERE verdict = 'weakens'").fetchall()
        except sqlite3.Error:
            continue
        for raw in rows:
            row = dict(raw)
            row.setdefault("floor", None)
            row.setdefault("subsumed", None)
            # Any corpus, not only Mathlib. This filter silently returned zero
            # survivors for Tau Ceti, which reads exactly like a corpus with
            # nothing in it -- the failure this project keeps finding. Callers
            # that want one corpus filter on `corpus`, which the export emits.
            if "." not in row["module"]:
                continue
            if row["subsumed"] != "new":
                continue
            if not (reaches_conclusion(row) and actually_weakened(row)):
                continue
            seen.setdefault((row["module"], row["theorem"], row["binder"]), row)
    return list(seen.values())


def rank(source_class: str, floor: str) -> int:
    """Depth for ordering, with unranked pairs sent to the bottom rather than
    the top. `magnitude` returns -1 for a pair it cannot place, and sorting on
    that directly would put the least-known families first."""
    value = magnitude(source_class, floor)
    return -1 if value == UNRANKED else value


def area_of(module: str) -> str:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else parts[0]


def full_name(row: dict) -> str:
    namespace = (row.get("namespace") or "").strip()
    return f"{namespace}.{row['theorem']}" if namespace else row["theorem"]


def fetch_signatures(rows: list[dict], repo: Path, cache: Path,
                     batch: int, timeout: int) -> dict[str, str]:
    """Ask Lean what each theorem really says. Cached: the answer only changes
    when the library does, and a rebuild of this document should be free."""
    from signatures import signatures, resolve_in_scope
    from leanrun import wait_for_memory

    known: dict[str, str] = {}
    if cache.exists():
        known.update(json.loads(cache.read_text(encoding="utf-8")))
    wanted = collections.OrderedDict()
    for row in rows:
        wanted.setdefault(full_name(row), row)
    missing = [name for name in wanted if name not in known]
    print(json.dumps({"declarations": len(wanted), "cached": len(wanted) - len(missing),
                      "to_fetch": len(missing)}), flush=True)

    for start in range(0, len(missing), batch):
        wait_for_memory()
        chunk = missing[start:start + batch]
        mods = {wanted[name]["module"] for name in chunk}
        known.update(signatures(repo, chunk, timeout, mods))
        cache.write_text(json.dumps(known, indent=0), encoding="utf-8")
        print(json.dumps({"resolved": len(known), "of": len(wanted)}), flush=True)

    stragglers = [n for n in missing if n not in known]
    if stragglers:
        pairs = [((wanted[n].get("namespace") or "").strip(), wanted[n]["theorem"])
                 for n in stragglers]
        mods = [wanted[n]["module"] for n in stragglers]
        for start in range(0, len(pairs), batch):
            wait_for_memory()
            found = resolve_in_scope(repo, pairs[start:start + batch], timeout,
                                     set(mods[start:start + batch]))
            for (namespace, theorem), signature in found.items():
                known[f"{namespace}.{theorem}".lstrip(".")] = signature
        cache.write_text(json.dumps(known, indent=0), encoding="utf-8")
        print(json.dumps({"after_scope_pass": len(known), "of": len(wanted)}), flush=True)
    return known


BREAK_AFTER = "]),.→↔⇑}"

# Lean invents binder names -- `inst`, `inst_3` -- that are not in the source
# and mean nothing to a reader, and it writes each universe separately. Both are
# rendering noise: Mathlib's own source says `[Module R M]` and `{F G : Type*}`.
# 21% of all signature text, and no mathematical content.
AUTO_BINDER_RE = re.compile(r"\[\s*inst[✝]?(?:_\d+)?\s*:\s*")
UNIVERSE_RE = re.compile(r"\{([A-Za-z][\w']*)\s*:\s*(Type|Sort)\s+u_\d+\}")


def readable(signature: str) -> str:
    """The signature as a person would write it, with nothing removed but names
    the elaborator supplied and universe indices nobody reads."""
    text = " ".join(signature.split())
    text = AUTO_BINDER_RE.sub("[", text)
    spans, matches, i = [], list(UNIVERSE_RE.finditer(text)), 0
    while i < len(matches):
        j = i
        while (j + 1 < len(matches)
               and matches[j].end() + 1 >= matches[j + 1].start()
               and matches[j + 1].group(2) == matches[i].group(2)):
            j += 1
        names = " ".join(m.group(1) for m in matches[i:j + 1])
        spans.append((matches[i].start(), matches[j].end(),
                      "{" + names + " : " + matches[i].group(2) + "*}"))
        i = j + 1
    for start, end, replacement in reversed(spans):
        text = text[:start] + replacement + text[end:]
    return text


def breakable(text: str) -> str:
    """Mark places a Lean signature may be broken across lines.

    Justified \\texttt{} can only break at spaces, and a signature is mostly
    bracketed groups and dotted names. The sentinel is inserted before escaping
    and becomes \\allowbreak afterwards, so it cannot land inside a control
    sequence that escaping introduced.
    """
    for ch in BREAK_AFTER:
        text = text.replace(ch, ch + "\x00")
    return text


def escape(text: str) -> str:
    """Lean prints characters TeX reserves. Typeset with a Unicode engine, so
    the mathematics itself needs no transliteration -- only the ten characters
    TeX would otherwise read as markup."""
    for bad, good in (("\\", "\\textbackslash{}"), ("{", "\\{"), ("}", "\\}"),
                      ("$", "\\$"), ("&", "\\&"), ("#", "\\#"), ("%", "\\%"),
                      ("_", "\\_"), ("^", "\\textasciicircum{}"),
                      ("~", "\\textasciitilde{}")):
        text = text.replace(bad, good)
    return text.replace("\x00", "\\allowbreak{}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stores", default="scrutiny/*.db")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=Path("scrutiny/signatures.json"))
    parser.add_argument("--batch", type=int, default=120)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--derived-area", action="append", default=[],
                        help="areas swept with the table derived from "
                             "class ... extends rather than the hand-written "
                             "one; named in the preamble so the document never "
                             "mixes two instruments silently")
    parser.add_argument("--classification", type=Path,
                        help="replaceable.jsonl; marks each entry as a proof "
                             "that never used the assumption or one that found "
                             "another route without it")
    parser.add_argument("--no-lean", action="store_true",
                        help="skip the signature pass and show nothing rather "
                             "than showing our reconstruction as if it were the "
                             "theorem")
    args = parser.parse_args()

    verdicts: dict[str, str] = {}
    if args.classification and args.classification.exists():
        for line in args.classification.read_text(encoding="utf-8").splitlines():
            if line.strip():
                item = json.loads(line)
                verdicts[item["id"]] = item["verdict"]

    rows = survivors(args.stores)
    rows.sort(key=lambda r: (area_of(r["module"]), r["module"], r["theorem"]))
    print(json.dumps({"survivors": len(rows),
                      "areas": len({area_of(r["module"]) for r in rows})}), flush=True)

    known = {} if args.no_lean else fetch_signatures(
        rows, args.repo, args.cache, args.batch, args.timeout)

    by_area: dict[str, list[dict]] = collections.defaultdict(list)
    for row in rows:
        by_area[area_of(row["module"])].append(row)

    def target(row):
        # The class the shipped source is verified to carry, not the descent's
        # floor. The descent searched below `to_class` and recorded only the
        # name of what it reached; the store kept no source for it, so the
        # export publishes `to_class` and marks the floor unverified. Depth and
        # invertibility statistics computed from the floor would rest on a
        # class the artifact itself says it cannot check.
        return row["to_class"]

    if args.derived_area:
        named = ", ".join(escape(a) for a in args.derived_area)
        DERIVED_NOTE = (
            rf"\textbf{{Two instruments.}} All areas but {named} were swept with a "
            r"hand-written table of 48 weakenings. That table names no categorical "
            rf"class, so {named} was swept with one derived from the library's own "
            r"\texttt{{class \dots\ extends}} declarations. The two are not "
            r"interchangeable and the areas are not comparable to each other.")
    else:
        DERIVED_NOTE = r""

    lines = [
        r"\documentclass[10pt,a4paper]{article}",
        r"\usepackage[a4paper,margin=1.4cm,top=1.6cm,bottom=1.6cm]{geometry}",
        r"\usepackage{fontspec}",
        # No \setmainfont: the default serif is fine and naming a font that
        # fontspec cannot find kills the build. All the Unicode is in the
        # signatures, which are typeset in Menlo -- present on every Mac and
        # carrying the glyphs Lean prints.
        r"\setmonofont{Menlo}[Scale=0.78]",
        r"\usepackage{xcolor}",
        r"\definecolor{locator}{gray}{0.42}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\usepackage{multicol}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{3pt}",
        # Ragged right, because justifying a monospace signature stretches the
        # spaces into gaps and still overflows.
        r"\raggedright",
        r"\setlength{\emergencystretch}{3em}",
        r"\usepackage{titlesec}",
        r"\titleformat{\section}{\large\bfseries}{}{0pt}{}",
        r"\titleformat{\subsection}{\normalsize\bfseries}{}{0pt}{}",
        r"\titlespacing*{\section}{0pt}{0pt}{6pt}",
        r"\titlespacing*{\subsection}{0pt}{10pt}{2pt}",
        r"\title{Assumptions that were never used: the catalogue}",
        r"\author{Companion to the note. Generated, not written.}",
        r"\date{\today}",
        r"\begin{document}", r"\maketitle",
        r"\section*{What this is}",
        rf"Every one of the {len(rows)} survivors of a mechanical search across "
        rf"{len(by_area)} areas of Mathlib: theorems whose stated algebraic "
        r"setting is stronger than their own proof requires. Each entry gives the "
        r"declaration, the module it lives in, the assumption as stated, and the "
        r"weakest class at which the original proof still compiles.",
        r"",
        r"The signature shown is what Lean prints for the theorem as the library "
        r"has it, not our reconstruction of it.",
        r"",
        DERIVED_NOTE,
        r"\textbf{Two kinds of entry.} An entry marked $\ddagger$ is one whose "
        r"weakened proof is \emph{not} the original proof: re-elaborated without "
        r"the assumption, a tactic searched again and found another route, so the "
        r"assumption was \emph{replaceable} rather than unused. An unmarked entry "
        r"is the same proof term modulo the substituted class --- the assumption "
        r"was never used at all. Of the entries that could be classified, "
        r"87.5\% are unused and 12.5\% replaceable. An entry marked ? could not be "
        r"classified because the original declaration is \texttt{private} and "
        r"cannot be named from outside its own file; those entries verify like any "
        r"other and are findings, not failures.",
        r"",
        r"\textbf{Nothing here is filtered for interest.} The search establishes "
        r"that a proof survives a weaker hypothesis; it cannot establish that the "
        r"weaker statement is worth having. Some entries are auxiliary lemmas "
        r"whose conclusion barely involves the weakened structure, and they are "
        r"listed alongside the rest because dropping them would claim a judgement "
        r"the machine did not make. \emph{Depth is not worth.}",
        r"",
        r"\tableofcontents",
    ]

    index: list[tuple[str, str]] = []
    for area in sorted(by_area):
        members = by_area[area]
        lost = sum(1 for r in members
                   if r["from_class"] in INVERTIBLE and target(r) in PLAIN)
        families = collections.defaultdict(list)
        for row in members:
            families[(row["from_class"], target(row))].append(row)
        # Deepest first. The ordering is by structural distance, which is not
        # the same as interest -- the preamble says so, because a list sorted
        # by depth otherwise implies the deep end is the interesting end.
        ordered = sorted(families.items(),
                         key=lambda kv: (-rank(kv[0][0], kv[0][1]), -len(kv[1]), kv[0]))

        # A one-entry area should not own a page. Break only where the section
        # is long enough to be worth starting fresh.
        plural = lambda n, word: f"{n} {word}" + ("" if n == 1 else "s")
        lines += ([r"\clearpage"] if len(members) >= 10 else [r"\bigskip"]) + [
                  rf"\section{{{escape(area)}}}",
                  rf"{plural(len(members), 'survivor')} in "
                  rf"{plural(len(families), 'family').replace('familys', 'families')}; "
                  rf"{lost} give{'s' if lost == 1 else ''} up subtraction or "
                  rf"division ($\dagger$).",
                  r"", r"\begin{center}",
                  r"\begin{tabular}{llrr}",
                  r"\textbf{stated over} & \textbf{holds over} & "
                  r"\textbf{n} & \textbf{magnitude}\\[2pt]"]
        for (source_class, floor), group in ordered:
            mark = r"\,$\dagger$" if source_class in INVERTIBLE and floor in PLAIN else ""
            lines += [rf"\texttt{{\small {escape(source_class)}}}{mark} & "
                      rf"\texttt{{\small {escape(floor)}}} & {len(group)} & "
                      rf"{magnitude(source_class, floor)}\\"]
        lines += [r"\end{tabular}", r"\end{center}", r""]

        for (source_class, floor), group in ordered:
            mag = magnitude(source_class, floor)
            shown = ('unranked' if mag == UNRANKED
                     else f'magnitude {mag}')
            mark = r"\;$\dagger$" if source_class in INVERTIBLE and floor in PLAIN else ""
            lines += [rf"\subsection*{{{escape(source_class)} $\to$ "
                      rf"{escape(floor)}\quad\textmd{{\small ({len(group)}, "
                      rf"{shown}){mark}}}}}"]
            # One locator per module, not one per entry: 41% of entries repeat
            # a module already shown in the same family.
            by_module = collections.defaultdict(list)
            for row in group:
                by_module[row["module"]].append(row)
            for module in sorted(by_module):
                where = escape(module.removeprefix("Mathlib.")).replace(
                    ".", r"\,\textperiodcentered\,")
                lines += [rf"{{\footnotesize\color{{locator}}{where}}}\\"]
                for row in sorted(by_module[module], key=lambda r: r["theorem"]):
                    name = full_name(row)
                    index.append((name, area))
                    signature = known.get(name)
                    # A double dagger marks a proof that did not merely ignore
                    # the assumption: re-elaborated without it, a tactic found a
                    # different route. The assumption was replaceable rather
                    # than unused, and the two are different claims.
                    kind = verdicts.get(row["id"], "")
                    tag = (r"\;{\footnotesize$\ddagger$}" if kind == "replaceable"
                           else (r"\;{\footnotesize\color{locator}?}"
                                 if kind == "unreadable" else ""))
                    lines += [rf"\hspace*{{1em}}\texttt{{\small "
                              rf"{escape(breakable(name))}}}{tag}\\"]
                    if signature:
                        body = escape(breakable(readable(signature)))
                        lines += [rf"\hspace*{{2em}}{{\footnotesize\texttt{{{body}}}}}"]
                    else:
                        lines += [r"\hspace*{2em}{\footnotesize\itshape "
                                  r"signature not resolved}"]
                    lines += [r""]

    lines += [r"\clearpage", r"\section*{Index of declarations}",
              r"\addcontentsline{toc}{section}{Index of declarations}",
              r"\begin{multicols}{2}\footnotesize\raggedright"]
    for name, area in sorted(set(index)):
        lines += [rf"\texttt{{{escape(breakable(name))}}} \quad "
                  rf"{{\color{{locator}}{escape(area)}}}\\"]
    lines += [r"\end{multicols}"]
    lines += [r"\end{document}"]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"written": str(args.out), "areas": len(by_area),
                      "entries": len(rows),
                      "with_signature": sum(1 for r in rows if full_name(r) in known)},
                     indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
