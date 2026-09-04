#!/usr/bin/env python3
"""Weaken a theorem's typeclass assumption and see whether its own proof still works.

Perturbation asks whether a hypothesis can be dropped, and its ceiling is low:
the statements it reaches are one edit from a theorem someone already wrote, so
a true one is usually either already in the library in more general form or
folklore. Both were measured -- of twenty candidates a strong prover closed,
fifteen were subsumed by an existing theorem and one was a duplicate.

This asks a different question. `Foo` is stated over `CommRing`; does its proof
ever use more than `Ring`? Nobody asks that unless they need it, so the space is
mostly unexamined rather than known-and-unwritten, which is the difference that
matters when the goal is a conjecture that is not folklore.

And the verdict is mechanical in a way nothing else here is. Weaken the binder,
keep the proof byte for byte, compile. It works or it does not. No prover to
be too weak, no sampler to miss a witness, no tactic that reports success
because it timed out.

Read `docs/typeclass.md` for what the verdict does *not* mean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sqlite3
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import os
import random

from perturb import (namespace_at, enclosing, variables_at, needed, opens_at,
                     split_binders, strip_comments)
from leanrun import (run_bounded, available_gb, wait_for_memory, opened,
                        errors_in, HEADER, header_for, AXIOMS_RE)

# SWEEP_TABLE names a derived table (tools/derive_edges.py) to use instead of
# the hand-written one below. Kept as an override rather than a replacement: the
# eighteen areas already swept were measured with the hand table, and a
# cross-area comparison needs one instrument. A wider sweep is a separate run
# with its own numbers, not a correction to the old ones.
_TABLE_PATH = os.environ.get("SWEEP_TABLE")

# Single-argument classes only, and only edges that are genuinely weakenings in
# Mathlib's hierarchy. Kept as a table rather than derived from the instance
# graph because a wrong edge here produces a silent false negative -- the
# weakened statement fails to elaborate and is recorded as "proof needs the
# structure", which is exactly the wrong conclusion. A table can be reviewed.
WEAKENINGS: dict[str, list[str]] = {
    "CommRing": ["Ring", "CommSemiring"],
    "Ring": ["Semiring", "NonUnitalRing", "AddCommGroup"],
    "Field": ["DivisionRing", "CommRing"],
    "DivisionRing": ["Ring", "GroupWithZero"],
    "CommSemiring": ["Semiring", "CommMonoidWithZero"],
    "Semiring": ["NonUnitalSemiring", "MonoidWithZero", "AddCommMonoid"],
    "CommGroup": ["Group", "CommMonoid"],
    "Group": ["Monoid", "DivInvMonoid"],
    "CommMonoid": ["Monoid", "CommSemigroup"],
    "Monoid": ["Semigroup", "MulOneClass"],
    "AddCommGroup": ["AddGroup", "AddCommMonoid"],
    "AddGroup": ["AddMonoid", "SubNegMonoid"],
    "AddCommMonoid": ["AddMonoid", "AddCommSemigroup"],
    "AddMonoid": ["AddSemigroup", "AddZeroClass"],
    "LinearOrder": ["PartialOrder", "Lattice"],
    "PartialOrder": ["Preorder"],
    "MetricSpace": ["PseudoMetricSpace"],
    "NormedField": ["NormedRing", "Field"],
    "NormedRing": ["NonUnitalNormedRing", "Ring"],
    "NormedAddCommGroup": ["SeminormedAddCommGroup", "AddCommGroup"],
    "Fintype": ["Finite"],
    "IsDomain": ["NoZeroDivisors"],
    "EuclideanDomain": ["CommRing"],
    "LinearOrderedField": ["LinearOrderedRing", "Field"],
    "LinearOrderedRing": ["LinearOrderedSemiring", "OrderedRing"],
    "CompleteLattice": ["Lattice"],
    "TopologicalSpace": [],   # nothing weaker worth trying
}

DECLARATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)?"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][^\s:({\[]*)"
    r"(?P<statement>(?:[^:=]|:(?!=)|=(?!\s))*?):=(?P<proof>.*?)"
    r"(?=\n(?:@\[|/--|theorem |lemma |def |instance |namespace |end |section |variable |open |private |protected |noncomputable ))",
    re.M | re.S)

INSTANCE_RE = re.compile(r"^\[\s*(?:[A-Za-z_][A-Za-z0-9_']*\s*:\s*)?"
                         r"([A-Za-z_][A-Za-z0-9_'.]*)\s+([^\]]+?)\s*\]$")

TRAILING_RE = re.compile(
    r"(?:\n\s*(?:@\[[^\]]*\]|protected|private|noncomputable|nonrec|open|/--.*))+\s*$",
    re.S)


TABLE: dict[str, list[str]] = WEAKENINGS
if _TABLE_PATH:
    TABLE = json.loads(Path(_TABLE_PATH).read_text(encoding="utf-8"))


def trim_proof(proof: str) -> str:
    """Drop modifiers the extraction swallowed from the following declaration.

    `theorem foo := bar` followed by `protected\ntheorem baz` leaves a dangling
    `protected` on the end of the proof, and the file then fails with
    "unexpected token; expected 'lemma'" -- our failure, reported as if the
    weakening were at fault.
    """
    return TRAILING_RE.sub("", proof.rstrip()).rstrip()


SCHEMA = """
CREATE TABLE IF NOT EXISTS weakening (
    id          TEXT PRIMARY KEY,
    module      TEXT NOT NULL,
    opens       TEXT,
    theorem     TEXT NOT NULL,
    namespace   TEXT,
    binder      TEXT NOT NULL,
    from_class  TEXT NOT NULL,
    to_class    TEXT NOT NULL,
    source      TEXT NOT NULL,
    verdict     TEXT,
    detail      TEXT
);
CREATE INDEX IF NOT EXISTS weakening_verdict ON weakening(verdict);
"""


def connect(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(path, timeout=120)
    connection.row_factory = sqlite3.Row
    connection.executescript(SCHEMA)
    return connection


def instance_class(binder: str) -> tuple[str, str] | None:
    """`[CommRing R]` gives `("CommRing", "R")`; anything else gives nothing."""
    match = INSTANCE_RE.match(binder.strip())
    if match is None:
        return None
    name, argument = match.group(1), match.group(2).strip()
    if " " in argument:          # multi-argument classes are out of scope
        return None
    return name, argument


def weakenings(path: Path, root: Path) -> list[dict]:
    """Every (theorem, instance binder, weaker class) this file offers."""
    try:
        source = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    except OSError:
        return []
    module = ".".join(path.relative_to(root).with_suffix("").parts)
    checkpoints = namespace_at(source)
    variable_points = variables_at(source)
    open_points = opens_at(source)
    found: list[dict] = []
    for match in DECLARATION_RE.finditer(source):
        name = match.group("name")
        statement, proof = match.group("statement"), match.group("proof")
        if len(statement) > 700 or len(proof) > 2500 or not proof.strip():
            continue
        split = split_binders(statement)
        if split is None:
            continue
        binders, conclusion = split
        available: list[str] = []
        for point, scoped in variable_points:
            if point > match.start():
                break
            available = scoped
        binders = needed(available, statement) + binders
        directives: list[str] = []
        for point, scoped in open_points:
            if point > match.start():
                break
            directives = scoped
        for index, binder in enumerate(binders):
            parsed = instance_class(binder)
            if parsed is None:
                continue
            from_class, argument = parsed
            for to_class in TABLE.get(from_class, []):
                weakened = list(binders)
                weakened[index] = f"[{to_class} {argument}]"
                identity = hashlib.sha256(
                    f"{module}|{name}|{index}|{to_class}".encode()).hexdigest()[:16]
                found.append({
                    "id": identity,
                    "module": module,
                    "theorem": name,
                    "namespace": enclosing(checkpoints, match.start()),
                    "binder": binder.strip(),
                    "from_class": from_class,
                    "to_class": to_class,
                    "opens": "\n".join(directives),
                    "source": (f"theorem w{identity} {' '.join(weakened)} :"
                               f"{conclusion} :={trim_proof(proof)}"),
                })
    return found


# Ordered: our own failure first, then the statement, then the proof. A wrong
# order would file a statement that cannot be written at all as a proof that
# needs the structure, which is the opposite of the truth.
CONTEXT_MARKERS = ("unknown identifier", "unknown constant", "unexpected token",
                   "function expected", "ambiguous", "unknown namespace")
INCOHERENT_MARKERS = ("failed to synthesize", "instance problem",
                      "maximum recursion depth", "typeclass instance problem")


def classify(errors: str) -> str:
    """Whose failure is this: ours, the statement's, or the proof's?

    Takes the error lines, never the whole report, and weighs the **first** one
    above the rest. Two ways this went wrong before. Lean's hints quote the
    failing term back -- "The identifier `x` is unknown, and Lean's autoImplicit
    option..." -- so scanning the whole report let a hint attached to a genuine
    instance failure read as our setup breaking. And a failed instance breaks
    the proof that follows it, which then reports its own unknown identifiers,
    so scanning every error let the cascade outvote its own cause. 120 of 180
    attempts were misfiled that way.

    Lean reports in source order, so the first error is the one that broke.

    `Field -> CommRing` on a theorem that also assumes `[NumberField K]` cannot
    even be stated -- `NumberField` extends `Field`, so the weakened signature
    has no instance. That is not evidence the proof uses commutativity, and
    counting it as such would make the sweep's negative result meaningless.
    It is the majority case for the most common edge in the table.
    """
    lines = [line for line in errors.splitlines() if line.strip()]
    first = (lines[0] if lines else "").lower()
    if any(marker in first for marker in CONTEXT_MARKERS):
        return "context"
    if any(marker in first for marker in INCOHERENT_MARKERS):
        return "incoherent"
    if first:
        return "needs_structure"
    return "context"


def compile_once(repo: Path, row: dict, directives: str,
                 timeout: int) -> tuple[str, str]:
    name = f"w{row['id']}"
    text = (header_for(row) + "\n"
            + (directives + "\n\n" if directives else "")
            + opened(row) + row["source"] + f"\n\n#print axioms {name}\n")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        out, err = run_bounded(["lake", "env", "lean", str(path)], repo, timeout)
    except (OSError, subprocess.TimeoutExpired):
        return "timeout", ""
    finally:
        path.unlink(missing_ok=True)
    report = out + err
    errors = errors_in(report)
    if errors:
        return classify("\n".join(errors)), errors[0][:200]
    match = AXIOMS_RE.search(report)
    if match and "sorryAx" not in (match.group(2) or ""):
        return "weakens", ""
    return "context", "compiled but produced no axiom report"


def instance_recoverable(repo: Path, row: dict, timeout: int) -> bool:
    """Does the weakened context still yield the class we removed?

    Sometimes it does, and not because of a bug. `cardPowDegree_anti_archimedean`
    assumes `[Fintype Fq] [Field Fq]`; weaken `Field` to `DivisionRing` and
    Mathlib hands the field structure straight back, because a finite division
    ring is a field. Wedderburn's little theorem is in the library as an
    instance, so the weakened statement is the original wearing a different
    hat -- it compiles, it is true, and it generalises nothing.

    Asking `inferInstance` for the class we dropped settles it in one compile,
    before anything expensive runs.
    """
    statement = row["source"][:row["source"].find(":=")]
    head = statement[:statement.rindex(":")] if ":" in statement else statement
    argument = row["binder"].strip("[]").split()[-1]
    probe = head.replace(f"theorem w{row['id']}", "example", 1)
    directives = "\n".join(dict.fromkeys(
        line for line in (row.get("opens") or "").splitlines() if line.strip()))
    text = (header_for(row) + "\n" + (directives + "\n\n" if directives else "")
            + opened(row) + probe
            + f": {row['from_class']} {argument} := inferInstance\n")
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
    return not errors_in(out + err)


def attempt(repo: Path, row: dict, timeout: int) -> tuple[str, str]:
    """Compile the weakened theorem with its original proof, alone.

    Alone matters for the reason it mattered in the scrutiny: a batch lets a
    parse error in one declaration corrupt its neighbours, and lets a proof
    cite a sibling. Here it would also let a weakened instance leak into the
    next theorem's elaboration.

    Two shots, because the file's `open` directives cut both ways. Without them
    a name like `log` becomes an autoImplicit variable and the statement fails
    as "Function expected". With them, a directive such as `open scoped zeta`
    -- real, in `ArithmeticFunction/Zeta.lean` -- names a notation namespace
    that does not resolve from outside its own file, and the whole attempt dies
    on our own preamble. Neither is a fact about the weakening, so a `context`
    verdict from the first shot is retried without the preamble rather than
    recorded.
    """
    directives = "\n".join(dict.fromkeys(
        line for line in (row.get("opens") or "").splitlines() if line.strip()))
    verdict, detail = compile_once(repo, row, directives, timeout)
    if verdict == "context" and directives:
        second, second_detail = compile_once(repo, row, "", timeout)
        if second != "context":
            verdict, detail = second, second_detail
    if verdict == "weakens" and instance_recoverable(repo, row, timeout):
        return "vacuous_instance", f"{row['from_class']} is still derivable"
    return verdict, detail


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("area", help="a directory under Mathlib/, e.g. NumberTheory")
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--collect-only", action="store_true")
    parser.add_argument("--corpus", type=Path,
                        help="source root holding the area, relative to --repo."
                             " Defaults to Mathlib's own; give another to sweep a"
                             " different library with the same instrument.")
    parser.add_argument("--worker", type=int, default=0,
                        help="this worker's index, 0-based")
    parser.add_argument("--of", type=int, default=1,
                        help="how many workers share the store; each takes a "
                             "disjoint stride of the shuffled row list")
    parser.add_argument("--shuffle", type=int, metavar="SEED",
                        help="decide rows in seeded random order, so an "
                             "interrupted run leaves a random sample rather "
                             "than a file-order prefix")
    args = parser.parse_args()

    # The corpus is a parameter, not a constant. Sweeping a second library is
    # the only measurement here that is not downstream of somebody else's, and
    # it needs nothing but a different root.
    root = args.repo / (args.corpus or Path(".lake/packages/mathlib"))
    prefix = "Mathlib" if args.corpus is None else ""
    files = sorted((root / prefix / args.area).rglob("*.lean")) if prefix \
        else sorted((root / args.area).rglob("*.lean"))
    connection = connect(args.db)
    rows: list[dict] = []
    for path in files:
        rows.extend(weakenings(path, root))
    connection.executemany(
        "INSERT OR IGNORE INTO weakening"
        " (id, module, theorem, namespace, opens, binder, from_class, to_class, source)"
        " VALUES (:id, :module, :theorem, :namespace, :opens, :binder, :from_class,"
        " :to_class, :source)", rows)
    connection.commit()
    print(json.dumps({"files": len(files), "weakenings": len(rows)}), flush=True)
    if args.collect_only:
        return 0

    todo = [dict(r) for r in connection.execute(
        "SELECT * FROM weakening WHERE verdict IS NULL")]
    if args.shuffle is not None:
        # Rows come back in collection order, which is file order. A run that
        # stops early therefore leaves a prefix of the corpus decided, and a
        # prefix is not a sample -- one census discarded 550 rows for exactly
        # that reason. Shuffling on a fixed seed makes every partial run a valid
        # random sample of whatever remained, so an interrupted census is still
        # usable and the seed makes it reproducible.
        random.Random(args.shuffle).shuffle(todo)
    if args.of > 1:
        # Two processes sharing one store. Each takes every Nth row of the
        # shuffled list, so the slices are disjoint and neither has to
        # coordinate with the other. Disjoint by construction beats locking:
        # the only writes that collide are commits, which SQLite serialises.
        todo = todo[args.worker :: args.of]
    if args.limit:
        todo = todo[: args.limit]
    started = time.monotonic()
    counts: dict[str, int] = {}
    for index, row in enumerate(todo, start=1):
        wait_for_memory()
        verdict, detail = attempt(args.repo, row, args.timeout)
        counts[verdict] = counts.get(verdict, 0) + 1
        connection.execute("UPDATE weakening SET verdict = ?, detail = ? WHERE id = ?",
                           (verdict, detail, row["id"]))
        connection.commit()
        if index % 10 == 0 or index == len(todo):
            rate = index / (time.monotonic() - started)
            print(json.dumps({
                "at": datetime.now(timezone.utc).strftime("%H:%M:%SZ"),
                "done": index, "of": len(todo),
                "per_min": round(rate * 60, 1),
                "eta_min": round((len(todo) - index) / rate / 60, 1) if rate else None,
                "available_gb": round(available_gb(), 1), **counts}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
