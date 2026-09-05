#!/usr/bin/env python3
"""Recompile every published survivor and say, per row, whether it holds.

This exists so a reader does not have to believe the table. Each row of
`survivors.jsonl` carries the weakened declaration together with the original
proof, unaltered, and the `open` directives of the file it came from. Given a
Mathlib checkout at the revision named in `MANIFEST.json`, that is everything
needed to put the claim in front of the compiler again.

    python3 verify.py --data data --repo <a lean project with mathlib>
    python3 verify.py --data data --repo <...> --sample 50

A row passes only if Lean reports no error *and* `#print axioms` names the
declaration resting on nothing beyond propext, Classical.choice and Quot.sound. Success is never
inferred from the absence of an error message: a file full of instance failures
still prints no line containing the literal word "error" when Lean tags them,
and that mistake was made here once already.

The verifier reads the published data and nothing else. If it ever needs a
field the export does not carry, the export is wrong and should be fixed there.
"""

from __future__ import annotations

import argparse
import json
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Lean's own tagged and untagged error forms. `error(lean.synthInstanceFailed):`
# does not contain "error:", and a scan for that literal reads a file full of
# instance failures as clean -- a mistake made here once.
#
# Warnings are NOT failures. Lean's linters complain about shadowed binder names
# and unused variables in files that compile perfectly, and the weakened
# statement inherits whatever the original had. Only errors count, which is what
# the sweep itself used.
ERROR_RE = re.compile(r"error(?:\([^)]*\))?:", re.M)
# `#print axioms foo` names what the proof rests on. A declaration may rest on
# FEWER than the three standard axioms -- a proof that avoids Classical.choice
# prints `[propext, Quot.sound]` -- and using fewer is better, not worse. So the
# test is that the set is contained in the standard three, never that it equals
# them. Demanding equality failed a perfectly good row.
# Lean has two spellings and only one of them is a list. A proof that needs no
# axioms at all prints "does not depend on any axioms", which is the *best*
# outcome available and which the first version of this pattern could not match
# -- so 40 of 645 rows, every one of them cleaner than required, were reported
# as failures. This is the second time this check has been wrong in the same
# direction: it once demanded all three axioms and failed proofs that used two.
# A stricter-than-necessary success test fails good rows quietly.
AXIOMS_RE = re.compile(
    r"'(?P<name>[^']+)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))")
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run_lean(repo: Path, text: str, timeout: int) -> tuple[str, bool]:
    """Compile one file in its own process group; kill the group on timeout.

    `lake env lean` spawns `lean` beneath it, so killing the direct child
    leaves a grandchild holding a compiled Mathlib -- gigabytes that nothing
    reclaims. This took a machine down once.
    """
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(text)
        path = Path(handle.name)
    process = None
    try:
        process = subprocess.Popen(
            ["lake", "env", "lean", str(path)], cwd=repo, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        out, err = process.communicate(timeout=timeout)
        return out + err, False
    except subprocess.TimeoutExpired:
        if process is not None:
            import os
            import signal
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            except (OSError, ProcessLookupError):
                pass
            process.communicate()
        return "", True
    except OSError as problem:
        return f"error: could not run lean: {problem}", False
    finally:
        path.unlink(missing_ok=True)


def opened(row: dict) -> str:
    """Put the declaration back in the scope its source had, the way the sweep
    does: one `open ... in`, bound to this declaration and nothing else.

    Not bare `open` commands. Those are file-scoped and permanent, and they
    bring enough into scope to create ambiguities that the scoped form does
    not: `SetLike.lt_iff_le_and_exists` compiles under `open ... in` and dies
    under bare opens on an ambiguous `instSubtypeSet`. It was reported as an
    unreproducible row for a day.

    `open scoped` cannot be folded into the same clause and stays its own
    command; it carries notation rather than names.

    Every namespace prefix, not just the leaf: a declaration inside `A.B.C` may
    cite a name that resolves only under `A` or `A.B`.
    """
    plain: list[str] = []
    scoped: list[str] = []
    alone: list[str] = []
    for line in (row.get("opens") or "").splitlines():
        body = line.strip().removeprefix("open ").strip()
        if not body:
            continue
        if body.startswith("scoped"):
            scoped.append(body)
        elif "(" in body or " hiding " in body:
            # `open A (x y)` and `open A hiding x` are their own syntactic
            # forms and cannot be chained with further namespaces in one
            # command. Merging them into the shared clause produced `open A
            # (x) B hiding y C in`, which does not parse -- and splitting on
            # whitespace first turned `hiding` and the hidden name into
            # namespaces of their own. 24 rows of the breaks export never
            # parsed for a consumer because of this; found by the
            # `unstated-conclusions` project, which recompiled them and sent
            # back the error blocks.
            alone.append(body)
        else:
            plain.append(body)
    namespace = (row.get("namespace") or "").strip()
    if namespace:
        parts = namespace.split(".")
        plain.extend(".".join(parts[: i + 1]) for i in range(len(parts)))
    # Plain names first, scoped second. A scoped notation namespace is often
    # reachable only *through* one of the plain ones -- `open scoped sigma`
    # resolves as `ArithmeticFunction.sigma` and is an unknown namespace until
    # `ArithmeticFunction` is open. The sweep emits the scoped clause first and
    # gets away with it only because it also emits every directive a second
    # time, raw, ahead of both; remove that duplicate and the row stops
    # compiling. The duplicate was load-bearing by accident.
    names = list(dict.fromkeys(" ".join(plain).split()))
    prefix = f"open {' '.join(names)} in\n" if names else ""
    prefix += "".join(f"open {directive} in\n" for directive in dict.fromkeys(alone))
    prefix += "".join(f"open {directive} in\n" for directive in dict.fromkeys(scoped))
    return prefix


def source_for(row: dict) -> str:
    name = f"w{row['id']}"
    # `opened` folds the file's own directives and the namespace prefixes into
    # one scoped clause, so nothing is emitted separately here. Emitting the
    # directives again as bare commands is what created the ambiguity above.
    return ("import Mathlib\n\nset_option maxHeartbeats 400000\n\n"
            + opened(row)
            + row["source"]
            + f"\n\n#print axioms {name}\n")


def check(repo: Path, row: dict, timeout: int) -> tuple[bool, str]:
    """Recompile one row, mirroring the sweep's own two-shot procedure.

    The sweep compiles a candidate with the file's `open` directives and, if
    that dies on a context error, once more without them. Some directives name
    a notation namespace that does not resolve from outside its own file, which
    is a fact about the preamble rather than about the weakening, so the sweep
    does not hold it against the row. The store keeps `opens` either way and
    records nothing about which attempt won.

    A verifier that always includes the directives therefore fails rows the
    sweep passed, for a reason that has nothing to do with the mathematics. It
    is not enough to reproduce the result; it has to reproduce the procedure.
    Which variant succeeded is reported, so a reader can see when a row needed
    the retry.
    """
    ok, why = attempt(repo, row, timeout)
    if ok or not (row.get("opens") or "").strip():
        return ok, why
    bare = dict(row)
    bare["opens"] = ""
    ok, second = attempt(repo, bare, timeout)
    if ok:
        return True, "ok without the file's open directives"
    return False, f"{why}; without directives: {second}"


def attempt(repo: Path, row: dict, timeout: int) -> tuple[bool, str]:
    # Before spending a compile: does the source carry the class being claimed?
    # A green recompile of the wrong statement is worse than a red one, because
    # it is quiet.
    mismatch = claims_what_it_proves(row)
    if mismatch:
        return False, mismatch
    report, timed_out = run_lean(repo, source_for(row), timeout)
    if timed_out:
        return False, "timeout"
    found = ERROR_RE.search(report)
    if found:
        line = report[found.start():].splitlines()[0][:110]
        return False, f"error: {line}"
    axioms = AXIOMS_RE.search(report)
    if not axioms:
        return False, "no axiom record"
    if axioms.group("name") != f"w{row['id']}":
        return False, f"axiom record names {axioms.group('name')}"
    used = set() if axioms.group("none") else {
        a.strip() for a in (axioms.group("axioms") or "").split(",") if a.strip()}
    extra = used - STANDARD_AXIOMS
    if extra:
        return False, f"axioms beyond the standard three: {sorted(extra)}"
    return True, "ok"


def preflight(repo: Path, timeout: int) -> bool:
    """Prove Lean can run here before paying for hundreds of launches.

    A wrong --repo otherwise produces one identical failure per row, each
    costing a process. The sweep driver learned this the same way.
    """
    if not repo.exists():
        print(f"\n{repo} does not exist.")
        return False
    report, timed_out = run_lean(repo, "import Mathlib\n\n#check @Nat.succ_le_succ\n",
                                 timeout)
    if timed_out:
        print(f"\npreflight timed out after {timeout}s. Is Mathlib built? "
              f"Try `lake exe cache get`.")
        return False
    if "Nat.succ_le_succ" not in report:
        first = next((l for l in report.splitlines() if l.strip()), "(no output)")
        print(f"\npreflight failed: Lean could not compile `import Mathlib`.\n"
              f"  {first[:160]}\n"
              f"If this says 'incompatible header', the built artefacts are from "
              f"another toolchain: run `lake exe cache get`.")
        return False
    return True


def claims_what_it_proves(row: dict) -> str | None:
    """Does the row's source actually carry the class the row publishes?

    The one check that would have caught the worst defect this artifact has
    shipped. `holds_over` is the descent's floor; `source` was frozen at the
    attempt one step above it. 43 of 568 rows therefore recompiled a weaker
    statement than the table printed, ten of them among the eleven deepest --
    the rows the invertibility argument is built from -- and this verifier
    reported PASS on every one.

    Recompiling proves something. This proves it is the advertised something.
    """
    holds = row.get("holds_over") or ""
    if not holds:
        return "no holds_over recorded"
    if holds not in row.get("source", ""):
        return (f"published as holding over {holds}, which appears nowhere in "
                f"the source this verifies (binder {row.get('binder', '?')})")
    return None


def selfcheck(data: Path, manifest: dict, rows: list[dict]) -> int:
    """The published files against each other. No Lean, no Mathlib.

    Four counts from one source; any disagreement means a row was counted where
    a finding was meant, which has happened.
    """
    import csv as _csv
    problems = []
    # An export that produced nothing passes every consistency check below:
    # zero equals zero equals zero, no duplicate ids, no blank source. It once
    # printed "ok 0 rows" over data this project had just overwritten with an
    # empty file. Nothing here may report ok on nothing.
    if not rows:
        problems.append("survivors.jsonl is empty. Every check below would "
                        "pass on no data, which is why this one runs first.")
    with (data / "survivors.csv").open(encoding="utf-8") as handle:
        csv_rows = list(_csv.DictReader(handle))
    if not (len(csv_rows) == len(rows) == manifest.get("survivors")):
        problems.append(f"counts disagree: csv {len(csv_rows)}, jsonl {len(rows)}, "
                        f"manifest {manifest.get('survivors')}")
    ids = [r["id"] for r in rows]
    if len(ids) != len(set(ids)):
        problems.append(f"{len(ids) - len(set(ids))} duplicate ids in survivors.jsonl")
    blank = [r["theorem"] for r in rows if not r.get("source", "").strip()]
    if blank:
        problems.append(f"{len(blank)} rows carry no source and cannot be verified, "
                        f"first: {blank[0]}")
    if not manifest.get("mathlib", {}).get("revision"):
        problems.append("MANIFEST records no Mathlib revision; every row is then "
                        "unfalsifiable")
    unproven = [(r["theorem"], why) for r in rows
                if (why := claims_what_it_proves(r))]
    if unproven:
        problems.append(
            f"{len(unproven)} rows publish a class their own source does not "
            f"contain, so verifying them would certify a weaker claim than the "
            f"table prints. First: {unproven[0][0]} -- {unproven[0][1]}")
    csv_keys = {(r["theorem"], r["binder"]) for r in csv_rows}
    jsonl_keys = {(r["theorem"], r["binder"]) for r in rows}
    if csv_keys != jsonl_keys:
        problems.append(f"csv and jsonl name different rows: "
                        f"{len(csv_keys ^ jsonl_keys)} differ")
    for problem in problems:
        print(f"FAIL  {problem}")
    if not problems:
        print(f"ok  {len(rows)} rows, csv and jsonl agree, ids unique, "
              f"every row has a source carrying the class it publishes, "
              f"revision recorded")
    return 1 if problems else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path("data"))
    parser.add_argument("--repo", type=Path,
                        help="a Lean project whose Mathlib is at the revision "
                             "named in MANIFEST.json. Not needed for --selfcheck, "
                             "which touches no Lean.")
    parser.add_argument("--sample", type=int, default=0,
                        help="check a random subset instead of everything")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--out", type=Path,
                        help="write the per-row result here (default stdout only)")
    parser.add_argument("--force", action="store_true",
                        help="run even though Mathlib is at a different revision "
                             "than the manifest names. Every line is then marked "
                             "off-revision, because the result is not comparable "
                             "to the published one.")
    parser.add_argument("--selfcheck", action="store_true",
                        help="check the published data against itself and exit. "
                             "No Lean, one second.")
    args = parser.parse_args()

    for needed in ("MANIFEST.json", "survivors.jsonl"):
        if not (args.data / needed).exists():
            raise SystemExit(f"{args.data / needed} not found. Point --data at the "
                             f"directory holding the published export.")
    manifest = json.loads((args.data / "MANIFEST.json").read_text(encoding="utf-8"))
    rows = [json.loads(line) for line
            in (args.data / "survivors.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()]

    if args.selfcheck:
        return selfcheck(args.data, manifest, rows)
    if args.repo is None:
        raise SystemExit("--repo is required to recompile. For the data-only "
                         "checks, use --selfcheck.")

    wanted = manifest.get("mathlib", {}).get("revision", "")
    # The revision that matters is Mathlib's, not the project that depends on
    # it. Comparing the project's HEAD reports a mismatch on every run.
    mathlib_here = args.repo / ".lake" / "packages" / "mathlib"
    actual = subprocess.run(
        ["git", "-C", str(mathlib_here if mathlib_here.exists() else args.repo),
         "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    print(f"# survivors        {len(rows)}")
    print(f"# mathlib wanted   {wanted or '(unrecorded)'}")
    print(f"# mathlib here     {actual or '(not a git checkout)'}")
    print(f"# toolchain        {manifest.get('toolchain', '')}")
    off_revision = bool(wanted and actual and wanted != actual)
    if off_revision and not args.force:
        raise SystemExit(
            f"\nMathlib here is not the revision these results were produced "
            f"against.\n"
            f"  manifest: {wanted}\n  here:     {actual}\n\n"
            f"A failure would not be distinguishable from Mathlib having moved, "
            f"so the number this prints would not mean what it says. To check "
            f"out the right revision:\n\n"
            f"  git -C <project>/.lake/packages/mathlib checkout {wanted}\n"
            f"  cd <project> && lake exe cache get\n\n"
            f"Or pass --force to run anyway; every line will be marked "
            f"off-revision.")
    if off_revision:
        print("# OFF-REVISION: results below are not comparable to the published "
              "ones.")

    if not preflight(args.repo, args.timeout):
        return 1

    if args.sample and args.sample < len(rows):
        random.Random(args.seed).shuffle(rows)
        rows = rows[: args.sample]
        print(f"# sampling         {len(rows)} rows, seed {args.seed}")
    print()

    mark = "OFF-REVISION " if off_revision else ""
    passed, failures, lines = 0, [], []
    for index, row in enumerate(rows, 1):
        ok, why = check(args.repo, row, args.timeout)
        passed += ok
        lines.append(f"{mark}{'PASS' if ok else 'FAIL'}  {row['theorem']}  "
                     f"{row['stated']} -> {row['holds_over']}"
                     + ("" if ok else f"  [{why}]"))
        if not ok:
            failures.append(lines[-1])
        print(f"{index:>4}/{len(rows)}  {lines[-1]}", flush=True)

    summary = (f"\n{passed} of {len(rows)} verified"
               + (f", {len(failures)} failed" if failures else ", none failed"))
    print(summary)
    if args.out:
        args.out.write_text("\n".join(lines) + summary + "\n", encoding="utf-8")
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
