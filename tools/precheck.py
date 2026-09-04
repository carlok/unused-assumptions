#!/usr/bin/env python3
"""Reject weakenings that cannot possibly work, without compiling them.

The sweep's cost is compilation, and most of it is spent proving the obvious.
In `NumberTheory`, 54% of attempts came back `incoherent` -- the weakened
statement could not even be stated, because some other assumption on the same
variable demands the class being removed. `AdmissibleAbsValues K` is declared
as `(K : Type*) [Field K]`, so a theorem carrying it keeps `Field K` no matter
what we do to the binder next to it. Compiling to discover that is a minute
spent learning something the class's own signature already says.

The signature is free. `#check @ClassName` prints what a class demands of its
argument, 661 declarations cost 36 seconds, and the requirement graph is small
and reusable. Closing it transitively gives, for each class, everything it drags
along; a weakening whose target is weaker than something dragged along by a
surviving binder is dead before Lean is invoked.

Precision matters far more than recall here, as everywhere in this pipeline: a
wrong rejection silently removes a candidate nobody will see again, while a
missed one costs one compilation. The filter is therefore validated against an
area already swept, and must reject nothing that actually compiled.
"""

from __future__ import annotations

import argparse
import json
import re
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from leanrun import run_bounded, wait_for_memory, opened, HEADER
from signatures import CHECK_RE

# `[inst : Foo bar]` and `[Foo bar]` alike, capturing class and argument.
BINDER_RE = re.compile(r"\[\s*(?:[\w'✝]+\s*:\s*)?([A-Za-z_][\w'.]*)\s+([^\]\s]+)\s*\]")


def class_signatures(repo: Path, wanted: list[tuple[str, dict]],
                     timeout: int) -> dict[str, str]:
    """Ask Lean what each class demands, resolving names where they were written.

    A class name lifted out of a theorem is usually not a full name --
    `AdmissibleAbsValues` is `NumberField.Height.AdmissibleAbsValues` -- so a
    bare `#check` finds one in seventy-five. Opening the scope the binder was
    written in finds them, and Lean prints the full name it settled on.
    """
    blocks = []
    for name, row in wanted:
        # Several spellings, because a class name lifted out of a binder is a
        # short name and the namespace it lives in is not always the one the
        # theorem sits in. Whichever resolves, resolves; the rest are errors we
        # ignore, and Lean prints the full name it settled on either way.
        namespace = (row.get("namespace") or "").strip()
        parts = namespace.split(".") if namespace else []
        spellings = [name] + [".".join(parts[: i + 1]) + f".{name}"
                              for i in range(len(parts))]
        scope = opened({"namespace": namespace, "opens": row.get("opens")})
        blocks.append("".join(f"#check @{s}\n" for s in spellings)
                      + (scope + f"#check @{name}\n" if scope else ""))
    source = HEADER + "\n" + "\n".join(blocks)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(source)
        path = Path(handle.name)
    try:
        out, err = run_bounded(["lake", "env", "lean", str(path)], repo, timeout)
    except (OSError, subprocess.TimeoutExpired):
        return {}
    finally:
        path.unlink(missing_ok=True)
    # Key on the last component: that is what the binder wrote, and what the
    # candidate rows will be matched against.
    found: dict[str, str] = {}
    for match in CHECK_RE.finditer(out + err):
        found.setdefault(match.group(1).rsplit(".", 1)[-1], match.group(2))
    return found


def demands(signature: str) -> set[str]:
    """Classes a class requires of its own first argument.

    `AdmissibleAbsValues : (K : Type u_1) -> [inst : Field K] -> Type u_1` gives
    `{Field}`. Only binders applied to the same variable count; a class that
    happens to mention some other type says nothing about ours.
    """
    head = re.match(r"[^,]*?\(([A-Za-z_][\w']*)\s*:\s*Type", signature)
    if head is None:
        return set()
    argument = head.group(1)
    return {m.group(1).rsplit(".", 1)[-1]
            for m in BINDER_RE.finditer(signature)
            if m.group(2) == argument}


def close(direct: dict[str, set[str]]) -> dict[str, set[str]]:
    """Everything a class drags along, transitively."""
    closed = {name: set(values) for name, values in direct.items()}
    changed = True
    while changed:
        changed = False
        for name, values in closed.items():
            grown = set(values)
            for value in values:
                grown |= closed.get(value, set())
            if grown != values:
                closed[name] = grown
                changed = True
    return closed


def doomed(row: dict, closed: dict[str, set[str]]) -> str | None:
    """Is this weakening dead on arrival? Returns the reason, or nothing.

    The only sound test is whether a surviving assumption on the same variable
    still requires the exact class being removed. Comparing strength ordinals
    instead is wrong and was: `[CommRing R]` sitting next to `[IsDomain R]` does
    not make weakening `IsDomain` pointless, because one is structure and the
    other is a property and the ordinals do not order them. Requirement is a
    fact the signature states; strength is a number we invented.
    """
    argument = row["binder"].strip("[]").split()[-1]
    head = row["source"][: row["source"].find(":=")]
    removed = row["from_class"]
    for match in BINDER_RE.finditer(head):
        name, applied = match.group(1).rsplit(".", 1)[-1], match.group(2)
        if applied != argument or match.group(0) == row["binder"]:
            continue
        if removed in ({name} | closed.get(name, set())):
            return f"{name} still requires {removed} on {argument}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--validate", action="store_true",
                        help="report what would be rejected, change nothing")
    args = parser.parse_args()

    connection = sqlite3.connect(args.db)
    connection.row_factory = sqlite3.Row
    where = "" if args.validate else " WHERE verdict IS NULL"
    rows = [dict(r) for r in connection.execute(f"SELECT * FROM weakening{where}")]
    if not rows:
        print(json.dumps({"pending": 0}))
        return 0

    wanted: dict[str, dict] = {}
    for row in rows:
        head = row["source"][: row["source"].find(":=")]
        for match in BINDER_RE.finditer(head):
            wanted.setdefault(match.group(1), row)
    names = set(wanted)
    wait_for_memory()
    signatures = class_signatures(args.repo, sorted(wanted.items()), args.timeout)
    direct = {name: demands(signature) for name, signature in signatures.items()}
    closed = close(direct)
    print(json.dumps({"classes": len(names), "resolved": len(signatures),
                      "with_requirements": sum(1 for v in closed.values() if v)}),
          flush=True)

    if args.validate:
        wrong = [r for r in rows if r["verdict"] == "weakens" and doomed(r, closed)]
        would = [r for r in rows if doomed(r, closed)]
        by = {}
        for r in would:
            by[r["verdict"]] = by.get(r["verdict"], 0) + 1
        print(json.dumps({"would_reject": len(would), "of": len(rows),
                          "by_actual_verdict": by,
                          "FALSE_REJECTIONS": len(wrong)}, indent=2))
        for r in wrong[:5]:
            print(f"    {r['theorem']}  {r['binder']} -> {r['to_class']}"
                  f"   ({doomed(r, closed)})")
        return 1 if wrong else 0

    rejected = 0
    for row in rows:
        reason = doomed(row, closed)
        if reason:
            connection.execute(
                "UPDATE weakening SET verdict = 'incoherent', detail = ? WHERE id = ?",
                (f"static: {reason}", row["id"]))
            rejected += 1
    connection.commit()
    print(json.dumps({"rejected_without_compiling": rejected, "of": len(rows),
                      "remaining": len(rows) - rejected}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
