#!/usr/bin/env python3
"""Drop weakenings of binders the theorem never had.

`needed()` reconstructs the file-level `variable`s a declaration appears to
take, by following names transitively through the statement. Lean does not work
that way: it includes only the variables a declaration actually uses, so the
reconstruction is a superset. `ClassNumber.normBound_pos` is declared with an
empty binder list and picks up nine `variable` lines, and we handed it
`[EuclideanDomain R]` -- a binder it does not have. Weakening that is a no-op
which compiles cleanly and looks exactly like a result.

Lean will say what the signature really is. `#check @Name` prints it with every
instance binder spelled out, so the fix is to ask, and to drop any candidate
whose class does not appear there with enough multiplicity.

This is a pre-filter, not a verdict about mathematics: a dropped candidate was
never a weakening in the first place.
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

from leanrun import run_bounded, wait_for_memory, opened, HEADER, ROOT_IMPORT

HEADER_ROOT = ROOT_IMPORT.split(",")[0].strip()

# `@Foo.bar : <type>` up to the next `@` at column zero, since a printed type
# wraps across lines.
# `#check @X` prints `@X : ...` when X takes implicit arguments and plain
# `X : ...` when the `@` is redundant. Requiring the `@` silently loses every
# declaration of the second kind, which is most classes.
CHECK_RE = re.compile(r"^@?([A-Za-z_][\w'.]*)\s*:\s*(.*?)(?=^@?[A-Za-z_][\w'.]*\s*:|\Z)",
                      re.M | re.S)
# Lean writes diagnostics into the same stream as `#check` output, and CHECK_RE
# captures everything up to the next `^name :` line -- so an error following a
# check is absorbed into that declaration's signature, temp-file path and all.
# Twenty-five of 388 cached signatures carried text like
#   /var/folders/.../tmpqpi2u51_.lean:11:8: error(...): Unknown identifier ...
# and one of them was printed in a document before anybody noticed.
DIAGNOSTIC_RE = re.compile(r"(?:^|\s)(?:\S*\.lean):\d+:\d+:|error\(|warning:")


def cut_diagnostics(signature: str) -> str:
    """Everything before Lean started complaining."""
    found = DIAGNOSTIC_RE.search(signature)
    return signature[:found.start()] if found else signature


INSTANCE_BINDER_RE = re.compile(r"\[\s*(?:[\w'✝]+\s*:\s*)?([A-Za-z_][\w'.]*)")


def header_for_modules(modules) -> str:
    """`import Mathlib` plus whatever module each asked-about name lives in.

    Without this the pass asks Lean about `TauCeti.Foo.bar` with only Mathlib
    imported, every name fails to resolve, and the `not_a_binder` filter
    silently does not run -- the rows go on to be compiled and come back
    `incoherent`, which is a fact about this file rather than about the corpus.
    A whole TauCeti sweep was scored that way before anyone noticed.
    """
    extra = sorted({m for m in (modules or ())
                    if m and m.split(".")[0] != HEADER_ROOT})
    if not extra:
        return HEADER
    # Before the `set_option`, not after it: an `import` following any command
    # is a syntax error, and the whole batch then resolves nothing at all --
    # which looks exactly like "the corpus has no such declarations".
    imports = "".join(f"import {m}\n" for m in extra)
    return HEADER.replace("\nset_option", f"{imports}\nset_option", 1)


def signatures(repo: Path, names: list[str], timeout: int,
               modules=None) -> dict[str, str]:
    """Ask Lean for each declaration's real type."""
    source = header_for_modules(modules) + "\n" + "".join(f"#check @{name}\n" for name in names)
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
    return {match.group(1): cut_diagnostics(match.group(2))
            for match in CHECK_RE.finditer(out + err)}


def resolve_in_scope(repo: Path, queries: list[tuple[str, str]],
                     timeout: int, modules=None) -> dict[tuple[str, str], str]:
    """Second pass: let Lean resolve the short name where it was written.

    Guessing a full name from the enclosing `namespace` lines fails in two ways
    that are common enough to matter. A declaration written `_root_.Foo.bar`
    does not live under its file's namespace at all, and `enclosing` recovers
    only what the source stacks explicitly, so a name Mathlib exports one level
    deeper is never found. Opening the namespace and asking for the short name
    sidesteps both, and Lean prints the full name it settled on.
    """
    blocks = []
    for namespace, theorem in queries:
        short = theorem.removeprefix("_root_.")
        blocks.append(opened({"namespace": namespace}) + f"#check @{short}\n")
    source = header_for_modules(modules) + "\n" + "\n".join(blocks)
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
    printed = {name: cut_diagnostics(signature) for name, signature in
               ((m.group(1), m.group(2)) for m in CHECK_RE.finditer(out + err))}
    # Match on the last component, which is what was asked for; a namespace we
    # guessed wrongly is exactly what this pass exists to tolerate.
    by_suffix: dict[str, str] = {}
    for name, signature in printed.items():
        by_suffix.setdefault(name.rsplit(".", 1)[-1], signature)
    found: dict[tuple[str, str], str] = {}
    for namespace, theorem in queries:
        short = theorem.removeprefix("_root_.").rsplit(".", 1)[-1]
        if short in by_suffix:
            found[(namespace, theorem)] = by_suffix[short]
    return found


def instance_classes(signature: str) -> dict[str, int]:
    """Class names appearing as instance binders, with multiplicity.

    Multiplicity matters: a theorem over two fields `K` and `L` really does
    offer two `Field` binders to weaken, and a theorem over one offers one.
    Names are not compared -- Lean prints `inst✝` and the argument may have been
    renamed -- so this is an over-approximation, but a far tighter one than
    reconstructing the binder list ourselves.
    """
    counts: dict[str, int] = {}
    for match in INSTANCE_BINDER_RE.finditer(signature):
        name = match.group(1).rsplit(".", 1)[-1]
        counts[name] = counts.get(name, 0) + 1
    return counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--batch", type=int, default=150)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()

    connection = sqlite3.connect(args.db)
    connection.row_factory = sqlite3.Row
    rows = [dict(r) for r in connection.execute(
        "SELECT * FROM weakening WHERE verdict IS NULL")]
    wanted: dict[str, list[dict]] = {}
    for row in rows:
        namespace = (row["namespace"] or "").strip()
        full = f"{namespace}.{row['theorem']}" if namespace else row["theorem"]
        wanted.setdefault(full, []).append(row)
    names = sorted(wanted)
    print(json.dumps({"candidates": len(rows), "declarations": len(names)}), flush=True)

    known: dict[str, str] = {}
    for start in range(0, len(names), args.batch):
        wait_for_memory()
        chunk = names[start: start + args.batch]
        mods = {r["module"] for full in chunk for r in wanted[full]}
        known.update(signatures(args.repo, chunk, args.timeout, mods))
        print(json.dumps({"resolved": len(known), "of": len(names)}), flush=True)

    # Whatever the full name missed, ask for in scope instead.
    stragglers = [full for full in names if full not in known]
    if stragglers:
        pairs, pair_modules = [], []
        for full in stragglers:
            group = wanted[full]
            pairs.append(((group[0]["namespace"] or "").strip(), group[0]["theorem"]))
            pair_modules.append(group[0]["module"])
        for start in range(0, len(pairs), args.batch):
            wait_for_memory()
            found = resolve_in_scope(args.repo, pairs[start: start + args.batch],
                                     args.timeout,
                                     set(pair_modules[start: start + args.batch]))
            for (namespace, theorem), signature in found.items():
                full = f"{namespace}.{theorem}".lstrip(".")
                known[full] = signature
        print(json.dumps({"after_scope_pass": len(known), "of": len(names)}), flush=True)

    dropped = unresolved = 0
    for full, group in wanted.items():
        signature = known.get(full)
        if signature is None:
            unresolved += len(group)
            continue
        available = instance_classes(signature)
        used: dict[str, int] = {}
        for row in group:
            source_class = row["from_class"]
            # One candidate per real binder of that class, not one per binder we
            # imagined. Ordering within a class is arbitrary; the count is not.
            if used.get(source_class, 0) < available.get(source_class, 0):
                used[source_class] = used.get(source_class, 0) + 1
                continue
            connection.execute(
                "UPDATE weakening SET verdict = ?, detail = ? WHERE id = ?",
                ("not_a_binder", f"{source_class} is not an instance binder of {full}",
                 row["id"]))
            dropped += 1
    connection.commit()
    print(json.dumps({"dropped": dropped, "unresolved": unresolved,
                      "kept": len(rows) - dropped - unresolved}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
