#!/usr/bin/env python3
"""Ask whether Mathlib already knows a weakening before anyone writes it up.

The prover pass taught this the expensive way. Of twenty candidates it closed,
fifteen were proved by citing a theorem that already existed in more general
form -- true, and worth nothing. The tell was in the proof term, and nothing
short of looking at it would have caught them.

The same trap is open here. A weakening whose statement Mathlib can already
prove by library search is not a finding, however cleanly it compiled with its
original proof. So: replace the proof with `exact?` and see whether the library
closes the statement on its own.

That is the mechanical half of the folklore gate, and it is the whole of what
this tool claims. Whether a result is published *outside* Mathlib is a
literature question, it needs a search this script does not do, and it belongs
before any write-up rather than after. `docs/pipeline.md` records it as a human
step for that reason -- an agent asked to certify novelty will certify it.
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

from leanrun import (run_bounded, wait_for_memory, opened, errors_in,
                        HEADER, header_for, AXIOMS_RE)


def why(theorem: str, citation: str) -> str:
    """Two ways `exact?` can close a weakened statement, and they differ.

    Citing some *other* Mathlib result means the library already proves the
    general form: the weakening is real and known. Citing the theorem's own
    name means the binder was never load-bearing -- `needed()` reconstructs a
    superset of the file-level `variable`s a declaration actually takes, since
    Lean includes only those a statement uses, so we weakened something that
    was not a hypothesis. That is our artefact, not a result about Mathlib, and
    counting the two together would flatter the tool.
    """
    head = citation.removeprefix("exact ").strip()
    cited = head.split()[0] if head else ""
    # Leaf against leaf. The `theorem` column may itself be dotted
    # (`IsComplexLinearMap.add`), and comparing a bare leaf to a dotted name
    # never matches -- filing the theorem's own name under "Mathlib already
    # knows this" instead of "we weakened something that was not a hypothesis".
    return ("not_a_weakening"
            if cited.rsplit(".", 1)[-1] == theorem.rsplit(".", 1)[-1]
            else "known")


def statement_of(source: str) -> str | None:
    """The declaration up to the `:=` that introduces the proof.

    Not the *first* `:=`. A named argument writes one inside the statement --
    `frobeniusEnd R p (A := ...)`, `regularMul (R := R) (H := H)` -- and cutting
    there truncates the statement mid-term. The file then fails to parse,
    `exact?` never runs, and the row is recorded as "Mathlib does not know
    this": a false novelty claim, which is the one error this gate exists to
    prevent. A whole corpus came back 129-for-129 novel that way.

    The proof's `:=` is the one at bracket depth zero.
    """
    depth = 0
    for i, ch in enumerate(source):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and source[i:i + 2] == ":=":
            return source[:i].rstrip()
    return None


def library_proves(repo: Path, row: dict, timeout: int) -> tuple[bool, str]:
    """Does Mathlib close the weakened statement with no help from us?"""
    statement = statement_of(row["source"])
    if statement is None:
        return False, ""
    directives = "\n".join(dict.fromkeys(
        line for line in (row.get("opens") or "").splitlines() if line.strip()))
    name = f"w{row['id']}"
    # header_for, not HEADER: a candidate from a corpus without an umbrella
    # module needs its own module imported or the statement never elaborates.
    # `exact?` cannot close a statement that does not elaborate, so the bare
    # header would silently record every such row as "Mathlib does not know
    # this" -- the one direction of error this gate exists to prevent.
    text = (header_for(row) + "\n"
            + (directives + "\n\n" if directives else "")
            + opened(row) + statement + " := by\n  exact?\n\n"
            + f"#print axioms {name}\n")
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        out, err = run_bounded(["lake", "env", "lean", str(path)], repo, timeout)
    except (OSError, subprocess.TimeoutExpired):
        return False, ""
    finally:
        path.unlink(missing_ok=True)
    report = out + err
    if errors_in(report):
        return False, ""
    match = AXIOMS_RE.search(report)
    if not match or "sorryAx" in (match.group(2) or ""):
        return False, ""
    found = re.search(r"Try this:\s*\n?\s*(?:\[apply\]\s*)?(.+)", report)
    return True, (found.group(1).strip()[:300] if found else "")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--worker", type=int, default=0,
                        help="this worker's index, 0-based")
    parser.add_argument("--of", type=int, default=1,
                        help="how many workers share the store; each takes a "
                             "disjoint stride, so the slices cannot collide")
    args = parser.parse_args()

    connection = sqlite3.connect(args.db, timeout=120)
    connection.row_factory = sqlite3.Row
    columns = {c[1] for c in connection.execute("PRAGMA table_info(weakening)")}
    for column in ("subsumed", "subsumed_by"):
        if column not in columns:
            connection.execute(f"ALTER TABLE weakening ADD COLUMN {column} TEXT")
    connection.commit()

    rows = [dict(r) for r in connection.execute(
        "SELECT * FROM weakening WHERE verdict = 'weakens' AND subsumed IS NULL")]
    if args.of > 1:
        # Disjoint strides, so two workers cannot pick the same nomination.
        rows = rows[args.worker :: args.of]
    if args.limit:
        rows = rows[: args.limit]
    subsumed = 0
    for index, row in enumerate(rows, start=1):
        wait_for_memory()
        known, citation = library_proves(args.repo, row, args.timeout)
        subsumed += 1 if known else 0
        settled = why(row["theorem"], citation) if known else "new"
        connection.execute(
            "UPDATE weakening SET subsumed = ?, subsumed_by = ? WHERE id = ?",
            (settled, citation, row["id"]))
        connection.commit()
        print(json.dumps({"checked": index, "of": len(rows), "subsumed": subsumed,
                          "theorem": row["theorem"], "verdict": settled}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
