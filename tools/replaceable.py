#!/usr/bin/env python3
"""Did the proof survive because it never used the assumption, or because the
tactic found another one?

Every row we publish says a theorem compiles with a weaker hypothesis. That
sentence covers two different facts and the paper cannot currently tell them
apart.

**Unused.** The elaborated proof term is the same one, modulo the substituted
class. The assumption was dead weight and removing it changes nothing.

**Replaceable.** The proof term is different: re-run in the weaker setting, a
tactic searched again and found another route. The assumption was not unused. It
was replaceable, which is a weaker and more interesting claim, and it is the
effect Best predicted and did not measure.

The test is one compile per row. The original theorem is already in the imported
environment, so only the weakened declaration is elaborated here; both proof
terms are then read out of the environment and their used-constant sets
compared.

    python3 tools/replaceable.py --repo <mathlib checkout> --data data \
        --out data/replaceable.jsonl [--worker 0 --of 2] [--sample 50]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import verify

CONSTS_RE = re.compile(r"CONSTS (\S+) :: \[(.*?)\]", re.S)
PLUMB_RE = re.compile(r"PLUMB (\S+) :: \[(.*?)\]", re.S)


def probe_for(row: dict) -> str:
    """The weakened declaration, then a metaprogram reading both proof terms.

    `ConstantInfo.value?` returns none for theorems in this toolchain, so the
    `.thmInfo` constructor is matched directly. That cost an hour; the symptom
    is every row reporting NOVALUE and looking like a corpus with no proofs in
    it, which is this project's usual failure wearing a new hat.
    """
    name = f"w{row['id']}"
    body = verify.source_for(row).replace(f"\n\n#print axioms {name}\n", "")
    # `_root_.Foo` in the source means the declaration is `Foo`, but the store
    # recorded it under the enclosing namespace. 11 rows.
    original = row["theorem"]
    if "_root_." in original:
        original = original.split("_root_.", 1)[1]
    return body + f"""
open Lean in
run_cmd do
  let env ← Lean.getEnv
  for n in [`{name}, `{original}] do
    match env.find? n with
    | some (.thmInfo v) =>
        let used := v.value.getUsedConstants.toList
        let plumbing := used.filter fun c =>
          -- Substituting a class necessarily changes which classes, parent
          -- projections and instances the term mentions. Lean is asked which
          -- those are rather than guessing from naming: classes and structures
          -- directly, `Parent.toChild` projections by shape, and instances by
          -- the `inst` prefix. A lemma like `Field.mul_comm` is not plumbing
          -- even though its prefix is a class, which is why the `to` test
          -- matters.
          Lean.isClass env c || Lean.isStructure env c || c.isInternal
            || (match c with
                | .str p t => (Lean.isClass env p || Lean.isStructure env p)
                                && t.startsWith "to"
                | _ => false)
            || (match c with | .str _ t => t.startsWith "inst" | _ => false)
        IO.println s!"CONSTS {{n}} :: {{used}}"
        IO.println s!"PLUMB {{n}} :: {{plumbing}}"
    | some _ => IO.println s!"NOTTHM {{n}}"
    | none   => IO.println s!"MISSING {{n}}"
"""


def classify(weak: set[str], orig: set[str], plumbing: set[str]) -> str:
    """Same proof, or a different one?

    Compare only the constants that are not typeclass plumbing. Substituting a
    class necessarily changes which classes, structures and parent projections
    the term mentions --- `Field`, `CommSemiring`, `Field.toSemifield` --- and
    those differ for any substitution whatever, so counting them would call
    every row replaceable.

    A first attempt matched the two class names as substrings and got this
    wrong: `CommSemiring` contains neither `Field` nor `CommRing`, so a row
    whose only difference was class plumbing was reported as a different proof.
    Lean knows what is a class and what is a structure projection; asking it
    beats pattern-matching its naming conventions.

    What remains is the lemmas the proof cites. If those are the same, the same
    proof ran and the assumption was never used. If the weakened proof reaches
    for something the original did not, a tactic searched again and found
    another route.
    """
    diff = (weak ^ orig) - plumbing
    return "unused" if not diff else "replaceable"


def run(repo: Path, row: dict, timeout: int) -> tuple[str, dict]:
    text = probe_for(row)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as handle:
        handle.write(text)
        path = Path(handle.name)
    try:
        out = subprocess.run(["lake", "env", "lean", str(path)], cwd=repo,
                             capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired):
        return "timeout", {}
    finally:
        path.unlink(missing_ok=True)

    report = out.stdout + out.stderr
    found = {m.group(1): {c.strip() for c in m.group(2).split(",") if c.strip()}
             for m in CONSTS_RE.finditer(report)}
    plumbing: set[str] = set()
    for m in PLUMB_RE.finditer(report):
        plumbing |= {c.strip() for c in m.group(2).split(",") if c.strip()}
    name = f"w{row['id']}"
    original = row["theorem"]
    if "_root_." in original:
        original = original.split("_root_.", 1)[1]
    if name not in found or original not in found:
        # Not a verdict about the theorem: we could not read one of the two
        # terms. Kept apart from unused/replaceable so it cannot be counted as
        # either.
        return "unreadable", {"detail": report.strip().splitlines()[-1][:160]
                              if report.strip() else "no output"}
    weak, orig = found[name], found[original]
    verdict = classify(weak, orig, plumbing)
    diff = (weak ^ orig) - plumbing
    return verdict, {
        "weak_constants": len(weak),
        "original_constants": len(orig),
        "differing": sorted(diff)[:12],
        "differing_total": len(diff),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--data", type=Path, default=Path("data"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--sample", type=int)
    parser.add_argument("--worker", type=int, default=0)
    parser.add_argument("--of", type=int, default=1)
    args = parser.parse_args()

    rows = [json.loads(line) for line
            in (args.data / "survivors.jsonl").read_text(encoding="utf-8").splitlines()
            if line.strip()]
    if args.sample:
        rows = rows[: args.sample]
    if args.of > 1:
        rows = rows[args.worker :: args.of]
    print(json.dumps({"rows": len(rows)}), flush=True)

    tally: dict[str, int] = {}
    with args.out.open("w", encoding="utf-8") as handle:
        for index, row in enumerate(rows, 1):
            verdict, detail = run(args.repo, row, args.timeout)
            tally[verdict] = tally.get(verdict, 0) + 1
            handle.write(json.dumps({"id": row["id"], "key": row.get("key"),
                                     "theorem": row["theorem"],
                                     "stated": row["stated"],
                                     "holds_over": row["holds_over"],
                                     "verdict": verdict, **detail},
                                    ensure_ascii=False) + "\n")
            handle.flush()
            print(json.dumps({"done": index, "of": len(rows),
                              "theorem": row["theorem"][:44], "verdict": verdict,
                              **tally}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
