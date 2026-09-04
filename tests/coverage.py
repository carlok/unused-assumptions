#!/usr/bin/env python3
"""Line coverage for the test suite, using the standard library only.

    python3 tests/coverage.py
    python3 tests/coverage.py --detail triage

`coverage.py` is the better tool and this is not trying to replace it. But this
repository has no dependencies on purpose -- its claim is that a stranger runs
one command -- and requiring a pip install to measure the tests of the thing
that must run without one is a bad trade. `trace` ships with Python and is
enough to answer the only question worth asking here: which lines of the
pipeline has anything ever executed?

Coverage is reported per module, and the untested parts are named rather than
summarised into a percentage, because a percentage is exactly the kind of number
this project keeps learning not to trust.
"""

from __future__ import annotations

import argparse
import sys
import trace
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WATCHED = ["triage", "catalogue", "priorart", "signatures", "derive_edges",
           "export", "typeclass", "precheck", "floor", "leanrun", "perturb"]


def executable_lines(path: Path) -> set[int]:
    """Lines that could run: not blank, not a comment, not a bare docstring
    delimiter. Crude, and it overcounts decorators and continuation lines, so
    the figure it produces is a floor rather than a claim."""
    lines, in_doc = set(), False
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        text = raw.strip()
        ticks = text.count('"""') + text.count("'''")
        if in_doc:
            if ticks:
                in_doc = False
            continue
        if ticks == 1:
            in_doc = True
            continue
        if not text or text.startswith("#") or ticks >= 2:
            continue
        if text.startswith(("import ", "from ", "@", ")", "]", "}", "else:", "try:")):
            continue
        lines.add(number)
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--detail", help="name a module to list its unrun lines")
    args = parser.parse_args()

    sys.path.insert(0, str(ROOT / "tools"))
    sys.path.insert(0, str(ROOT))

    tracer = trace.Trace(count=1, trace=0, ignoredirs=[sys.prefix, sys.exec_prefix])
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"))
    runner = unittest.TextTestRunner(verbosity=0, stream=open("/dev/null", "w"))
    tracer.runfunc(runner.run, suite)

    counts = tracer.results().counts
    hit: dict[str, set[int]] = {}
    for (filename, lineno), _ in counts.items():
        hit.setdefault(Path(filename).stem, set()).add(lineno)

    print(f"  {'module':<16} {'run':>5} {'runnable':>9} {'':>6}")
    total_hit = total_all = 0
    for name in WATCHED:
        path = ROOT / "tools" / f"{name}.py"
        if not path.exists():
            path = ROOT / f"{name}.py"
        if not path.exists():
            continue
        runnable = executable_lines(path)
        covered = runnable & hit.get(name, set())
        total_hit += len(covered)
        total_all += len(runnable)
        share = 100 * len(covered) / len(runnable) if runnable else 0
        print(f"  {name:<16} {len(covered):>5} {len(runnable):>9} {share:>5.0f}%")

    print(f"\n  {'total':<16} {total_hit:>5} {total_all:>9} "
          f"{100 * total_hit / max(total_all, 1):>5.0f}%")
    print("\n  Low numbers are expected and not a target. Most of this pipeline "
          "only runs\n  with Lean and a Mathlib checkout; the tests cover the "
          "pure functions, which\n  is where every defect this project shipped "
          "actually lived.")

    if args.detail:
        path = ROOT / "tools" / f"{args.detail}.py"
        if not path.exists():
            path = ROOT / f"{args.detail}.py"
        missed = sorted(executable_lines(path) - hit.get(args.detail, set()))
        source = path.read_text(encoding="utf-8").splitlines()
        print(f"\n  unrun in {args.detail}.py:")
        for number in missed[:40]:
            print(f"    {number:>4}  {source[number - 1].strip()[:78]}")
        if len(missed) > 40:
            print(f"    … and {len(missed) - 40} more")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
