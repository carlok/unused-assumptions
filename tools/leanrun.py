#!/usr/bin/env python3
"""Running Lean, safely, and reconstructing a declaration's setting.

Extracted from a larger tool. Four things here were paid for rather than
designed, and each has a comment saying what it cost.
"""

from __future__ import annotations

import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def run_bounded(command: list[str], cwd: Path, timeout: int,
                env: dict[str, str] | None = None) -> tuple[str, str]:
    """Run a child in its own process group and kill the group on timeout.

    `lake env lean` spawns `lean` beneath it. subprocess.run kills only the
    direct child, so a timeout leaves a grandchild holding a compiled Mathlib
    -- gigabytes that nothing reclaims, accumulating one per timeout until the
    machine dies. That is what took this one down.
    """
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    try:
        return process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            process.kill()
        process.communicate()
        raise


def available_gb() -> float:
    """Memory the system could hand a new Lean process, in gigabytes."""
    try:
        out = subprocess.run(["vm_stat"], capture_output=True, text=True, timeout=10).stdout
    except (OSError, subprocess.TimeoutExpired):
        return float("inf")
    size = 4096
    first = out.splitlines()[0] if out else ""
    if "page size of" in first:
        size = int(re.search(r"page size of (\d+)", first).group(1))
    pages = 0
    for name in ("Pages free", "Pages inactive", "Pages speculative"):
        match = re.search(rf"{name}:\s+(\d+)", out)
        if match:
            pages += int(match.group(1))
    return pages * size / (1024 ** 3)


def wait_for_memory(minimum_gb: float = 4.0, poll: int = 30) -> None:
    """A Lean process with Mathlib wants gigabytes. Starting one with none free
    is how the previous run took the machine down with it."""
    waited = 0
    while available_gb() < minimum_gb:
        print(json.dumps({"waiting_for_memory_gb": round(available_gb(), 1),
                          "waited_seconds": waited}), flush=True)
        time.sleep(poll)
        waited += poll


ERROR_RE = re.compile(r"error(?:\([^)]*\))?:\s*(.*)")


def errors_in(report: str) -> list[str]:
    return ERROR_RE.findall(report)


AXIOMS_RE = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", re.M)


ROOT_IMPORT = os.environ.get("SWEEP_IMPORT", "Mathlib")


HEADER = ("".join(f"import {name.strip()}\n" for name in ROOT_IMPORT.split(",")
                  if name.strip())
          + "\nset_option maxHeartbeats 400000\n")


def header_for(row: dict) -> str:
    """What a standalone candidate must import to stand up.

    Mathlib has an umbrella, so importing it is enough. Another corpus need not:
    TauCeti's root module is deliberately empty, its lakefile building by glob
    instead, so there is nothing to import that brings the corpus with it. A
    candidate from such a library has to import the module it came from, which
    is the only thing that supplies its namespace and its own file's imports.

    Doing so also puts the original theorem in scope, so a tactic can close the
    weakened goal by citing it. That is not new -- importing Mathlib has the
    same effect for a Mathlib candidate -- and it is what the prior-art gate
    exists to catch.
    """
    module = (row.get("module") or "").strip()
    if not module or module.split(".")[0] == "Mathlib":
        return HEADER
    return HEADER.replace("\nset_option", f"import {module}\n\nset_option")


def opened(row: dict) -> str:
    """Put a candidate back in the scope its source declaration had.

    Two things, and both were learned by losing candidates to them.

    The namespace, with every prefix. `open A.B` brings in what lives in `A.B`;
    sitting inside `namespace A` then `namespace B` also gives you `A`, so
    opening only the leaf loses everything declared at the outer level.

    The file's own `open` directives. A declaration is elaborated with whatever
    its file had opened, and 3,664 of 4,593 candidates come from a file with at
    least one. Without them a name like `log` is not unknown -- it becomes an
    autoImplicit variable, and the statement fails as "Function expected",
    which is indistinguishable from an ill-typed perturbation.

    Everything is folded into a single `open ... in`, so it binds to this
    declaration and nothing after it. A bare `open` is a command and would
    persist for the rest of a batched file, letting one candidate elaborate on
    a neighbour's scope. `open scoped` cannot be merged that way and stays a
    separate command; it carries notation rather than names, so the leak it
    causes is inert.
    """
    plain: list[str] = []
    scoped: list[str] = []
    for line in (row.get("opens") or "").splitlines():
        body = line.strip().removeprefix("open ").strip()
        if not body:
            continue
        (scoped if body.startswith("scoped") else plain).append(body)
    namespace = (row.get("namespace") or "").strip()
    if namespace:
        parts = namespace.split(".")
        plain.extend(".".join(parts[: i + 1]) for i in range(len(parts)))
    # Plain names first, scoped second. A scoped notation namespace is often
    # reachable only *through* one of the plain ones: `open scoped sigma`
    # resolves as `ArithmeticFunction.sigma` and is an unknown namespace until
    # `ArithmeticFunction` is open. The sweep emits the scoped clause first and
    # gets away with it only because it also emits every directive a second
    # time, raw, ahead of both; verify.py was corrected and this copy was not.
    names = list(dict.fromkeys(" ".join(plain).split()))
    prefix = f"open {' '.join(names)} in\n" if names else ""
    prefix += "".join(f"open {directive} in\n" for directive in dict.fromkeys(scoped))
    return prefix
