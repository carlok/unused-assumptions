#!/usr/bin/env python3
"""Generate candidate statements by perturbing known ones.

A filter needs something to filter. This produces the something: take a theorem
from a reference corpus, render its statement as a closed proposition, and
change one thing about it.

Most perturbations are false and many do not typecheck. That is expected and it
is why the scrutiny exists; the generator's job is volume and determinism, not
plausibility. Every candidate records exactly which theorem it came from and
what was changed, so a survivor can always be traced back.

Output is JSONL, one candidate per line, appendable and greppable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


# `theorem name binders : conclusion :=` -- the statement is everything between
# the name and the `:=` that opens the proof.
THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][\w.']*)\s*(?P<statement>[^:=]*?:.*?)\s*:=",
    re.M | re.S,
)
BINDER_RE = re.compile(r"[\(\{\[⦃]")
VARIABLE_RE = re.compile(r"^variable\s+(.+?)$", re.M)
BOUND_NAME_RE = re.compile(r"^[\(\{\[⦃]\s*([\w'\s]+?)\s*:")
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][\w.']*)", re.M)
END_RE = re.compile(r"^end(?:\s+([A-Za-z_][\w.']*))?\s*$", re.M)


def namespace_at(source: str) -> list[tuple[int, str]]:
    """Offset checkpoints of the enclosing namespace.

    A candidate has to be elaborated where its statement was written. A theorem
    inside `namespace ADEInequality` refers to `sumInv`, which does not resolve
    in a bare context, and the resulting `Unknown identifier` looks exactly like
    an ill-typed perturbation while being nothing of the sort.
    """
    events: list[tuple[int, str, str]] = []
    for match in NAMESPACE_RE.finditer(source):
        events.append((match.start(), "open", match.group(1)))
    for match in END_RE.finditer(source):
        events.append((match.start(), "close", match.group(1) or ""))
    events.sort()
    stack: list[str] = []
    checkpoints: list[tuple[int, str]] = [(0, "")]
    for offset, kind, name in events:
        if kind == "open":
            stack.append(name)
        elif stack and stack[-1] == name:
            # Only a named `end` closes a namespace. A bare `end` closes an
            # anonymous section, which was never pushed, and popping on it threw
            # away the enclosing namespace for the whole rest of the file --
            # `NumberField.mixedEmbedding` became the empty namespace, and every
            # declaration after that point was elaborated in the wrong place.
            stack.pop()
        checkpoints.append((offset, ".".join(stack)))
    return checkpoints


def enclosing(checkpoints: list[tuple[int, str]], offset: int) -> str:
    current = ""
    for point, name in checkpoints:
        if point > offset:
            break
        current = name
    return current


def parse_binders(text: str) -> list[str]:
    """Split a run of binders into individual ones, respecting nesting."""
    out: list[str] = []
    opening = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
            continue
        if text[i] not in opening:
            break
        depth, start = 0, i
        while i < n:
            if text[i] in opening:
                depth += 1
            elif text[i] in opening.values():
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            i += 1
        else:
            break
        out.append(text[start:i])
    return out


def variables_at(source: str) -> list[tuple[int, list[str]]]:
    """File-level `variable` binders, as offset checkpoints.

    Mathlib declares most of a theorem's context outside the theorem: between
    71% and 94% of files per area use `variable`. A statement rendered from the
    theorem's own binders alone leaves those names unbound, so it cannot
    elaborate however it is namespaced. This was the largest single cause of
    apparent ill-typedness.

    Scoping is approximated: `section`/`end` and `namespace`/`end` both clear
    what they opened. Over-including a binder costs an unused hypothesis, which
    elaborates fine; under-including costs the candidate.
    """
    events: list[tuple[int, str, object]] = []
    for match in VARIABLE_RE.finditer(source):
        events.append((match.start(), "vars", parse_binders(match.group(1).strip())))
    for keyword in ("section", "namespace"):
        for match in re.finditer(rf"^{keyword}\b", source, re.M):
            events.append((match.start(), "open", None))
    for match in re.finditer(r"^end\b", source, re.M):
        events.append((match.start(), "close", None))
    events.sort(key=lambda item: item[0])

    scopes: list[list[str]] = [[]]
    checkpoints: list[tuple[int, list[str]]] = [(0, [])]
    for offset, kind, payload in events:
        if kind == "open":
            scopes.append([])
        elif kind == "close":
            if len(scopes) > 1:
                scopes.pop()
        else:
            scopes[-1].extend(payload or [])
        checkpoints.append((offset, [b for scope in scopes for b in scope]))
    return checkpoints


OPEN_RE = re.compile(r"^open\s+(?!scoped\b.*\bin\b)(.+?)$", re.M)


def opens_at(source: str) -> list[tuple[int, list[str]]]:
    """File-level `open` directives, as offset checkpoints.

    A declaration is elaborated with whatever its file had opened, and
    reproducing only its namespace is not the same thing: a file that says
    `open Real` gives its theorems `log`, and without it `log` becomes an
    autoImplicit variable and the statement fails as "Function expected".
    That was the largest single cause of the typeclass sweep's own failures.

    `open X in` is skipped: it belongs to the declaration that follows it, not
    to the file. Scope ends are ignored, so this over-approximates -- an extra
    open is cheap, and when it does bite it says "ambiguous", which is
    classified as our failure rather than a verdict.
    """
    directives: list[str] = []
    points: list[tuple[int, list[str]]] = [(0, [])]
    for match in OPEN_RE.finditer(source):
        line = match.group(1).strip()
        if line.endswith(" in") or not line:
            continue
        directives = directives + [f"open {line}"]
        points.append((match.start(), directives))
    return points


def needed(available: list[str], statement: str) -> list[str]:
    """The file-level binders a statement actually refers to, transitively.

    An instance binder is pulled in when its type mentions a name already
    included, so `{C : Type u}` drags `[Category C]` along with it.
    """
    names: dict[str, str] = {}
    for binder in available:
        match = BOUND_NAME_RE.match(binder)
        if match:
            for name in match.group(1).split():
                names[name] = binder
    chosen: dict[str, None] = {}
    text = statement
    changed = True
    while changed:
        changed = False
        for binder in available:
            if binder in chosen:
                continue
            match = BOUND_NAME_RE.match(binder)
            bound = match.group(1).split() if match else []
            body = binder.split(":", 1)[1] if ":" in binder else binder
            mentioned = any(re.search(rf"(?<![\w'.]){re.escape(n)}(?![\w'])", text) for n in bound)
            depends = binder.startswith("[") and any(
                re.search(rf"(?<![\w'.]){re.escape(n)}(?![\w'])", body)
                for other in chosen for n in (BOUND_NAME_RE.match(other).group(1).split()
                                              if BOUND_NAME_RE.match(other) else []))
            if mentioned or depends:
                chosen[binder] = None
                text += " " + body
                changed = True
    return [b for b in available if b in chosen]


def strip_comments(source: str) -> str:
    """Blank `--` line comments and nestable `/- -/` blocks, keeping offsets."""
    out: list[str] = []
    depth = 0
    i, n = 0, len(source)
    while i < n:
        two = source[i : i + 2]
        if depth == 0 and two == "--":
            while i < n and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if two == "/-":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if two == "-/" and depth:
            depth -= 1
            out.append("  ")
            i += 2
            continue
        out.append(" " if depth and source[i] != "\n" else source[i])
        i += 1
    return "".join(out)


def split_binders(statement: str) -> tuple[list[str], str] | None:
    """Separate a theorem's binders from its conclusion.

    `(a : X) {b : Y} (h : P a) : Q a b` becomes `["(a : X)", "{b : Y}",
    "(h : P a)"]` and `Q a b`. Returns None when the split is ambiguous, which
    is common and never worth guessing at.
    """
    binders: list[str] = []
    i, n = 0, len(statement)
    closing = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    while i < n:
        if statement[i].isspace():
            i += 1
            continue
        if statement[i] == ":":
            conclusion = statement[i + 1 :].strip()
            return (binders, conclusion) if conclusion else None
        if statement[i] not in closing:
            return None
        depth, start = 0, i
        while i < n:
            if statement[i] in closing:
                depth += 1
            elif statement[i] in closing.values():
                depth -= 1
                if depth == 0:
                    i += 1
                    break
            i += 1
        else:
            return None
        binders.append(statement[start:i])
    return None


def is_hypothesis(binder: str) -> bool:
    """A binder that looks like a proof obligation rather than data.

    Heuristic and deliberately conservative: a hypothesis is an explicit binder
    whose type mentions a relation. Getting this wrong costs an ill-typed
    candidate, which the next stage discards anyway.
    """
    if not binder.startswith("("):
        return False
    body = binder[1:-1]
    if ":" not in body:
        return False
    kind = body.split(":", 1)[1]
    return any(token in kind for token in
               ("=", "<", "≤", "≥", ">", "∈", "∣", "≠", "Prime", "Coprime", "Odd", "Even"))


def render(binders: list[str], conclusion: str) -> str:
    """A closed proposition: `∀ binders, conclusion`."""
    if not binders:
        return conclusion.strip()
    return "∀ " + " ".join(binders) + ", " + conclusion.strip()


def perturbations(binders: list[str], conclusion: str) -> list[tuple[str, str, str]]:
    """Every one-change variant of a statement, as (kind, detail, proposition)."""
    out: list[tuple[str, str, str]] = []

    # Dropping a hypothesis asks the question a mathematician asks first: does
    # the theorem actually need that assumption?
    for index, binder in enumerate(binders):
        if is_hypothesis(binder):
            remaining = binders[:index] + binders[index + 1 :]
            out.append(("drop_hypothesis", binder, render(remaining, conclusion)))

    # Replacing a literal with a universally quantified variable asks whether
    # the result was ever about that particular number.
    for literal in sorted(set(re.findall(r"(?<![\w.])([2-9]|[1-9]\d)(?![\w.])", conclusion))):
        generalized = re.sub(rf"(?<![\w.]){literal}(?![\w.])", "kGen", conclusion)
        out.append(("generalize_literal", literal,
                    render(binders + ["(kGen : ℕ)"], generalized)))

    # Strengthening the conclusion, and weakening a hypothesis, both produce a
    # strictly stronger claim. Usually false; occasionally the interesting case.
    if "≤" in conclusion:
        out.append(("strengthen_conclusion", "≤ to <",
                    render(binders, conclusion.replace("≤", "<", 1))))
    for index, binder in enumerate(binders):
        if "<" in binder and is_hypothesis(binder):
            weakened = binders[:index] + [binder.replace("<", "≤", 1)] + binders[index + 1 :]
            out.append(("weaken_hypothesis", binder, render(weakened, conclusion)))

    return out


def candidates(path: Path, root: Path) -> list[dict]:
    try:
        source = strip_comments(path.read_text(encoding="utf-8", errors="replace"))
    except OSError:
        return []
    module = ".".join(path.relative_to(root).with_suffix("").parts)
    checkpoints = namespace_at(source)
    variable_points = variables_at(source)
    open_points = opens_at(source)
    found: list[dict] = []
    for match in THEOREM_RE.finditer(source):
        name, statement = match.group(1), match.group("statement")
        if len(statement) > 600 or "\n\n" in statement:
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
        directives: list[str] = []
        for point, scoped in open_points:
            if point > match.start():
                break
            directives = scoped
        context = needed(available, statement)
        binders = context + binders
        for kind, detail, proposition in perturbations(binders, conclusion):
            proposition = " ".join(proposition.split())
            if len(proposition) > 800:
                continue
            found.append({
                "id": hashlib.sha256(proposition.encode()).hexdigest()[:16],
                "source_module": module,
                "source_theorem": name,
                "namespace": enclosing(checkpoints, match.start()),
                "opens": "\n".join(directives),
                "perturbation": kind,
                "changed": " ".join(detail.split()),
                "proposition": proposition,
            })
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="corpus source root, e.g. <mathlib>/Mathlib")
    parser.add_argument("--out", type=Path, required=True, help="JSONL destination")
    parser.add_argument("--limit-files", type=int, help="stop after this many source files")
    parser.add_argument("--area", help="restrict to one top-level area, e.g. NumberTheory")
    args = parser.parse_args()

    files = sorted(args.root.rglob("*.lean"))
    if args.area:
        files = [p for p in files if p.relative_to(args.root).parts[:1] == (args.area,)]
    if args.limit_files:
        files = files[: args.limit_files]

    seen: set[str] = set()
    kept = 0
    with args.out.open("w", encoding="utf-8") as sink:
        for path in files:
            for candidate in candidates(path, args.root):
                if candidate["id"] in seen:
                    continue
                seen.add(candidate["id"])
                sink.write(json.dumps(candidate, ensure_ascii=False) + "\n")
                kept += 1
    print(json.dumps({"source_files": len(files), "candidates": kept,
                      "out": str(args.out)}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
