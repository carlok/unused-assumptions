#!/usr/bin/env python3
"""Export the survivors as data somebody else can check.

The stores are working files: a quarter of a gigabyte of intermediate verdicts,
in a schema that only makes sense next to the code that wrote it. What a reader
wants is the residue -- which theorem, which assumption, what it actually needs
-- and, more than that, the ability to disbelieve us and check.

So two files. `survivors.csv` is the table, for reading and sorting.
`survivors.jsonl` carries what `verify.py` needs to recompile every row against
a Mathlib checkout without ever touching a store: the weakened declaration with
the original proof byte for byte, and the file's `open` directives.

Both are projections of the stores, generated on demand. A hand-maintained copy
would drift, and this project has already published a number that disagreed with
its own companion document.

`MANIFEST.json` is the part that makes the rest falsifiable. Every result here
is relative to one Mathlib revision; without recording it, a failure a month
from now cannot be told apart from Mathlib having moved.
"""

from __future__ import annotations

import argparse
import csv
import json
import sqlite3
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from catalogue import survivors, area_of, full_name, INVERTIBLE, PLAIN
from density import stores_for
from triage import magnitude

COLUMNS = ["area", "module", "theorem", "binder", "stated", "holds_over",
           "magnitude", "loses_invertibility", "descent_floor_unverified",
           "assumption"]


def target(row: dict) -> str:
    """The weakest class this row can actually prove it holds over.

    Not the floor. The descent stage searched below `to_class`, recorded the
    name of the class it reached, and did not keep the source that proved it --
    the store has no column for one. So `floor` is a claim with no evidence
    behind it in the published data, and rebuilding a source at the floor by
    rewriting the binder does not reproduce what the descent did: six rows
    reconstructed that way fail to compile while the same rows at `to_class`
    pass.

    `to_class` is what the stored source carries and what earned the `weakens`
    verdict, so it is what a reader can check. The floor still ships, in its own
    column, marked as unverified.
    """
    return row["to_class"]


def corpus_of(module: str) -> str:
    """Which library a row came from. The root segment of the module path is
    the corpus name for every library we sweep."""
    return (module or "").split(".")[0] or "unknown"


def join_key(row: dict) -> str:
    """A key a downstream consumer can recompute without hashing.

    Deliberately includes the module. 1,663 theorem names in Mathlib alone
    appear in more than one module, so `corpus:theorem:binder` collides and
    would silently merge unrelated rows.
    """
    return f"{corpus_of(row['module'])}:{row['module']}:{full_name(row)}:{row['binder']}"


def source_at_floor(row: dict) -> str:
    """The source that proves what the row publishes.

    `holds_over` is `target()` above -- the descent's floor, often weaker than
    the class the attempt stage substituted -- while `source` was frozen at that
    attempt. The descent compiled the floor and the store kept only its name, so
    shipping `source` unchanged publishes one claim and hands the verifier a
    weaker one. 43 of 568 rows, and ten of the eleven deepest, which are the
    rows the paper's invertibility argument is built from. The verifier said
    PASS on every one, because recompiling proves something and nothing checked
    it was the advertised something.

    The repair is mechanical, because the binder is: find the binder as it
    stands in the source at whatever class the attempt put there, and rewrite it
    at the floor. Returns the source untouched when the floor is already
    present, so the rows that were right stay byte-identical.
    """
    floor = target(row)
    at_floor = row["binder"].replace(row["from_class"], floor, 1)
    if at_floor in row["source"]:
        return row["source"]
    for word in set(row["source"].replace("[", " ").replace("]", " ").split()):
        probe = row["binder"].replace(row["from_class"], word, 1)
        if probe in row["source"]:
            return row["source"].replace(probe, at_floor, 1)
    raise SystemExit(
        f"{row['theorem']}: cannot place the binder {row['binder']!r} at its "
        f"floor {floor!r} in the source. Publishing it would ship a claim the "
        f"verifier cannot check.")


def git(repo: Path, *args: str) -> str:
    try:
        out = subprocess.run(["git", "-C", str(repo), *args],
                             capture_output=True, text=True, timeout=30)
        return out.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stores", default="scrutiny/*.db")
    parser.add_argument("--mathlib", type=Path, required=True,
                        help="the Mathlib checkout the sweep ran against")
    parser.add_argument("--toolchain", type=Path,
                        help="lean-toolchain of the project that built it")
    parser.add_argument("--exclude", type=Path,
                        help="a file of theorem names that failed verification; "
                             "they are dropped and counted. A row the verifier "
                             "cannot reproduce is not evidence, whatever the "
                             "sweep recorded")
    parser.add_argument("--classification", type=Path,
                        help="replaceable.jsonl from tools/replaceable.py; adds "
                             "the `assumption` column saying whether the "
                             "original proof was the same one")
    parser.add_argument("--corpus", type=Path, action="append",
                        help="a further corpus checkout, repeatable; its "
                             "directory name is the corpus name")
    parser.add_argument("--signatures", type=Path,
                        default=Path("scrutiny/signatures.json"))
    parser.add_argument("--out", type=Path, required=True,
                        help="directory to write survivors.csv, survivors.jsonl "
                             "and MANIFEST.json into")
    args = parser.parse_args()

    rows = survivors(args.stores)

    # unused / replaceable / unclassified, joined by id. A row says the proof
    # compiles with a weaker hypothesis; this says whether it is the same proof.
    verdicts: dict[str, str] = {}
    if args.classification and args.classification.exists():
        for line in args.classification.read_text(encoding="utf-8").splitlines():
            if line.strip():
                item = json.loads(line)
                verdicts[item["id"]] = item["verdict"]

    # Every decided row, not only the ones that held. The breaks export needs
    # the failures, and deduplicating by the same (module, theorem, binder,
    # to_class) key keeps a row reached from two stores from counting twice.
    all_seen: dict[tuple, dict] = {}
    for store in stores_for(args.stores):
        link = sqlite3.connect(f"file:{store}?mode=ro", uri=True)
        link.row_factory = sqlite3.Row
        for raw in link.execute("SELECT * FROM weakening WHERE verdict IS NOT NULL"):
            item = dict(raw)
            all_seen.setdefault(
                (item["module"], item["theorem"], item["binder"],
                 item["to_class"]), item)
        link.close()
    all_rows = list(all_seen.values())
    if args.exclude and args.exclude.exists():
        drop = {n.strip() for n in args.exclude.read_text(encoding="utf-8").splitlines()
                if n.strip()}
        before = len(rows)
        rows = [r for r in rows if full_name(r) not in drop]
        print(json.dumps({"excluded_unverified": before - len(rows)}), flush=True)
    rows.sort(key=lambda r: (area_of(r["module"]), r["module"], r["theorem"],
                             r["binder"]))
    known = {}
    if args.signatures.exists():
        known = json.loads(args.signatures.read_text(encoding="utf-8"))

    args.out.mkdir(parents=True, exist_ok=True)

    with (args.out / "survivors.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=COLUMNS)
        writer.writeheader()
        for row in rows:
            floor = target(row)
            writer.writerow({
                "area": area_of(row["module"]),
                "module": row["module"],
                "theorem": full_name(row),
                "binder": row["binder"],
                "stated": row["from_class"],
                "holds_over": floor,
                "magnitude": magnitude(row["from_class"], floor),
                "loses_invertibility":
                    int(row["from_class"] in INVERTIBLE and floor in PLAIN),
                # The descent's answer, shipped because it is information and
                # marked because nothing here can check it. Blank when the
                # descent went no lower than the verified class.
                "descent_floor_unverified":
                    (row.get("floor") or "") if (row.get("floor")
                                                 and row["floor"] != floor) else "",
                # "unreadable" means the original proof term could not be read,
                # not that the weakening is doubtful: those rows verify. Shipped
                # as "unclassified" so nobody reads it as a failed row.
                "assumption": {"unused": "unused", "replaceable": "replaceable"}
                    .get(verdicts.get(row["id"], ""), "unclassified"),
            })

    with (args.out / "survivors.jsonl").open("w", encoding="utf-8") as handle:
        for row in rows:
            floor = target(row)
            handle.write(json.dumps({
                "id": row["id"],
                "corpus": corpus_of(row["module"]),
                "key": join_key(row),
                "area": area_of(row["module"]),
                "module": row["module"],
                "theorem": full_name(row),
                "namespace": (row["namespace"] or "").strip(),
                "binder": row["binder"],
                "stated": row["from_class"],
                "holds_over": floor,
                "magnitude": magnitude(row["from_class"], floor),
                "loses_invertibility":
                    row["from_class"] in INVERTIBLE and floor in PLAIN,
                "descent_floor_unverified":
                    (row.get("floor") or "") if (row.get("floor")
                                                 and row["floor"] != floor) else "",
                # What verify.py recompiles. `source` is the weakened
                # declaration with the original proof, unaltered; `opens` is the
                # file's own `open` directives, without which a name like `log`
                # becomes an autoImplicit variable.
                "opens": row["opens"] or "",
                "source": row["source"],
                "signature": known.get(full_name(row), ""),
            }, ensure_ascii=False) + "\n")

    # Corpus name -> checkout. Mathlib always; others when their rows appear.
    corpora = {"Mathlib": args.mathlib}
    for extra in (args.corpus or []):
        corpora[extra.name] = extra

    manifest = {
        "generated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "survivors": len(rows),
        # Which population this counts, spelled out, because the repository
        # publishes two counts of "survivors" that are not the same set. This
        # export is the union of every weakening table swept; the paper's own
        # figures are the hand-written table alone, which is the population its
        # per-area statistics are computed over. Both are right and shipping
        # them side by side unlabelled is not: 568 here against 462 there
        # reads as an inconsistency rather than as two questions.
        "population": "the union of every weakening table swept; the paper's "
                      "counts are the hand-written table alone and are smaller",
        "stores": sorted(Path(s).stem for s in stores_for(args.stores)),
        "areas": sorted({area_of(r["module"]) for r in rows}),
        # One entry per corpus, as the downstream dual asked. The single
        # "mathlib" key below is kept because things read it today.
        "corpora": [
            {
                "corpus": name,
                "revision": git(path, "rev-parse", "HEAD"),
                "describes": git(path, "log", "-1", "--format=%s"),
                "toolchain": ((path / "lean-toolchain").read_text(encoding="utf-8").strip()
                              if (path / "lean-toolchain").exists() else ""),
                "project_path": None,
            }
            for name, path in sorted(corpora.items())
        ],
        # What `id` hashes, so a consumer can recompute it. Note it is per
        # target class, not per binder, and that `key` is the per-binder join.
        "id_scheme": "sha256('module|theorem|binder_index|to_class')[:16]; "
                     "stable across runs; contains no revision and no corpus",
        "key_scheme": "corpus:module:theorem:binder -- deterministic, and the "
                      "join key across exports. Module is included because "
                      "theorem names are not unique across modules",
        "mathlib": {
            "revision": git(args.mathlib, "rev-parse", "HEAD"),
            "describes": git(args.mathlib, "log", "-1", "--format=%s"),
            # Deliberately not the local path: it carries a username, and this
            # file is published. The revision is what makes a row falsifiable.
        },
        "toolchain": (args.toolchain.read_text(encoding="utf-8").strip()
                      if args.toolchain and args.toolchain.exists() else ""),
        # Deliberately not a commit id. The sweep runs from a private
        # repository, so a sha from it resolves nowhere for a reader and the
        # one shipped here was both unresolvable and a revision behind the fix
        # that produced this data. The tools that matter are in this repository
        # and its own history dates them.
        "exported_by": "tools/export.py in this repository",
        "note": "Every row is relative to the Mathlib revision above. A row that "
                "fails to verify against a different revision says nothing about "
                "this export.",
    }
    # --- breaks: where the descent stopped, for the downstream dual ------
    # One row per (module, theorem, binder) that has at least one failing
    # attempt. `descent` carries every candidate class tried with its verdict,
    # so a consumer can recompute the stopping point under its own ordering
    # rather than trusting ours.
    by_binder: dict[tuple, list[dict]] = {}
    for raw in all_rows:
        by_binder.setdefault(
            (raw["module"], raw["theorem"], raw["binder"]), []).append(raw)

    # 57k rows carrying the full declaration text is 63 MB, which no
    # repository should hold. Gzipped it is 5 MB, and jsonl.gz streams line by
    # line exactly as the plain file does.
    breaks = 0
    import gzip as _gzip
    with _gzip.open(args.out / "breaks.jsonl.gz", "wt", encoding="utf-8") as handle:
        for (module, theorem, binder), group in sorted(by_binder.items()):
            failed = [r for r in group
                      if r["verdict"] not in (None, "weakens", "not_a_binder")]
            if not failed:
                continue
            # The weakest class that failed, by the same ordinal the paper uses.
            worst = max(failed, key=lambda r: magnitude(r["from_class"], r["to_class"]))
            held = [r for r in group if r["verdict"] == "weakens"]
            sample = held[0] if held else group[0]
            handle.write(json.dumps({
                "id": worst["id"],
                "corpus": corpus_of(module),
                "key": join_key(sample),
                "area": area_of(module),
                "module": module,
                "theorem": full_name(sample),
                "namespace": (sample["namespace"] or "").strip(),
                "binder": binder,
                "stated": sample["from_class"],
                "holds_over": (sorted(
                    held, key=lambda r: -magnitude(r["from_class"], r["to_class"])
                )[0]["to_class"] if held else None),
                "fails_at": worst["to_class"],
                "fail_verdict": worst["verdict"],
                "fail_error": (worst["detail"] or "")[:500],
                "blamed": None,
                "descent": sorted(
                    ({"to_class": r["to_class"], "verdict": r["verdict"]}
                     for r in group),
                    key=lambda d: d["to_class"]),
                "opens": sample["opens"] or "",
                # The source that FAILED, not the one that held. Each attempt in
                # the store carries its own text, and an earlier version of this
                # export attached the holding row's source to the failing row --
                # so for exactly the rows a consumer needs (a binder that both
                # held and broke) the failing compile had no source. Reported by
                # the downstream project, which had to rebuild them by rewriting
                # the binder, the same manoeuvre that broke six rows here.
                "source": worst["source"],
                "source_class": worst["to_class"],
                "source_at_hold": sample["source"] if held else None,
                "hold_class": (sorted(
                    held, key=lambda r: -magnitude(r["from_class"], r["to_class"])
                )[0]["to_class"] if held else None),
            }, ensure_ascii=False) + "\n")
            breaks += 1

    (args.out / "MANIFEST.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({"survivors": len(rows), "breaks": breaks,
                      "areas": len(manifest["areas"]),
                      "with_signature": sum(1 for r in rows if known.get(full_name(r))),
                      "out": str(args.out)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
