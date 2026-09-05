# `data/breaks.jsonl.gz` — where each weakening stopped holding

The survivors are the positive result: a theorem compiled with a weaker class
than it is stated with. This file is the other side. It records, for every
binder the sweep tried and could not weaken, what was attempted and how it
failed.

Nobody usually publishes this. It is here because the negative data answers
questions the positive data cannot — which weakenings are impossible rather than
merely unattempted, and where the boundary between the two actually sits.

**57,382 rows**, one per `(module, theorem, binder)` with at least one failing
attempt, over 36,738 distinct theorems. Gzipped: 5.6 MB here, 63 MB plain. It
streams line by line like any JSONL file.

```python
import gzip, json
for line in gzip.open("data/breaks.jsonl.gz", "rt"):
    row = json.loads(line)
```

Every row is Mathlib at the revision named in `data/MANIFEST.json`.

## Fields

| field | meaning |
|---|---|
| `id` | `sha256("module\|theorem\|binder_index\|to_class")[:16]`. Unique across the file. |
| `key` | `corpus:module:theorem:binder`. The join key against other exports. |
| `corpus` | Root segment of the module path. `Mathlib` throughout this release. |
| `area` | Top-level Mathlib area, e.g. `Algebra`. |
| `module` | The **defining** module, from the file the declaration was parsed out of rather than any re-export, so importing it puts the declaration in scope. |
| `theorem`, `namespace`, `binder` | The declaration and the instance binder that was substituted. |
| `stated` | The class the theorem is stated with. |
| `fails_at` | The **weakest** class that failed, ranked by the ordinal the paper uses. |
| `fail_verdict` | Why it failed. See below. |
| `fail_error` | Lean's first error line, capped at 200 characters. |
| `blamed` | Always `null`. See below. |
| `descent` | Every candidate class tried for this binder, each with its own verdict. |
| `opens` | The `open` directives in scope where the declaration was defined. |
| `source`, `source_class` | The failing declaration as compiled, and the class it used. |
| `holds_over`, `hold_class`, `source_at_hold` | Present on the 285 rows that also held somewhere. `null` on the rest. |

## `id` is finer than one per binder

It is derived per *target class*, so a single `(theorem, binder)` has several
ids — one for each class the table proposed. Each row here carries the id of the
attempt reported in `fails_at`. `key` is the coarser identifier and is what
joins across files.

`key` includes the module deliberately. `corpus:theorem:binder` collides:
1,663 theorem names in Mathlib alone appear in more than one module.

Neither `id` nor `key` contains a revision or a class table, so both are stable
across runs.

**Recomputing an `id` needs the name as written in the source, not the `theorem`
field.** The hash was taken at collection time from the declaration's own name,
which is the short one when it sits inside a `namespace` block; the export
publishes the qualified name. So for 35,313 of the 57,382 rows the `theorem`
value will not reproduce the id, and 22,067 will. Strip `namespace` first:

Try both forms — a declaration inside `namespace A` may still be written
`theorem A.b`, in which case the qualified name is the one that was hashed:

```python
import hashlib

def candidate_names(row):
    ns, name = (row.get("namespace") or "").strip(), row["theorem"]
    yield name
    if ns and name.startswith(ns + "."):
        yield name[len(ns) + 1:]

def reproduces(row):
    for name in candidate_names(row):
        for index in range(64):         # binder_index is not published; 43 is the largest seen
            seed = f"{row['module']}|{name}|{index}|{row['fails_at']}"
            if hashlib.sha256(seed.encode()).hexdigest()[:16] == row["id"]:
                return True
    return False
```

`binder_index` is the binder's position in the declaration's binder list. It is
not a field here, so the search above stands in for it. Do not cap it low: 43 is
the largest index in this file, and a cap of 9 silently fails on 1,267 rows.

With both names and that range, all 57,382 ids reproduce. For ordinary use treat
`id` as opaque and join on `key`.

## The four verdicts

| verdict | rows | what it means |
|---|---:|---|
| `incoherent` | 44,979 | The weakened statement cannot be stated. A sibling assumption demands the class back and nothing typechecks. |
| `needs_structure` | 6,847 | The statement elaborates and the proof fails. |
| `context` | 5,296 | **Our tooling failed to reconstruct the declaration's scope.** Not a fact about the theorem. Treat as missing data. |
| `vacuous_instance` | 260 | The binder was never a real hypothesis. |

`context` is the one to be careful with. It says the instrument could not ask the
question, not that the answer was no. Excluding those rows changes the
denominator of anything computed from this file, and it should.

## `descent` is more than `fails_at`

The store is **not** a sequential descent. The weakening table proposes several
candidate classes per binder and each is tried independently, so "the first class
below" is a reconstruction rather than a recorded event. `fails_at` is that
reconstruction under our ordering.

`descent` is the raw record, and lets you recompute the stopping point under an
ordering of your own:

```json
"stated":       "AddCommMonoid",
"holds_over":   "AddMonoid",
"fails_at":     "AddCommSemigroup",
"fail_verdict": "incoherent",
"descent": [{"to_class": "AddCommSemigroup", "verdict": "incoherent"},
            {"to_class": "AddMonoid",        "verdict": "weakens"}]
```

Use `descent` if the distinction matters, and it usually does.

## The 285 rows with both sides

A binder that broke somewhere and held somewhere carries `holds_over`,
`hold_class` and `source_at_hold` alongside the failing ones. These bracket the
boundary from both directions on the same binder, which no other row does.

## `blamed` is null, and cannot be recovered

The field names the class Lean could not synthesise. It is `null` in all 57,382
rows.

The collection mechanism explains part of it: for the dominant failure the stored
error is exactly `failed to synthesize instance of type class`, Lean puts the
class name on the *following* line, and the sweep keeps only the first line of
the first error. Widening the capture and re-sweeping was the obvious remedy and
was planned.

It was measured first, and it does not pay. Recompiling a 176-row slice with the
whole error block captured fills `blamed` for 28 rows — 16% — and those 28 are
exactly the rows whose error is an instance-synthesis failure.

The real limit is what the verdicts mean. `incoherent` is a statement that cannot
be stated, which is what a synthesis failure is, and that does name a class.
`needs_structure` is a statement that elaborates and a proof that then fails, and
proofs fail with type mismatches, unsolved goals and timeouts — none of which
have a constant to blame. Widening the capture recovers the field for one verdict
and cannot recover it for the other.

So `blamed` is documented as unrecoverable for roughly four rows in five, and the
re-sweep is not scheduled. `descent` carries strictly more than "where it broke"
and does not have this problem.

## `fail_error` is 200 characters

That is what the store holds — `compile_once` keeps `errors[0][:200]`. Nothing is
truncated at export; there is no more to give without a re-sweep.

## Regenerating

```bash
python3 tools/export.py \
  --stores '<store glob>' --mathlib <mathlib checkout> \
  --toolchain <project>/lean-toolchain \
  --corpus <another corpus checkout> \
  --signatures scrutiny/signatures.json --out <dir>
```

`--corpus` is repeatable; a directory's name becomes the corpus name. The sweep
stores themselves are gigabytes and are not published, so this reproduces the
export from data you would have to generate first — `verify.py` is the tool that
checks the published rows without them.

## A caution

This file has had a defect that the survivors could not have. `opened()` folded
every `open` directive into one clause, which is invalid when one of them carries
a selector or `hiding`, and 24 sources here would not parse standalone as a
result. It was found by a consumer, not by us, because every check we run is over
the survivors — the one population where the bug cannot occur. `ENGINEERING.md`
has the details.

Read this file as less exercised than `survivors.csv`. If something looks wrong,
it may be.
