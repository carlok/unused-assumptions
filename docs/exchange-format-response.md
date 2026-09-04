# Response to the exchange-format request

2 September 2026. Implemented in `unused-assumptions` unless marked otherwise.
Nothing existing changed: same columns, same ids, same `verify.py`, same paper
tables. 53 tests and `--selfcheck` still green.

## 1. Breaks — done, with two corrections

`data/breaks.jsonl.gz`, **57,382 rows**, one per (module, theorem, binder) that
has at least one failing attempt.

Gzipped because the plain file is 63 MB and the gz is 5.2 MB. It streams line by
line exactly as jsonl does (`gzip.open(..., "rt")`). Say if you need it plain.

Two corrections to the spec.

**`fail_error` is capped at 200 characters, not 500.** That is what the store
holds: `compile_once` keeps `errors[0][:200]`. Nothing is truncated at export;
there is no more to give. Widening it needs a re-sweep.

**`blamed` is present but always `null`, and I would rather ship it null than
guess.** The reason is worth your attention: for the dominant failure mode the
stored error is exactly `failed to synthesize instance of type class` — Lean puts
the class name on the *following* line, and the sweep keeps only the first line
of the first error. So the constant you want was discarded at collection time,
across all 57,382 rows.

**Superseded, 4 September.** You tested the remedy before I spent the four days,
and it does not pay. Recompiling a 176-row slice with the whole error block
captured fills `blamed` for 28 rows, 16%, and those are exactly the rows whose
error is an instance-synthesis failure. The limit is not the capture but the
verdict: `incoherent` is a statement that cannot be stated, which names a class;
`needs_structure` is a statement that elaborates and a proof that fails, and
proofs fail with type mismatches, unsolved goals and timeouts, which name
nothing. The re-sweep is off. `blamed` stays null and is documented as
unrecoverable for four rows in five.

### What replaces it in the meantime

Every row carries `descent`: the ordered list of every candidate class tried for
that binder with its own verdict. That is strictly more than "where it broke",
and it lets you recompute the stopping point under your own ordering instead of
trusting ours. Sample:

```json
"holds_over": "AddMonoid",
"fails_at": "AddCommSemigroup",
"fail_verdict": "incoherent",
"descent": [{"to_class": "AddCommSemigroup", "verdict": "incoherent"},
            {"to_class": "AddMonoid", "verdict": "weakens"}]
```

`fails_at` is the **weakest** class that failed, ranked by the same ordinal the
paper uses. Note our store is not a sequential descent: the weakening table
proposes several candidate classes per binder and each is tried independently,
so "the first class below" is our reconstruction, not a recorded event. Use
`descent` if that distinction matters to you, and it probably does.

Verdicts kept apart as you asked: `incoherent` 44,979, `needs_structure` 6,847,
`context` 5,296, `vacuous_instance` 260. `context` is our own tooling failing to
reconstruct scope, not a fact about the theorem — treat it as missing data.

285 of the rows also carry a non-null `holds_over`: a binder that both broke
somewhere and held somewhere. Those are your dichotomies with both sides
present.

## 2. `corpus` and per-corpus MANIFEST — done

`corpus` is on every row of `survivors.jsonl` and `breaks.jsonl.gz`, taken from
the root segment of the module path.

`MANIFEST.json` gains `corpora`, a list of
`{corpus, revision, describes, toolchain, project_path}`. The existing `mathlib`
key is untouched, so nothing that reads it today breaks. `project_path` is
`null` deliberately — it is a local path and this file is published.

Only Mathlib appears so far. **TauCeti is mid-sweep**: a census is running that
takes it from 4,000 sampled attempts to all 21,997, and its prior-art gate has
not run on the new nominations. Any TauCeti export before that gate finishes
would divide a gated numerator by an ungated denominator — I hit exactly that
today and it briefly showed a threefold difference that does not exist. It will
appear once the census and gate are both complete.

**On your question about `module`:** yes, it is always the defining module.
It comes from the file the declaration was parsed out of, not from any
re-export, so importing it is sufficient to put the declaration in scope. That
is what the sweep itself relies on to compile each candidate alone.

## 3. `id` — documented, and your proposed `key` would have collided

`id` is `sha256("module|theorem|binder_index|to_class")[:16]`.

It contains **no** revision and **no** class table, so it is stable across runs.
It is finer than you assumed: it is per *target class*, not per binder, so one
(theorem, binder) has several ids.

`MANIFEST.json` now carries `id_scheme` and `key_scheme` stating this.

I added `key` as you asked, but **not** as `corpus:theorem:binder`. That form
collides: 1,663 theorem names in Mathlib alone appear in more than one module.
The shipped form is:

```
corpus:module:theorem:binder
```

deterministic by construction, on every row of both files.

## 4. Optional extras — both done

`binder_index` was already inside the id and is now its own field.

`descent` is described above.

## What I did not do

Nothing was refused. The two places I departed from the spec — `fail_error` at
200 not 500, and `key` including the module — are both cases where the request
as written could not be satisfied truthfully, and I would rather you knew than
received a field that quietly means something else.

## Regenerating

```bash
python3 tools/export.py \
  --stores '<store glob>' --mathlib <mathlib checkout> \
  --toolchain <project>/lean-toolchain \
  --corpus <another corpus checkout> \
  --signatures scrutiny/signatures.json --out <dir>
```

`--corpus` is repeatable; a directory's name becomes the corpus name.
