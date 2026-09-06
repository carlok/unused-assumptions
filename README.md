# unused-assumptions

Theorems in Mathlib whose stated algebraic setting is stronger than their own
proof requires, found by machine and checkable by you.

The method is one sentence. Take a theorem, replace one instance binder with a
weaker class, keep the proof byte for byte, compile it alone. It works or it
does not, and no judgement enters.

## Do not believe the table — check it

Every row in `data/survivors.jsonl` carries the weakened declaration with the
original proof and the `open` directives of the file it came from. That is
everything needed to put the claim back in front of the compiler.

```sh
python3 verify.py --data data --selfcheck                 # the data against itself, one second
python3 verify.py --data data --repo <project> --sample 50   # a random 50, minutes
python3 verify.py --data data --repo <project> --out data/verified.txt   # all of them, about an hour
```

`<project>` is any Lean project with Mathlib as a dependency, at the revision
`data/MANIFEST.json` names. The verifier refuses to run against a different one
and prints how to check it out, because a failure there would be
indistinguishable from Mathlib having moved and the number would not mean what
it says. `--force` overrides and marks every line off-revision.

A row passes only when Lean reports no error **and** `#print axioms` shows the
declaration resting on nothing beyond `propext`, `Classical.choice` and
`Quot.sound`. Success is never inferred from the absence of an error message:
Lean tags some diagnostics as `error(lean.synthInstanceFailed):`, which does not
contain the literal `error:`, and a file full of instance failures reads as
clean to a naive scan. That mistake was made here once.

The sample run takes minutes; the full run about an hour.

## Tests

```sh
python3 -m unittest discover -s tests -v   # 53 tests, no dependencies, under a second
python3 tests/coverage.py                  # stdlib `trace`, no pip install
```

Each test encodes a defect this pipeline actually shipped, written as the
failing case rather than as an abstract property, because that is the form in
which each was found. `ENGINEERING.md` tells the stories.

Coverage is low and that is expected: most of the pipeline only runs with Lean
and a Mathlib checkout. The tests cover the pure functions, which is where every
defect actually lived.

## What is here

| | |
|---|---|
| `data/survivors.csv` | the table: theorem, the assumption as stated, the weakest class the shipped source is **verified** to prove, how far that is, the descent's own lower answer in `descent_floor_unverified` — which nothing here can check — and `assumption`, saying whether the proof never used it or merely did not need it |
| `data/survivors.jsonl` | the same, plus the source `verify.py` recompiles |
| `data/verified.txt` | the expected verifier output |
| `data/MANIFEST.json` | **the Mathlib revision every row is relative to**, the toolchain, the counts |
| `data/areas-*.csv` | per-area counts under each of the two weakening tables, so the density result can be rechecked without the sweep |
| `paper/note.pdf` | the argument, ten pages, built from `paper/note.tex` |
| `paper/catalogue.pdf` | every survivor with the signature Lean prints for it, 57 pages |
| `tools/` | the sweep. Needs a Mathlib checkout and days of compute; `verify.py --selfcheck` and the tests do not; `export.py` needs both a checkout and the unpublished stores |
| `tests/` | regression tests, one per shipped defect |
| `data/verified.txt` | the verifier's own output over the published data: 644 of 645 |
| `data/unreproduced.csv` | the row that did not reproduce, with the error, kept rather than dropped |
| `data/root-invariance.jsonl` | our unused/replaceable verdict joined against a companion project's reading of each proof term's root, row by row |
| `data/replaceable.jsonl` | for each row, whether the original proof was the same one (`unused`) or the tactic found another route (`replaceable`) |
| `data/breaks.jsonl.gz` | 57,382 rows: where each weakening stopped holding, with the full descent per binder. For consumers doing the dual problem; `docs/breaks-format.md` describes the schema |
| `ENGINEERING.md` | the defects found along the way, and how |

Counts live in `data/MANIFEST.json` rather than in this file, because a number typed
into prose goes stale quietly. Six of them did before that lesson took.

## Is it spread evenly? No, and you can check that here

The other published claim is about distribution. A theorem's chance of carrying
an unused assumption is not the same across the library: 21 complete areas run
from 0.0 to 29.9 per thousand declarations, and one pooled rate fails at
**p = 0.0003** (G = 49 on 20 degrees of freedom).

That is the *clustered* figure and it is the one to quote. Treating theorems as
independent trials gives p = 2.7e-17, which is wrong: mathlib heads a file with
`variable [Field K]` and every theorem below inherits it, so the assumption being
weakened belongs to the file at least as much as to the theorem. Under the hand
table the same correction leaves no significant result at all, p = 0.13, and the
paper says so.

```bash
python3 tools/density.py --from data/areas-derived.csv --against data/areas-hand.csv
```

No Lean, no checkout, about a second. It reads integers and recomputes every
rate, interval and statistic, so editing a count changes the p-value and there
is no percentage in the file to disagree with it.

Two guards printed with the answer. `shots` is attempts per declaration, and the
ranking does not track it (rho = -0.23) -- so this is not a picture of the
weakening table. `--against` re-measures under the other table: the levels move
a lot and the order holds partly, rho = +0.80 over 20 areas, p = 2e-05.

It also prints the stores or files it read, by name, before each measurement.
That line is there because the first version of this result was +0.92, produced
by a glob that was written to mean one instrument and quietly matched both.

Two caveats that belong with the number. The two tables are not independent,
both being orderings of the same hierarchy, so treat the agreement as agreement
rather than replication. And the denominator counts declarations for which some
weakening was *proposed*, so this is density among theorems the method can ask
about, which is not the same as density among theorems.

## One row does not reproduce, and it ships

`data/verified.txt` is a full run of `verify.py` over every published row against
the pinned revision: **644 of 645 recompile clean.**

The one that does not is `MulChar.restrictHom_surjective`, and it is in
`data/unreproduced.csv` with the verifier's error rather than deleted. The sweep
recorded it as compiling; the verifier cannot make its `rewrite` step find its
pattern, under either scope construction we have tried. We do not yet know why.

A second project has since confirmed it independently and by a different route:
their sweep finds the proof term resting on `sorryAx`, which Lean inserts when a
tactic fails while still adding the declaration. Two unrelated mechanisms, one
theorem, and the only such row in either project's 645.

It stays published because a dropped row is a claim nobody can check, and
because the honest rate is more interesting than a clean one. One in 645 is
0.16%. An earlier draft of this file was going to report 1.9%, which turned out
to be three bugs in the verifier rather than anything about the library --
`ENGINEERING.md` has that story.

## Two counts of "survivors", and why they differ

`data/survivors.csv` and `paper/note.pdf` do not report the same number, and
neither is a mistake.

The data is the **union of both weakening tables** this project sweeps with: a
hand-written one and one derived from the library's own `class ... extends`
declarations. `data/MANIFEST.json` names that population and the stores it came
from. The paper's figures are the **hand-written table alone**, because that is
the population its per-area statistics and its pre-registered test were computed
over, and mixing a second instrument into them afterwards would not be the same
experiment.

An earlier export was neither: union in five areas and hand-only in nine,
because it was taken while the second sweep was partway through, and it was
labelled as the union. Outside review caught it. If you are checking a claim
against this data, read `MANIFEST.json` first -- it is generated, and this
sentence is not.

The two tables are not nested in either direction. Over the fifteen areas swept
both ways they share under a third of what they find, so the union is
substantially larger than either. `data/MANIFEST.json` names which population it
counts and which stores it came from.

## Rebuilding the paper

```sh
cd paper && pdflatex note.tex && pdflatex note.tex
cd paper && xelatex catalogue.tex && xelatex catalogue.tex && xelatex catalogue.tex
```

The catalogue needs **xelatex**, not pdflatex: Lean prints glyphs no 8-bit
engine can set.

**Twice for the note, three times for the catalogue.** One pass leaves every
citation as `[?]`, because the bibliography is resolved from the `.aux` file the
first pass writes; the catalogue's table of contents needs a third pass before
its page numbers settle. The committed PDF is the
second-pass output and matches the source in this repository; if yours shows
`[?]`, run it again rather than reporting a mismatch.

`paper/tables/` holds the generated macros. Every number the paper quotes is one
of them, so the prose cannot drift from the data — but regenerating them needs
the sweep's SQLite stores, which are not published. The committed macros are
what the committed PDF was built from.

## The revision matters

Every result is relative to one Mathlib revision, named in `data/MANIFEST.json`. A
row that fails against a different revision says nothing about this export --
Mathlib will have moved, and the failure cannot be told apart from an error
here. `verify.py` compares revisions and warns.

## What this is not

**No new mathematics.** Every survivor is a statement a competent reader grants
on sight. About half give up only one step of structure. The value is not any
row but the map: which parts of a library carry assumptions their arguments
never use. Nobody has that for any formal library, and nobody can produce it by
reading.

**Not a claim that these should all be changed.** A mechanical search can
establish that a proof survives a weaker hypothesis. It cannot establish that
anybody wants the theorem there, and the difference between those two is the
whole value of the result. Mathlib generalises when a use appears, deliberately.

**Not filtered for interest**, because the filters cannot judge it. Some rows
are auxiliary lemmas whose conclusion barely involves the weakened structure:
deep by the ordinal, empty as mathematics. They are present, and the catalogue
says so, because dropping them would claim a judgement the machine never made.

## Prior art

Alex J. Best, *Automatically Generalizing Theorems Using Typeclasses*, CICM
2021, inspects elaborated proof terms and reports typeclass fields the proof
never touches. Jesse Alama, *Eliciting Implicit Assumptions of Mizar Proofs by
Property Omission*, JAR 2013, removes a property and re-verifies -- our
epistemology exactly, fifteen years earlier, in another system.

Best judged the substitute-and-recompile variant "far too slow to be used on the
scale of a large library in a prover such as Lean, however similar techniques
have been used in the Mizar system" -- and his citation there is Alama 2013, who
had already done it. On the interactive reading he meant, he was right and still
is: per declaration this is around fifty times more expensive than reading the
proof term. What is new here is a bound rather than a refutation. The library
fits in a few days of one machine.

## Requirements

Python 3.9 or later (the code uses `dict[str, …]` and `str.removeprefix`). No
third-party packages, for anything. Lean and a Mathlib checkout are needed only
to re-verify; reading the data and running the tests needs neither.

## Licence

Apache-2.0, matching Mathlib.
