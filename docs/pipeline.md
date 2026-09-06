# The relax-constraints hunt, end to end

Conclave's main track as of 21 August 2026. Perturbation is retired to a
secondary role: it yielded one genuine tightening from 4,593 candidates, and the
reason is structural rather than fixable. Every statement it reaches is one edit
from something a person already wrote down and thought about, so a true one is
nearly always already known, folklore, or false.

Weakening a typeclass assumption asks a question nobody asks unless they need
the answer. Mathlib generalises reactively -- a use appears, so a theorem gets
generalised -- and nothing sweeps. That space is unexamined by construction, and
folklore is precisely where people have already thought.

## Stages

| # | stage | tool | status |
|---|---|---|---|
| -- | drive one sprint, resumably | `tools/sprint.sh` | built |
| -- | derive the weakening table | `tools/derive_edges.py` | built |
| 0 | collect | `tools/typeclass.py --collect-only` | built |
| 0b | signatures | `tools/signatures.py` | built |
| 0c | precheck | `tools/precheck.py` | built |
| 1 | attempt | `tools/typeclass.py` | built |
| 2 | triage | `tools/triage.py` | built |
| 3 | prior art | `tools/priorart.py` | built |
| 4 | descent | `tools/floor.py` | built |
| 5 | deliberation | --- | not in this release |
| 6 | literature | --- | human, deliberately |
| 7 | write-up | `tools/note_tables.py`, `tools/catalogue.py` | built |
| 8 | submission | --- | not built |

Run it with `tools/sprint.sh <name> <area>...`. Areas already finished are
skipped, the check derived from the store rather than a marker file, so the same
command resumes after a reboot, a kill, or a fortnight. Set `SWEEP_TABLE` to
sweep with a derived table instead of the hand-written one.

### Before anything: preflight

`sprint.sh` runs `#check @Nat.succ_le_succ` and exits 1 if it fails. A toolchain
bump leaves the Mathlib dependency's oleans unreadable and `lake build` exits 0
without fixing them; every `#check` then resolves nothing, `not_a_binder` never
runs because it needs a signature to count against, and every attempt returns
`incoherent`. That store looks exactly like a finished sweep. It has happened
twice. The fix is `lake exe cache get`, and three seconds of preflight
distinguishes the two cases.

### The two tables

The hand-written table is 48 edges over 27 classes, and every wrong edge is a
silent false negative: the weakened statement fails to elaborate and is recorded
as "the proof needs the structure", the opposite of the truth. `derive_edges.py`
reads `class X ... extends Y` from the library instead -- 374 edges over 224
classes, single-argument at both ends -- and that direction cannot be wrong,
since X carries everything Y does by construction.

They are **not** nested. On Algebra: 89 survivors found by both, 62 only by the
hand table, 50 only by the derived one. The hand table encodes multi-step jumps
a direct-parent table cannot reach in one hop; the derived table names classes
nobody thought to list. Sweep with one or the other and say which; a comparison
across areas needs a single instrument.

`magnitude()` scores 4 for any pair whose families differ, and `FAMILY` does not
list the derived classes, so their targets default to the deepest bucket.
Extend `FAMILY` and `STRENGTH` before comparing depth across tables.

### 0. Collect

Walk a Mathlib area. For each theorem take its statement, its proof, its
enclosing namespace, the file's `open` directives, and the file-level
`variable`s it appears to need. For every instance binder in the `WEAKENINGS`
table, emit one attempt per weaker class.

`WEAKENINGS` stays hand-written. A wrong edge makes the weakened statement fail
to elaborate, which is then recorded as "the proof needs the structure" -- the
opposite of the truth, and silent. A table can be reviewed.

### 1. Attempt

Rebuild the declaration standalone: weakened binder, **original proof byte for
byte**, compiled alone. Alone, because a batch lets a parse error in one
declaration corrupt its neighbours and lets a proof cite a sibling.

Two shots. The file's `open` directives cut both ways -- without them a name like
`log` becomes an autoImplicit variable, and with them a directive such as `open
scoped zeta` names a notation namespace that does not resolve outside its own
file. A `context` verdict from the first shot is retried without the preamble
before being recorded.

| verdict | meaning |
|---|---|
| `weakens` | compiles clean, no `sorryAx`. A **nomination**, not a result |
| `needs_structure` | the statement elaborates, the proof fails |
| `incoherent` | the statement cannot be stated -- a sibling instance demands the stronger class |
| `context` | this tool could not reproduce the declaration's setting. Not a result |
| `timeout` | |

Success comes from `#print axioms`, never from the absence of an error, and the
error scan matches Lean's tagged form (`error(lean.synthInstanceFailed):`) as
well as the plain one. Both lessons were paid for: a text scan for the literal
`"error:"` reads a file full of instance failures as clean.

### 2. Triage

Split `weakens` in two, mechanically, because reporting one number would
overstate the result and the overstatement would be invisible afterwards.

- `magnitude` -- how much structure the weakening gives up. `Field ->
  DivisionRing` drops commutativity; `Field -> CommRing` drops inverses, and a
  theorem about fields that holds over any commutative ring was not a theorem
  about fields. An ordinal drop within one hierarchy, fixed at 4 for an edge
  that forgets an operation, since the ordinals are not comparable across
  hierarchies.
- `breadth` -- how many of a theorem's binders weaken at once. All of them is
  the signature of a plumbing lemma.

`structural` needs magnitude >= 3 and breadth <= 2. Everything else is
`reusability`: the same proof in a weaker setting, worth having and worth
nothing to write about.

### 3. Prior art

Replace the proof with `exact?` and see whether Mathlib closes the weakened
statement unaided. Three outcomes, and the distinction between the last two is
the point:

- `new` -- the library does not prove it. The only one that continues.
- `known` -- some *other* Mathlib result proves it. Real weakening, already done.
- `not_a_weakening` -- the citation is the theorem's **own** name. `needed()`
  reconstructs a superset of the file-level `variable`s a declaration actually
  takes, since Lean includes only those a statement uses, so the binder we
  weakened was never a hypothesis. Our artefact. Counting it with `known` would
  flatter the tool; counting either as a finding would be false.

The first eight nominations were all `not_a_weakening`, which is why this stage
exists ahead of anything expensive.

### 4. Descent

The sweep reports the edge its table contains, which is a fact about the table
rather than about the theorem. Its headline survivor came back as
`Field -> CommRing`; the proof holds over a `Semiring`, three steps lower.

Descent substitutes every weaker class in turn and reports the weakest that
compiles. No hierarchy reasoning and no judgement: the compiler decides, and
classes the hierarchy does not order simply both hold or both fail. One
compilation per candidate per survivor, which is affordable only here, at the
end, where survivors are few.

This stage exists because a person asked whether the reported edge was the real
one. It should not have taken a person. Any stage whose answer is *"our table
stopped here"* is reporting on itself, and the pipeline should notice that
without being asked -- which is now what the weakening table is for: it
nominates a starting point, and descent decides how far the nomination goes.

### 5. Deliberation

Judging which surviving relaxations are worth having is not mechanical, and no
tool here attempts it. The stage exists in a private companion to this
repository and is not part of the release; what it contributed to the published
result is one filter, `reaches_conclusion` in `tools/triage.py`, which came from
reading a survivor list and noticing that the sweep was flattening a real
distinction.

The point worth keeping is structural: deliberation sits **on top of** a machine
result rather than in place of one. Whatever judges these cannot fake the
premise, because the compile already happened.

### 6. Literature check

Deliberately not automated and deliberately **before** the write-up. An agent
asked to certify novelty will certify it: there is no mechanical check on an
overstated novelty claim, unlike falsity, which sampling catches. Stage 3 settles
what Mathlib knows; whether a result is published elsewhere is a question for a
person with a search engine.

The cost of skipping it is already on the record. The first target chosen for deliberation was
folklore -- the compositum discriminant identity needs its coprimality
hypothesis, which anyone who knows conductor-discriminant expects -- and that was
established by reading it, after the fact.

### 7. Write-up

`tools/note_tables.py` emits every figure the note quotes as a LaTeX macro, and
`tools/catalogue.py` renders every survivor with the signature Lean prints for
it. Prose that spells a number out goes stale the moment the next area lands,
and goes stale quietly, because nothing rereads a paragraph. Six figures went
stale before that rule was applied everywhere.

`tools/export.py` writes the published CSV and JSONL, and `verify.py` recompiles
every row of them from a clean checkout. That last one is what makes this a
result rather than a report.

## What it has produced

77% of Mathlib, 116,265 attempts, 462 survivors, none of them new mathematics.
Throughput 1,537 attempts an hour on one laptop, which is the answer to Best's
objection that this is too slow for a library of this size.

Two documents come out of stage 7, both generated: `paper/note.tex` argues
from four statements, `paper/catalogue.tex` lists all 645 with the signature
Lean prints for each. Every figure in the note is a macro from `note_tables.py`,
because prose that spells a number out goes stale quietly. Six hand-written
figures went stale anyway before they were all converted.


## Beyond the sweep

| tool | what it does |
|---|---|
| `tools/export.py` | the published CSV and JSONL, plus a manifest naming the Mathlib revision every row is relative to |
| `verify.py` | recompiles every published row from a clean checkout; reads the data and never a store |
| `tools/shortlist.py` | narrows survivors to those worth offering individually: magnitude >= 3, not auxiliary, signature known |
| `tools/jointly.py` | asks whether a theorem's several weakenings hold *together*, which nothing else does |
| `tools/density.py` | per-area yield rate, whether one rate explains every area, and whether the ranking survives a change of table |
| `tests/` | one test per defect that shipped, stdlib only |

**`jointly.py`** closes a gap that was invisible for a long time. `breadth` in
triage counts binders that weaken **independently**, each verified with the
others at full strength. Whether they hold at once is a different question and
is not implied: two weakenings can fail together where each succeeds apart,
because a sibling instance may need one of the two original classes.

525 theorems have a single weakening and nothing to ask. 41 have two or three,
which is 47 subsets, so it enumerates rather than searching. Finding a maximal
jointly-holding set is the shape minimal-unsatisfiable-subset algorithms exist
for, and they exist because enumeration is infeasible; here the expensive oracle
keeps the space small by construction.

**`density.py`** asks whether the phenomenon is spread evenly. Counting
survivors rewards an area for being large; this divides by the declarations the
sweep actually considered and asks whether one rate explains every area. It does not: fifteen complete areas span 0.0 to 29.9 findings per
thousand, G = 118.7 on 14 degrees of freedom, p = 1.1e-18.

Three guards, because a per-area ranking is easy to produce and hard to trust.
`shots` is attempts per declaration, and the rank correlation between rate and
shots is -0.29, so the ranking is not a picture of the table. `reach` is
declarations per file, which separates an area the method cannot ask about
(CategoryTheory, 0.3) from one it asked and found little in. And `--against`
re-measures under the other weakening table: levels differ a lot, order holds
partly, rho = +0.74 over fifteen areas at p = 0.0016.

It prints the stores it read before each measurement, and takes a
comma-separated list so a store set can be named rather than pattern-matched.
That is not convenience. The first version of the cross-table number was +0.92,
produced by a glob written to mean the hand-table sweeps that also matched the
derived-table store -- one instrument against a union of both. Nothing in a
store records which table produced it, so no check over the data could have
found it.

Both tails are written out rather than imported, so the repository keeps its
no-dependency promise, and both are checked against published critical values
in the tests: five points for chi-square, seven for Student t. The t tail
earned the seven. Its first version returned negative probabilities at every
degree of freedom above 1, and it had been checked at df = 1.

## The rule that keeps earning its place

**A verdict category at 0% or 100% is a bug until proven otherwise.**

Every defect found in this pipeline has failed the same way:
something that resolved nothing looked exactly like something that contained
nothing. A signature pass that resolved 0 of 55 read as a corpus with no
declarations. A statement split at the wrong character read as 129 novel
findings. None was visible in a summary; all were found by opening one case and
reading the Lean output.
