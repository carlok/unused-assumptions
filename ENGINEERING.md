# What it took to believe the output

A mechanical search produces a number, and the number is worthless until
somebody has read enough of the individual results to know what it is counting.
This file is the evidence for that claim. Every defect below survived code
review, produced a plausible number, and was caught only by opening one case and
reading what the compiler actually said.

They share one shape:

> **Something that resolved nothing looked exactly like something that
> contained nothing.**

A lookup stage that returns no matches is indistinguishable, at the summary
level, from a corpus that has nothing to match. Both print zero. That is the
failure mode of this entire class of tool, and the rule it produces is:

> **A verdict category at 0% or 100% is a bug until proven otherwise.**

It has paid for itself repeatedly, and every story below is one of the times.

---

## The imports the signature pass did not make

The stage that asks Lean for a declaration's real type built its `#check` file
from `import Mathlib` alone, never importing the module the declaration lives
in. For Mathlib that is harmless — the umbrella covers everything. For any other
library every name failed to resolve.

`not_a_binder`, the filter that rejects a weakening of an assumption the theorem
does not actually carry, only fires when a signature resolves. So on that corpus
it never fired at all: rows the Mathlib pipeline discards *before compiling*
were instead compiled and came back `incoherent`. The corpus scored as
pathologically over-constrained.

The log said `"dropped": 9, "unresolved": 3991, "kept": 0`. It was read past.

**Cost:** a headline comparison, published internally, claiming one corpus was
three times more over-constrained than another. The real gap, after the fix, is
7 to 18 percentage points depending on the area -- Algebra 77.8% against 89.4%
-- and in NumberTheory the intervals overlap outright. Every other entry on this
page gives both numbers; this one said "a fraction of that" for four revisions,
which makes a threefold error sound like a rounding adjustment.

## The statement split at the wrong character

Several stages cut a declaration at the first `:=` to separate statement from
proof. A named argument writes `:=` *inside* the statement — `(R := R)`,
`(A := A)` — and a structure instance ends with `where` and no `:=` at all.

Two consequences, found six weeks apart in two different files:

- The prior-art stage produced a file that never parsed, so `exact?` never ran,
  so every row was recorded as novel. **129 of 129.**
- The filter that rejects an assumption the conclusion never mentions read its
  "conclusion" out of the *proof text*. A theorem stated over `R` and `S` whose
  conclusion mentions neither, but whose proof body says `where left R S`,
  passed a filter built to reject exactly that.

**Fix:** split at the `:=` at bracket depth zero, and stop at a depth-zero
`where`. Shared, so the next stage to need it cannot get it wrong differently.

## Leaf compared against a dotted name

The prior-art stage distinguishes *the library already proves this* from *we
weakened something that was never a hypothesis* by asking whether the citation
names the theorem itself. It compared the citation's last component against the
theorem's **full** name. For any theorem whose own name contains a dot, the
comparison could never match, and its own-name citations were filed as genuine
prior art.

**Cost:** 23 rows in one corpus and 63 in another, in the wrong bucket. Detected
by reading a list of "already known" results and noticing that one cited itself.

## Lean's diagnostics captured as mathematics

The regex that reads `#check` output captures everything up to the next
`^name :` line. Lean writes diagnostics into the same stream, so an error
following a check was absorbed into the preceding declaration's signature —
temp-file path, line number and all.

25 of 388 cached signatures carried text like

```
… ↑⊤.annihilator /var/folders/…/tmpqpi2u51_.lean:11:8:
error(lean.unknownIdentifier): Unknown identifier `bddBelow_gauge_set` …
```

and one of them was **printed in a published document**. It had been checked
for: the source was grepped for `/Users`, `/private` and `/tmp`. macOS puts temp
files under `/var/folders`.

**Lesson:** read the built artefact, not the source that produces it.

## Rows counted as findings

A binder that survives at two different target classes is one finding recorded
twice, and areas swept by parallel runners land in more than one store. Four
places counted rows.

The paper said 472 survivors; its own companion catalogue said 462. The
catalogue was right.

The first fix was worse than the bug: deduplicating the whole table by
`(module, theorem, binder)` collapsed the **attempt** count too, because every
binder is tried against several target classes. The attempt total fell by ten
thousand before the arithmetic gave it away. That key identifies a *finding*,
never an *attempt*.

## A build that succeeded and fixed nothing

After a toolchain bump the dependency's compiled artefacts became unreadable.
`lake build` on the root project exits 0 without rebuilding a dependency, so
everything looked fine. Every `#check` then resolved nothing — see the first
entry — and the sweep scored every attempt `incoherent`.

The resulting store is indistinguishable from a completed sweep.

**Fix:** the driver now compiles `#check @Nat.succ_le_succ` before starting and
exits with the Lean error if it fails. Three seconds against two days. It has
fired twice.

## A scanner that read one line at a time

The weakening table can be derived from the library's own `class X extends Y`
declarations, which is better than a hand-written list because `extends` cannot
be wrong in the direction that matters. The scanner read the source line by
line. Mathlib writes

```lean
class DivisionRing (K : Type*)
  extends Ring K, DivInvMonoid K, Nontrivial K where
```

with the `extends` on the next line, so the scanner saw `class DivisionRing`
extending nothing at all. 224 classes and 374 edges should have been 313 and
545: **89 classes missing entirely**, `DivisionRing`, `BooleanAlgebra` and
`ConditionallyCompleteLinearOrder` among them.

Found sideways. The question was whether a depth ordinal derived from the
`extends` graph reproduces the hand-written one. It does for the multiplicative
*group* hierarchy -- zero ordering inversions out of 28 -- and fails badly for
rings, 71 out of 210. The failure turned out to be `DivisionRing` sitting at
depth zero, which is only possible if the table believes it is a root.

The check that found this is worth more than the fix: **compare a derived
quantity against an independently produced one and explain every disagreement.**

## Unknown, scored as maximum

The depth measure returns "forgets an operation" -- the top of the scale --
whenever two classes belong to different families. The family table listed only
the hand-written classes, so a class it had never heard of had no family, and
therefore differed from everything.

Every weakening into an unlisted class scored maximum depth. It was noticed
first in one area, where 18 of 30 apparently deep survivors were that default,
and diagnosed as a local oddity. It was not local: across the whole sweep **40
of 64 deep survivors were deep for that reason alone.**

Recording the second look rather than only the fix, because the first look
understated it by half and the reason was that one area is not a sample.

The fix is not a better guess. A pair the tables cannot place now returns
`UNRANKED`, which is below the threshold, so a deep test excludes it by
arithmetic and a caller that wants to report it can. The classes worth placing
were placed from the library's own `extends`; the ones that resist it stay
unranked and are counted separately.

**A fallback branch will be taken, and it should return the least interesting
value rather than the most.** A default that flatters the result is a guess
wearing a measurement's clothes.

## A glob that matched one thing too many

The per-area yield result rests on measuring the same library under two
different weakening tables and asking whether the ranking changes. The two
sweeps live in separate stores, and the second one was named by the pattern
`s[wp]*.db` -- meaning, to its author, the two hand-table sweeps.

It also matches `sprint-3.db`, the derived-table store being compared against.
So one instrument was compared with a union of both, which agrees with itself
better than two instruments do. The published correlation was **+0.92**. It is
**+0.73**.

Nothing in a store records which weakening table produced it; that lives in how
the sweep was invoked. No consistency check over the data could have caught
this, and none of the four numbers that must agree disagreed.

**Fix:** the tool prints the stores it read, by name, before every measurement,
and accepts a comma-separated list so the correct set can be named rather than
pattern-matched. A glob that matches too much looks exactly like a glob that
matches right, and the only defence is making the input list an output.

## A statistic checked at the one point where it worked

The same result quotes a rank correlation, so the correlation needed a p-value,
so the Student t tail was written out -- this repository having no dependencies
and a p-value being a poor reason to acquire one.

The first version returned **negative probabilities** at every degree of freedom
above 1. Two errors: the guard against a vanishing denominator substituted the
floor where it should substitute the floor *and then invert*, and the recurrence
takes two half-steps per iteration, which do not collapse into one loop.

It was checked against a published critical value and passed, because the value
chosen was df = 1 -- the only one it got right. Seven are checked now, and the
chi-square tail beside it has five.

**One point is not a check.** It is an anecdote with a number in it.

## Reading a stage that had not run

Order was reported as having produced no surviving weakening at all, out of
2,041 declarations, and that went into a findings document and a commit message.

The prior-art gate had not yet run on it. Every row sat at `subsumed IS NULL`,
the query counted only `subsumed = 'new'`, and the answer was zero. Order has 44
findings over 38 theorems and sits second in the ranking.

This is the first defect in this file that is not in the pipeline. It is in the
reading of it, by someone who had written the rule at the top of this page and
then read a zero anyway, four hours after committing a paragraph about zeros
that mean nothing was computed.

## A claim the store could not support

The descent stage takes a surviving weakening and pushes it further down the
hierarchy, recording the weakest class it reaches as `floor`. It compiles that
class to find it. It does not keep the source that compiled, because the store
has no column for one.

So `floor` is a name with no evidence behind it, and the export published it as
the row's claim. Rebuilding a source at the floor by rewriting the binder does
not reproduce what the descent did: six rows reconstructed that way fail to
compile, while the same rows at the class the stored source actually carries
pass. `Finset.mul_aux` is the plain case — `to_class` is `CommMonoid`, the
stored source carries `[CommMonoid G]` and earned its verdict there, and
`floor` says `Semigroup` with nothing attached.

**Cost:** 62 of 645 published rows claimed a class the artifact could not check,
and a fix that rewrote the source to match the claim turned six of them from a
quiet mismatch into an outright failure. The claim is now the class the source
carries; the floor ships in its own column, named `descent_floor_unverified`.

**Lesson:** a stage that computes something must keep what proved it, or it has
computed a rumour. This one had been running for weeks.

## A verifier that reproduced the result but not the procedure

The sweep compiles a candidate with the file's own `open` directives and, on a
context error, once more without them. Some directives name a notation
namespace that does not resolve from outside its own file, which is a fact about
our preamble rather than about the weakening, so the sweep does not hold it
against the row. The store keeps `opens` either way and records nothing about
which of the two attempts won.

`verify.py` always included the directives. It therefore failed rows the sweep
had passed, for a reason with nothing to do with the mathematics, and those
failures were indistinguishable from rows that genuinely do not hold.

Found while diagnosing eighteen failures that had been provisionally written off
as a non-reproduction rate about the library — a number that was going into the
paper as a limitation. Seventeen of the eighteen were defects in the checker,
described on this page and the two sections below it. One was real.

**Lesson:** reproducing a result is not enough; the check has to reproduce the
*procedure*. Where the procedure has a branch, the artifact should record which
branch was taken. `verify.py` reports which variant succeeded; the published
rows do not carry it.

## A claim the store could not support

`floor` is the class the descent stage reached by searching below the one the
table proposed. The store has a column for its name and none for the source that
proved it, so the descent compiled something and kept only the answer.

That was invisible while nothing tried to check it. Then a verifier did.
Rebuilding a source at the floor by rewriting the binder does not reproduce what
the descent did -- six rows reconstructed that way fail to compile while the same
rows at the proposed class pass -- so for 62 of 645 published rows the table
printed one claim and the shipped source carried a weaker one.

The export now publishes the class the source actually carries, and ships the
floor in its own column marked unverified. The cost is not small and is worth
stating plainly: **at the verifiable class the deepest survivors in the paper's
discovery set number zero, where the floor gave eleven.** An argument about what
happens at the deep end cannot be made from data whose deep end is a class
nobody can recompile.

**A measurement you cannot reproduce is not a measurement, however carefully it
was taken.**

## The verifier reproduced the result without reproducing the procedure

Three defects in three days, all in the checker rather than the data, and all
failing the same way: a row that was fine was reported as broken.

**An axiom report Lean spells two ways.** `#print axioms` prints "depends on
axioms: [...]" for a proof that needs some and "does not depend on any axioms"
for a proof that needs none. The pattern matched only the first, so **40 rows
were failed for being cleaner than required**. This check had already been wrong
once in the same direction, demanding all three standard axioms and failing
proofs that used two; the fix then allowed subsets, and a subset rule cannot
reach a case the library does not phrase as a set.

**Scope bound to the file instead of the declaration.** The sweep folds a
declaration's `open` directives into one `open ... in` clause. The verifier
emitted them as bare commands, which are file-scoped and permanent, and brought
enough into scope to make an identifier ambiguous that the scoped form resolves.
One row was written up as unreproducible because of it.

**A duplicate that was load-bearing.** Removing that duplication then broke a row
that had compiled for weeks. `open scoped sigma` resolves as
`ArithmeticFunction.sigma` and is an unknown namespace until `ArithmeticFunction`
is open, and the sweep emits scoped clauses *first* -- which works only because it
also emits every directive a second time, raw, ahead of both. The plain clause
now comes first, which is the order the dependency requires and needs no
duplicate. The same ordering bug was still latent in the sweep, masked there. A downstream
project reading this file went and looked, found it, and reported it back --
along with a second one this page had not noticed at all.

Together these three were reported as a 1.9% non-reproduction rate and written
up as a fact about the library. The true rate is **one row in 645**, and the
other twelve were this file's subject rather than the library's.

**A new instrument pointed at old results will find its own bugs first.** Budget
for that, and do not publish the first number it gives you.

## Two bugs found by a reader, not by us

A project consuming this artifact read the tools and found two defects that had
survived every check here.

**`wait_for_memory` raises `NameError`.** It calls `json.dumps` and
`time.sleep`; `leanrun.py` imports neither. Six tools call it. It never fired
because `available_gb()` normally clears its threshold on the first poll, so the
loop is never entered -- a code path that never runs looks exactly like one that
works, which is this page's subject in a new place. It fired for them
immediately, because they run against a live sweep on a machine with two Mathlib
processes already resident.

**The scoped-open ordering was fixed in one copy and not the other.**
`verify.py` emits the plain clause before the scoped one, because
`open scoped sigma` resolves as `ArithmeticFunction.sigma` and is unknown until
`ArithmeticFunction` is open. `leanrun.py` kept the old order, masked because the
sweep also emits every directive raw ahead of both clauses. This file recorded it
as "still latent in the sweep" and left it there.

Both are fixed, in all three copies, with tests that force the paths.

**A rule written down is not a rule enforced.** The first was invisible to a
test suite that never made memory scarce; the second was written into this file
as a known latent bug and then not acted on. The reader who found them had
neither of our habits and no reason to trust the code, which is the whole
argument for publishing it.

## A promised re-sweep that would have recovered nothing

The exchange format carries a `blamed` field -- the class Lean could not
synthesise -- and it is null in all 57,382 rows. The diagnosis here was that the
sweep keeps only the first line of the first error and Lean writes the class name
on the second, so the constant was discarded at collection time. The remedy that
followed from it was to widen the capture and re-sweep, and that was written down
as a commitment.

The consuming project tested it before we spent the days. Recompiling a 176-row
slice with the whole error block captured fills `blamed` for 28 rows, 16%, and
those 28 are exactly the rows whose error is an instance-synthesis failure.

The diagnosis was right about the mechanism and wrong about the population. What
limits the field is not how the error was captured but what the verdicts mean:
`incoherent` denotes a statement that cannot be stated, which is what a synthesis
failure is and which does name a class, while `needs_structure` denotes a
statement that elaborates and a proof that then fails -- and proofs fail with
type mismatches, unsolved goals and timeouts, none of which have a constant to
blame. Widening the capture recovers `blamed` for one verdict and cannot recover
it for the other.

`blamed` stays null and is documented as unrecoverable for four rows in five. The
re-sweep is not scheduled.

**A correct diagnosis does not validate the remedy it suggests.** The first line
of the error really was all that was kept. That fact justified a two-day run
whose ceiling nobody had measured, and the measurement cost one afternoon.

---

## What follows from all this

Three practices, each bought with a defect:

**Read individual cases.** Not summaries. Every defect here was invisible in
aggregate and obvious in one worked example.

**Distrust round numbers.** 0%, 100%, and *exactly* the value you hoped for.

**Verify the artefact you ship**, not the pipeline that produced it. That is why
`verify.py` exists in this repository, reads only the published data, and is
meant to be run by someone who believes none of the above.

The newest tool is the first time that rule changed a design rather than
diagnosing a bug. `density.py` computes a per-area yield and a p-value, and it
reads the sweep's SQLite stores, which are gigabytes and are not published --
so shipped as written it would have sat beside the data unable to read it,
which is this file's whole subject. It now exports the counts the statistic
consumes, and a test recomputes the published p-value from the published CSV.

And a fourth, learned late: **write the test as the failing case.** The suite in
`tests/` is one test per defect above, and it has already caught two things
beyond regressions -- that a copy of a tool had drifted from the one being
fixed, and that a test's own example had gone stale when the class it named as
"unlisted" was subsequently listed. Both were invisible to reading.
