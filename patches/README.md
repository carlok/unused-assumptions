# Section-level patches, verified by compiling

36 patches against Mathlib at the revision in `../data/MANIFEST.json`. Each one
weakens a typeclass on a `variable` line, and **the whole file compiles after
the change**. That is the claim; nothing here rests on inference.

**One of these compiles and should not be applied.**
`Mathlib_Order_DirSupClosed__CompleteSemilatticeSup` weakens `[CompleteLattice α]`
to `[CompleteSemilatticeSup α]`. It builds. But `Order/CompleteLattice/Defs.lean`
says of that class: *"we rarely use `CompleteSemilatticeSup` (in fact, any such
object is always a `CompleteLattice`, so it's usually best to start there)"* — so
the weakening lands somewhere the library deliberately avoids. Raised by Snir
Broshi (<https://github.com/SnirBroshi>) reading the demonstration branch, and
withdrawn from it.

The patch stays here, annotated, because it is a true result. Nothing in this
pipeline asks whether the class a weakening lands in is one anyone wants to land
in; the gate is the compiler, and the compiler has no opinion about that. It is
the clearest instance so far of the gap between a weakening that holds and one
that is wanted.

**Five of these are alternatives, not additions.** Two patches for
`Algebra/Order/Group/Indicator.lean` and three for `Algebra/Order/WithTop/Untop0.lean`
rewrite the *same* `variable` line in different directions — one weakens the
algebraic class, another weakens the order. Each was verified on its own against
an unmodified file. They cannot be applied together, and applying them in
sequence silently drops the later ones because the earlier one moved the
context. Pick one per line.

The two patches for `LinearAlgebra/BilinearMap.lean` target different lines and
do coexist.

**Each patch is verified alone**, so a file carrying two weakenings at once is a
separate claim. Three files reach that state on the demonstration branch --
`LinearAlgebra/BilinearMap.lean`, `RingTheory/Localization/Basic.lean` and
`Algebra/Order/WithTop/Untop0.lean` -- and all three were rebuilt with both
changes applied. All three compile. `REPORT-master.json` records this under
`combinations_checked`, kept apart from the per-patch results because it is a
different question.

**Re-checked against a later Mathlib on 2026-09-06.** At `633b366493`
(`leanprover/lean4:v4.34.0-rc2`), 804 commits and one toolchain version after
the pinned revision, **33 of the 36 still rebuild their whole file**; none
applied and then failed. Two of the three that did not carry over were
superseded upstream in the same direction — one by `#42214`, a maintainer
removing the same unused section variable by hand and weakening it further than
this patch does — and one file was rewritten. Per-patch detail in
`REPORT-master.json`.

**One of those three was misfiled.** `Topology/EMetricSpace/Pi.lean` was recorded
as superseded because `#42688` refactored it and the patch text stopped applying.
The weakening had not stopped holding. Against the refactored file both
`[TopologicalSpace α]` and `[WeakPseudoEMetricSpace α]` can be replaced by
`[EDist α]` — two binders for one, stronger than the original patch — and the file
rebuilds at `633b366493`. Observed by Snir Broshi
(<https://github.com/SnirBroshi>) reading the demonstration branch; verified by
recompiling. Whether a patch *applies* is a fact about text, and this run treated
it as the end of the question.

These compile **file by file**. A Mathlib PR builds the whole library, and a
weakened `variable` line can break a downstream importer. That is untested here,
at either revision.

```sh
cd <your mathlib checkout>
git apply /path/to/Mathlib_Algebra_CharP_Algebra__Semiring.patch
```

## Why these and not the other 609 rows

89% of the assumptions this project weakens are written on a `variable` line, so
they belong to a section rather than to a theorem. Weakening one there changes
every declaration below it, and most of those still need the stronger class — so
a per-row patch set would be wrong far more often than right.

These 36 are the subset where it is safe, and safety was **compiled rather than
argued**:

| | |
|---|---:|
| groups where every theorem carrying the binder survived | 102 |
| of those, the binder is on a `variable` line | 68 |
| **the patched file compiles** | **36** |
| the compiler rejected it | 32 |

The middle row is the point. Inference said all 68 were safe; the compiler said
half of them were not. A declaration the sweep never tried can still depend on
the stronger class, and only building the file finds it.

`REPORT.json` lists every rejection with its first error, and every skip with
its reason.

## What a patch does not claim

That anyone wants it. These are weakenings that hold and that the file survives;
whether Mathlib considers them an improvement is a judgement no compiler makes.
The paper says the same thing about all 645 rows.
