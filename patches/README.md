# Section-level patches, verified by compiling

36 patches against Mathlib at the revision in `../data/MANIFEST.json`. Each one
weakens a typeclass on a `variable` line, and **the whole file compiles after
the change**. That is the claim; nothing here rests on inference.

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
