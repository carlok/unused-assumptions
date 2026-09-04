# Section-level patches, verified by compiling

36 patches against Mathlib at the revision in `../data/MANIFEST.json`. Each one
weakens a typeclass on a `variable` line, and **the whole file compiles after
the change**. That is the claim; nothing here rests on inference.

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
