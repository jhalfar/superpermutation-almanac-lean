# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations).

## This batch: two upper bounds for large $`n`$

Write $`F_3(n) = n! + (n-1)! + (n-2)!`$. [`AlmanacSolution.lean`](AlmanacSolution.lean) states:

| statement | meaning |
|---|---|
| `Almanac.AsymptoticUpperAt 3 0` | for every $`\varepsilon > 0`$ and all large $`n`$ there is a superpermutation of length at most $`F_3(n) + \varepsilon\,(n-3)!`$, so the coefficient of $`(n-3)!`$ tends to 0 |
| `Almanac.AsymptoticUpperAt 4 8` | for every $`\varepsilon > 0`$ and all large $`n`$ there is a superpermutation of length at most $`F_3(n) + (8 + \varepsilon)\,(n-4)!`$ |

The construction is Jay Pantone's, with nested block levels added
(`proofs/lean/constant43586371` of the main repository, where these results first appeared on 2026-10-24). Both
proofs are checked by the kernel alone: they use `propext`, `Classical.choice` and `Quot.sound` and nothing else,
with no `native_decide`.

[`UpperLinks.lean`](UpperLinks.lean) holds the linking lemmas. They prove that the covering predicate of the
proofs is `Almanac.IsSuperpermutation` over `List (Fin n)`, that `Almanac.fact` is `Nat.factorial`, and then the
two template statements from `Uniform.coefficient_tends_to_zero` and `UniR.rate_R8_eventually`.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.upper_coeff3_zero\n#print axioms AlmanacSubmission.upper_coeff4\n' > Axioms.lean
lake env lean Axioms.lean
```

On my machine a clean build of the project, Mathlib from its cache, took 9 minutes with at most 8 Lean
processes and 18 GB of memory. `lake env leanchecker --fresh AlmanacSolution` replays everything in the kernel in
about 8 minutes, and NanoDa 0.4.19 accepts the exported proofs.

## Sources and licences

The project includes Lean files from Jay Pantone's
[superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80) (commit `c8fb7ff`) and from
[jhalfar/superpermutations](https://github.com/jhalfar/superpermutations) (commit `64ab6a7`), both under the
Apache License 2.0 (texts in [`licenses/`](licenses/)). Each changed file says at its top what changed. The fixes
for Lean 4.35.0 follow the compatibility changes in Pantone's later release. [`NOTICE`](NOTICE) has the details,
and [`SOURCES.tsv`](SOURCES.tsv) gives the SHA-256 of the original of every copied file. `AlmanacDefs.lean`,
`AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
