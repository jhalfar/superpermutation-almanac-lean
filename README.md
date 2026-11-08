# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`; this commit holds the second.

## This batch: a lower bound for 8 symbols

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 8 46134` | every superpermutation on 8 symbols has length at least 46,134 |

The proof is the one in `proofs/lean/n8_46134` of the main repository. Theorem D bounds a Hamiltonian path in
the overlap graph by lines that the exact weight-three chains of a strongly exitless path must satisfy. For
$`k = 8`$ it uses the two lines $`4r \le 9\delta + 56`$ and $`17r \le 38\delta + 264`$ and one statement about the
zone where both are tight. These three hypotheses are reduced, with proofs checked by the kernel, to three
equations, each saying that a finite depth-first search (`LowerBounds/DSearch.lean`) finds nothing:

```lean
theorem S.lineSearch_8_4_9_56    : S.lineSearch 8 2097152 4 9 56 400 40 251 = false := by native_decide
theorem S.lineSearch_8_17_38_264 : S.lineSearch 8 2097152 17 38 264 400 40 251 = false := by native_decide
theorem S.zoneSearch_8 : S.zoneSearch 8 2097152 4 9 56 2 17 38 264 6 400 40 251 = false := by native_decide
```

Only these three evaluations are not checked by the kernel. They trust the Lean compiler, the C compiler of
the Lean toolchain and the Lean runtime. Everything else, including the proof that a `false` answer of the
search means that no chain breaks the line, is checked by the kernel. Without `native_decide` my bound for 8
symbols stays 46,133 (Theorem C of the main repository).

The search runs as native code: `lakefile.toml` puts `LowerBounds.DSearch` (a file with no imports) in a
library of its own, `DSearchEngine`, with `precompileModules = true`, so Lake compiles it to a shared library
and loads it when it builds the three files that evaluate the search. Each search is cut into 251 parts that
run as tasks.

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma. It proves that the covering predicate of the proof
(`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
`List (Fin 8)`, and then the template statement from `SuperpermLowerBounds.covers_lower_bound_8_native`.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_eight\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice`, `Quot.sound` and the three axioms that `native_decide` records
for the three equations.

On my machine (Linux, 8 CPUs, at idle priority beside other jobs) a clean build of the project, Mathlib from
its cache, took 36 minutes with at most 9 GB of memory. The three evaluations take most of that time: they
ran beside each other and beside the rest of the build for 22, 32 and 37 minutes. Built again on their own,
the three evaluations took 22 minutes on the 8 CPUs, 2.2 CPU-hours in all. Without the compiled library
Lean's interpreter runs the search: a small test search then took 795 s on one CPU instead of 10 s, so the
evaluations need `precompileModules`. `lake env leanchecker --fresh AlmanacSolution` replays everything in
the kernel in 22 minutes with 8 GB, and the NanoDa of the Lean toolchain accepts the exported proof (12,213
declarations) with only those six axioms permitted.

## Sources and licences

The project includes Lean files from [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations)
(commit `64ab6a7`), from the Hunter-Raudvere library
[superpermutations-hunter](https://github.com/urdvr/superpermutations-hunter) (commit `d452221`) and from Jay
Pantone's [superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80) (commit `c8fb7ff`), all
under the Apache License 2.0, and from Xiaolong Liu's
[superpermutations-preimage-chain-lower-bounds](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds)
(commit `8474c74`), under CC BY 4.0. The licence texts are in [`licenses/`](licenses/). Each changed file says
at its top what changed. The fixes for Lean 4.35.0 follow the compatibility changes in Pantone's release "A
polynomial error estimate for superpermutation length". [`NOTICE`](NOTICE) has the details, and
[`SOURCES.tsv`](SOURCES.tsv) gives the SHA-256 of the original of every copied file. `AlmanacDefs.lean`,
`AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
