# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d` and the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d`. This commit holds the fourth.

## This batch: 5,899 for 7 symbols

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 7 5899` | every superpermutation on 7 symbols has length at least 5,899 |

The proof is my proof of 5,899 in `proofs/lean/n7` of the main repository (the model of standard
configurations, the accounting at cost 134 and twelve finite searches), with one change: the six searches F0 to
F5 for sequences of rows are run by the search engine of `proofs/lean/n7_5900` and `proofs/lean/n7_5901`
instead of the engine of `proofs/lean/n7`. The statements are the same (every sequence with exactly $`s`$ links of
weight 4 and at most $`84 - 6s`$ holes has at most $`P_s(x)`$ rows, for the tables of `LowerBounds/PTables.lean`).
The newer engine prunes with two more rules whose soundness is proved by the kernel: the reversal cut of the
written proof of 5,900 (a shortest counterexample or its reversal has a dip no deeper than its peak) and Rule JS
of 5,901 (one of the two spellings of a junction class is enough). With a tuned potential the six searches visit
2,944,496,974 prefixes instead of 109,851,175,223.

* [`LowerBounds/PFinalK16.lean`](LowerBounds/PFinalK16.lean): the theorem of 5,899 from the twelve search
  equations, checked by the kernel. It is `PFinal.lean` with `K16.seqCap_of_k16search` in place of
  `PS.seqCap_of_search` for F0 to F5.
* [`LowerBounds/PK16F0Native.lean`](LowerBounds/PK16F0Native.lean),
  [`PK16F1Native.lean`](LowerBounds/PK16F1Native.lean), [`PK16Native.lean`](LowerBounds/PK16Native.lean): F0 to
  F5 by `native_decide`.
* [`PRingNative.lean`](LowerBounds/PRingNative.lean) and [`PProfNative.lean`](LowerBounds/PProfNative.lean): the
  ring search FR and the five profile searches FF, as in the main repository.
* [`LowerBounds/PFinalK16Native.lean`](LowerBounds/PFinalK16Native.lean): `covers_lower_bound_7_k16_native`.

Only the twelve evaluations are not checked by the kernel. They trust the Lean compiler, the C compiler of the
Lean toolchain and the Lean runtime. The three engines (`LowerBounds/PSearch.lean`, `KSearch.lean`,
`K16Search.lean`) form the library `SearchEngine` of `lakefile.toml` with `precompileModules = true`, so Lake
compiles them to a shared library and loads it when it builds the files that evaluate the searches.

| search | kept prefixes (a C program with the same rule, and the Lean counting copy for F3) | potential, parts |
|---|---|---|
| F0, chains, holes <= 84 | 1,821,996,511 | (20, 31, 5), 16 parts |
| F1, one link, holes <= 78 | 865,775,975 | (10, 16, 30), 8 parts |
| F2 .. F5 | 185,928,533 / 69,918,349 / 814,664 / 62,942 | (10, 16, 30), one part each |
| FR, rings | 460,113,709 | 1,009 parts |
| FF, five profiles | 108,741 / 27,110 / 54,979 / 103,034 / 405,173 (the counts of the main repository) | one part each |

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma. It proves that the covering predicate of the proof
(`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
`List (Fin 7)`, and then the template statement from `SuperpermLowerBounds.covers_lower_bound_7_k16_native`.

The files of the 872 batch (`K6/`) are still in the repository but nothing of this batch imports them.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_seven\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice`, `Quot.sound` and the twelve
`<name>._native.native_decide.ax_1_1` of `K16.f0k` .. `K16.f5k`, `PS.ring`, `PS.prof36`, `PS.prof26`,
`PS.prof34`, `PS.prof14`, `PS.prof4`.

On my machine (Linux under WSL 2, Mathlib from its cache, idle priority beside other jobs) I measured:

| step | time | memory |
|---|---|---|
| clean `lake build AlmanacSolution`, at most 6 Lean processes on 6 CPUs | 11 minutes (1,840 s of CPU) | at most 9.9 GB for all processes together (proportional set size) |
| the five evaluation files again, one after the other, every thread on one CPU | 764 s: F2..F5 63 s, F1 183 s, F0 404 s, FR 110 s, FF 4 s | 0.54 GB each |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 35 minutes | 9.4 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.lower_seven` | 7 s, 90 MB | 6.9 GB |
| NanoDa of the Lean toolchain on that export, 1 CPU, the three axioms and the twelve native ones permitted | 32 s, "Checked 14507 declarations with no errors" | 1.6 GB |

So the twelve evaluations take about 13 minutes on one CPU, well inside the two hours of the re-evaluation
stage, and the two kernel checks together stay under 11 GB. With 8 CPUs the build should take under 10 minutes.

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
