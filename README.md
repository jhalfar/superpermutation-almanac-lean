# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d`, the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d`, the fourth (5,899 for 7 symbols with
`native_decide`) is commit `a09f9ef`, the fifth (5,898 for 7 symbols, checked by the kernel) is commit
`5cc0ac3`, the sixth (12 and 13 symbols from Theorem C) is commit `7ed009a` and the seventh (the error after
$`2(n-4)!`$ with exponent 1/37) is commit `ad9477f`. This commit holds the eighth.

## This batch: 5,900 for 7 symbols

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 7 5900` | every superpermutation on 7 symbols has length at least 5,900 |

The proof is my proof of 5,900 in `proofs/lean/n7_5900` of the main repository. Its written proof is
`proofs/lean/n7_5900/PROOF_5900.md` there. It stands on the proof of 5,899 (the model of standard
configurations and set B of its tables) and adds the accounting at defect 15, the statements for the kernel
alone (table T' and Theorem K) and the joint statements S1 to S5:

| part | what | files in `LowerBounds/` |
|---|---|---|
| A | the accounting at defect 15: components, cuts, pieces, the knapsack | `A15Arith`, `A15Core`, `A15Cut`, `A15Pieces`, `A15Tables`, `A15Final` |
| B | the kernel alone: table T', Theorem K, the search engine for sequences and its soundness | `KDefs`, `KTables`, `KSearch`, `KSound`, `KPot`, `KRev`, `KRules`, `KFinal` |
| C | the joint statements: the joint engine, its soundness, its rules | `J15Search`, `J15Sound`, `J15Rules`, `J15Final` |
| D | the assembly from the search equations, checked by the kernel | `F5900Joint`, `KFinalK16`, `F5900K16` |
| E | the evaluations and the theorem | `KK*Native`, `KSmallNative`, `J15S*Native`, `KFinalNative`, `J15FinalNative`, `F5900K16Native` |

One thing differs from the main repository. There the part of 5,899 comes from its 22 search equations
(`PFinalNative.lean` of `proofs/lean/n7`). Here it comes from the twelve equations of my fourth batch, in which
the six searches F0 to F5 run on the engine of `proofs/lean/n7_5901` (the same statements, a smaller tree). Set
B, `Caps` and `Profiles` are the same statements either way, so only the assembly changes:

* [`LowerBounds/KFinalK16.lean`](LowerBounds/KFinalK16.lean) (new): `KS.setB_of_k16`, set B from F0 to F5 of
  `K16Search.lean` and FR, in the same way as `KS.setB_of_search` of `KFinal.lean`.
* [`LowerBounds/F5900K16.lean`](LowerBounds/F5900K16.lean) (new): `covers_5900_of_k16`, the bound from the 89
  search equations as hypotheses. It is `covers_5900_of_search` of the main repository with `caps_of_k16`,
  `profiles_of_k16` and `KS.setB_of_k16` in their places. Its axioms are `propext`, `Classical.choice` and
  `Quot.sound`.
* [`LowerBounds/F5900K16Native.lean`](LowerBounds/F5900K16Native.lean) (new):
  `covers_lower_bound_7_5900_native`, that theorem applied to the 89 evaluated equations.
* `LowerBounds/KFinalNative.lean`: without the import of `PFinalNative.lean` and without the three theorems
  that used it (they are now in `F5900K16.lean`).

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma: the covering predicate of the proof
(`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
`List (Fin 7)`, and then the template statement from `SuperpermLowerBounds.covers_lower_bound_7_5900_native`.

## What is trusted

89 equations of the form "this search returns `false`" are evaluated by `native_decide`:

| equations | files | engine |
|---|---|---|
| 12 of the proof of 5,899 (F0 to F5, FR, five profiles) | `PK16F0Native`, `PK16F1Native`, `PK16Native`, `PRingNative`, `PProfNative` | `K16Search`, `PSearch` |
| 41 for table T' and Theorem K | 36 files: `KK87Native`, `KSmallNative`, `KK0_00Native` .. `KK5Native` | `KSearch` |
| 36 for the joint statements | 36 files `J15S1_00Native` .. `J15S5Native` | `J15Search` |

For them the Lean compiler, the C compiler of the Lean toolchain and the Lean runtime are trusted. The four
engines (`LowerBounds/PSearch.lean`, `KSearch.lean`, `K16Search.lean`, `J15Search.lean`) form the library
`SearchEngine` of `lakefile.toml` with `precompileModules = true`, so Lake compiles them to a shared library and
loads it when it builds the files that evaluate the searches. Everything else, including the proofs that each
search answering `false` means what is claimed, is checked by the kernel.

The axioms of `AlmanacSubmission.lower_seven` are `propext`, `Classical.choice`, `Quot.sound` and 89 axioms
`<name>._native.native_decide.ax_1_1`: `K16.f0k` .. `K16.f5k`, `PS.ring`, `PS.prof36`, `PS.prof26`, `PS.prof34`,
`PS.prof14`, `PS.prof4`; `KS.k8`, `KS.k7`, `KS.c59`, `KS.c62`, `KS.ring`, `KS.k6`, `KS.c76`, `KS.k4`, `KS.k5`,
`KS.k3`, `KS.k1_0` .. `KS.k1_7`, `KS.k0_0` .. `KS.k0_10`, `KS.k2_0` .. `KS.k2_11`; `J15.s5`, `J15.s4`,
`J15.s3`, `J15.s2a1_0` .. `J15.s2a1_2`, `J15.s1_0` .. `J15.s1_11`, `J15.s2a2_0` .. `J15.s2a2_17`.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_seven\n' > Axioms.lean
lake env lean Axioms.lean
```

The 72 evaluation modules of 5,900 are far too large for the automatic check of the site: this batch is meant
to be built by hand. Everything else takes minutes. What I measured (Linux under WSL 2, Mathlib from its cache,
idle priority, other jobs on the machine):

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory, with the 89 evaluations replaced by `sorry` (a test copy, not this batch), 15 CPUs | 6 minutes (375 s) | at most 7.8 GB for all processes together (proportional set size) |
| the twelve evaluations of 5,899 | about 13 CPU-minutes | 0.5 GB each |
| on the same test copy, `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 25 minutes | 9.3 GB |
| on the same test copy, `leanexport` of `lower_seven` (108 MB) and NanoDa of the toolchain, 1 CPU | 6 s and 22 s, "Checked 15521 declarations with no errors" | 0.4 GB for NanoDa |
| four of the 72 evaluations of 5,900 (`J15S4Native`, `KK1_05Native`, `KK0_04Native`, `J15S2A2_11Native`) | 155 s, 212 s, 162 s, 394 s on 4, 4, 16, 16 threads | 0.9 GB each |
| 19 more of the 72 (among them `KSmallNative`, `KK0_03Native`, `KK0_05Native`, `KK0_09Native`, `KK0_10Native`, `KK4Native`, `KK5Native` and nine of the joint statements) in one `lake build`, 16 CPUs | 9.4 hours, 129 CPU-hours | at most 1.8 GB for all processes together |

When I first evaluated the 72 modules (October 2026, Lean 4.31, one process per module with 1 to 20 threads,
beside other jobs) the sum of wall time times threads was 4,190 thread-hours. On Lean 4.35.0 the four modules
above took 0.39 to 0.70 times their thread-hours of then, so I expect the 72 modules to take about 2,000 to 3,000
CPU-hours: 2.5 to 4 days on 32 threads. Each module is one Lean process of under 1 GB. Each search is cut
into parts (16,381 for the largest statement) that the Lean runtime runs as tasks on all its threads, so a
module uses every thread it gets; the longest one, `KK0_01Native`, needs about 180 CPU-hours.

`lake build` starts one Lean process per thread and gives each process as many threads. The environment
variable `LEAN_NUM_THREADS` sets both numbers, for example `LEAN_NUM_THREADS=32 lake build AlmanacSolution`.
A build that is stopped can be started again: Lake keeps the modules that are done.

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
