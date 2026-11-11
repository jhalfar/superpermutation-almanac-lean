# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d`, the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d`, the fourth (5,899 for 7 symbols with
`native_decide`) is commit `a09f9ef` and the fifth (5,898 for 7 symbols, checked by the kernel) is commit
`5cc0ac3`. This commit holds the sixth.

## This batch: 12 and 13 symbols from Theorem C, checked by the kernel

[`AlmanacSolution.lean`](AlmanacSolution.lean) states two results:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 12 522622401` | every superpermutation on 12 symbols has length at least 522,622,401 |
| `Almanac.LowerBoundAt 13 6746627048` | every superpermutation on 13 symbols has length at least 6,746,627,048 |

Both come from Theorem C of the main repository (`proofs/lean/lower`), the same proof that gave the bounds
522,622,378 and 6,746,626,957 listed so far, with better constants. Every finite search is evaluated by the
kernel (`decide +kernel`); there is no `native_decide`, no `Lean.ofReduceBool` and no compiled code, and both
theorems depend on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

The idea of the new constants is William Echols's. On 10 November 2026 he showed
([williamechols/superpermutations](https://github.com/williamechols/superpermutations), commit `ac27b17`, the
Almanac's $`S(11) \ge 43{,}917{,}904`$) that Theorem C gives one more unit at 11 symbols when the constant $`c`$ is put just
above the least value that reaches the bound, instead of on a round grid. I did the same at 12 and 13 symbols.
Nothing of his code is used here.

### Theorem C and its constants

Write $`\mathrm{hpv}(k) = k! + (k-1)! + (k-2)! + k - 3`$ and take rationals $`c = c_n/q`$, $`b = b_n/q`$.
A window is a run of consecutive pieces of an exact weight-three chain (Xiaolong Liu's preimage-chain library)
that starts and ends with a partial piece; $`r`$ is its number of pieces and $`\delta`$ the sum of their
deficits. Theorem C says: if every window satisfies

```math
2r + 2(k-4) + c\,\delta \le (k-3)\,\delta + b
```

and three conditions on the constants hold (`ConditionsC`), then every superpermutation on $`k`$ symbols has at
least

```math
\mathrm{hpv}(k) + \left\lceil \frac{2(k-2)! - 2(k-2) - b}{k^2 - 4k + 1 - c\,(k-1)} \right\rceil
```

letters (`boundC`). The hypothesis is proved for a model of chains by a finite search (`LowerBounds/SSearch.lean`,
proved complete in `SSound.lean`, `SModel.lean`; `SBridge.lean` carries it to Liu's chains). The search does not
depend on $`b`$, so one run gives the least $`b`$ for a given $`c`$; that least $`b`$ grows with $`c`$, and so does
the size of the search. For each target bound I computed the least $`c`$ that reaches it (each finished search
gives a lower bound on $`b`$ as a linear function of $`c`$, and these lines locate the threshold exactly) and took
a simple fraction just above it:

| symbols | `ModelStatement k cn bn q` | c | b | states of the search | deepest window (pieces) | bound |
|---|---|---|---|---|---|---|
| 12 | `12 281 17976 6465` | 281/6465 = 0.0434648... | 17976/6465 | 124,947 | 2,912 | 522,622,401 |
| 13 | `13 409 9160 2536` | 409/2536 = 0.1612776... | 9160/2536 | 81,260 | 1,544 | 6,746,627,048 |

The least values of $`c`$ for these bounds are 0.04346480 and 0.16127750. Larger bounds exist (522,622,405 with
13 million states, 6,746,627,226 with 44 million), but their searches are far too large for the kernel. The
search for 13 symbols is the same tree as the one for 6,746,627,046 in the main repository; only $`c`$ and $`b`$
moved.

### Files

* `LowerBounds/`: Theorem C and its window search, copied from `proofs/lean/lower` (see `NOTICE`).
* `LowerBounds/SGen/`: the two certificates, written by `tools/s_plan2.py` (a Python copy of the search decides
  where to cut it into lemmas and writes the state at every cut; nothing it computes is trusted, a wrong cut or
  state makes a lemma fail). `C12_281_17976_6465*` has 1,195 lemmas in 73 part files and 413 files of
  states; `C13_409_9160_2536*` has 691 lemmas in 48 part files and 113 files of states.
* `LowerBounds/SCertTune.lean`, `LowerBounds/SFinalTune.lean`: the window statements, the model statements, the
  conditions, the value of `boundC` and the bounds for `SuperpermutationBounds.Covers`, written by
  `tools/mkstmt.py`.
* [`LowerLinks.lean`](LowerLinks.lean): the linking lemmas. They prove that the covering predicate of the proof
  (`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
  `List (Fin n)`, and then the two template statements.

To regenerate the certificates: `python3 tools/s_plan2.py 12 281 17976 6465 C12_281_17976_6465 --leaf 450
--band 250 --per-file 3000` and `python3 tools/s_plan2.py 13 409 9160 2536 C13_409_9160_2536 --leaf 450 --band
250 --per-file 3000` (Python 3 only; the generator writes into `tools/LowerBounds/SGen/`, from where the files
move to `LowerBounds/SGen/`), then `python3 tools/mkstmt.py . C12_281_17976_6465 C13_409_9160_2536`.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_twelve\n#print axioms AlmanacSubmission.lower_thirteen\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`.

On my machine (Linux under WSL 2, Mathlib from its cache, at most 3 Lean processes) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | 5,748 s wall with 3 processes, 16,000 s of CPU in all (so about 35 minutes on 8 CPUs) | at most 8.5 GB for the three processes together |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 10,952 s (3.0 hours) | 8.7 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.lower_twelve AlmanacSubmission.lower_thirteen` | 160 s, 323 MB | 6.7 GB |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 6,885 s (1.9 hours), "Checked 19792 declarations with no errors" | 1.1 GB |

The two kernel checks ran side by side, one CPU each, as the judge runs them. There is nothing to re-evaluate:
the batch has no `native_decide`.

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
