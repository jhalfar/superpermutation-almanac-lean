# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83` and the second (a lower bound for 8 symbols) is commit `7e6664d`.
This commit holds the third.

## This batch: 872 for 6 symbols, checked by the kernel

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 6 872` | every superpermutation on 6 symbols has length at least 872 |

The bound itself is not new: the Almanac lists 872 from Benjamin Grayzel's Lean proof of $`s(6) = 872`$
([BGray-wrl/superperm6](https://github.com/BGray-wrl/superperm6)), which evaluates its finite searches with
`native_decide`. This proof uses no `native_decide`, no `Lean.ofReduceBool` and no compiled code. Every finite
search is evaluated by the kernel (`decide +kernel`), and the theorem depends on the axioms `propext`,
`Classical.choice` and `Quot.sound` only. It does not use Grayzel's code.

The proof is the one in `proofs/lean/small` of the main repository:

1. The model of standard configurations of my proof of 5,899 for 7 symbols (`proofs/lean/n7`, here in
   `LowerBounds/`). By its Theorems W and N, if no valid configuration on 6 symbols has cost at most
   $`(6-2)! + 4 = 28`$, every superpermutation on 6 symbols has at least $`\mathrm{hpv}(6) + 5 = 872`$ letters,
   with $`\mathrm{hpv}(6) = 6! + 5! + 4! + 3 = 867`$.
2. A configuration of cost at most 28 splits into open trails, closed trails and loops of 4 blocks, and counting
   its 120 rotation classes against its cost leaves only families of 1, 2 or 3 open trails and no closed trail
   (`K6/Family.lean`, `K6/Knap.lean`, `K6/TightConf.lean`).
3. Two searches by the kernel finish the proof. The first bounds the rows of a chain with a given number of
   holes (the chain caps, `K6/CapEval.lean`, 52,386 calls of the search). The second runs through the families
   of the tight case and checks that each of them leaves a rotation class that no loop can cover
   (`K6/TightAll.lean`, 176,883 + 942,655 + 1,184,615 calls for 1, 2 and 3 trails). That a `false` answer of
   the search means that no such family exists is proved in `K6/Sound.lean`, `K6/TightAlong.lean` and
   `K6/TightFinal.lean`.

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma. It proves that the covering predicate of the proof
(`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
`List (Fin 6)`, and then the template statement from `K6.covers_872`.

## The searches in small pieces

In the main repository the tight case is cut into 72 parts, one theorem each, and the largest of them needs
33 GB of memory when the kernel checks it: the kernel keeps what it has computed for the whole of one
declaration, and the memory grows with the length of the evaluation (about 50 to 100 KB per call of the search).
That is far above the judge's 14 GiB. So the two searches are cut differently here.

[`K6/Frontier.lean`](K6/Frontier.lean) is the tool. `goL R cut f U q c` runs the search below a node as the
search itself does, but it stops at every node where `cut` holds and returns the list of these nodes, the
frontier. `go_of_goL` proves that the search answers `false` below a node if the frontier contains no node where
the search finds something, and if the search answers `false` below every node of the frontier. A search is
then proved in three kinds of theorems:

* a cut: `goL R cut s = L.map some` (or `partL` for the whole search), where the list `L` of the frontier is
  written out in the file, and the kernel computes the frontier and compares it with `L`.
* a piece: `allNo R C = true`. The kernel runs the search below the nodes of a short list `C`.
* the frontier `L` is the concatenation of pieces, and a node with a large search below it is cut again.

The cuts are at a number of rows (`cutZ`, `cutR`). [`tools/gen_te.py`](tools/gen_te.py) runs a copy of the
search in Python, chooses the depths, packs the nodes into pieces of at most 12,000 calls of the search and
writes the files `K6/CE/*.lean` (chain caps), `K6/TE/*.lean` (tight case), `K6/CapEval.lean` and
`K6/TightAll.lean`. Nothing in it is trusted: a list that differs from what the search in Lean computes makes
the kernel reject the cut. `python3 tools/gen_te.py --check` writes them again and compares.

| search | calls of `go` | cuts | pieces |
|---|---|---|---|
| chain caps | 52,386 | 1 | 5 |
| tight case, 1 trail | 176,883 | 4 | 22 |
| tight case, 2 trails | 942,655 | 12 | 110 |
| tight case, 3 trails | 1,184,615 | 24 | 182 |

The pieces split the searches without overlap, so the kernel does less work than for the 72 parts of the main
repository (each of them runs the top of the search again), and no declaration needs more than about 1 GB.
For the same reason the seven checks of the tables over the 720 words in `K6/TabOK.lean` are evaluated in 8
pieces of 90 words each (`all_of_chunks`).

The tables of the searches (`K6/Tab.lean`, `K6/CapTab.lean`, `K6/TightTab.lean`) are written by
`tools/gen_k6.py`, `tools/gen_cap.py` and `tools/gen_tight.py`, unchanged from the main repository. They are
not trusted either: `K6/TabOK.lean` and `K6/CapFinal.lean` check them against the words.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_six_kernel\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`.

On my machine (Linux under WSL 2, Mathlib from its cache, idle priority beside other jobs) I measured:

| step | time | memory |
|---|---|---|
| clean `lake build AlmanacSolution` on 4 CPUs, at most 4 Lean processes at a time | 17 minutes | at most 10.5 GB for all processes together (proportional set size) |
| the same, summed over the 591 modules | 70 minutes | the largest single file, `K6/TabOK.lean`, 3.1 GB |
| one piece of a search (`K6/TE`, `K6/CE`), compiled alone | 2 to 10 s | at most 1.7 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 77 minutes | 9.5 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.lower_six_kernel` | 8 s, 89 MB | 5.7 GB |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 35 minutes, "Checked 14293 declarations with no errors" | 1.1 GB |

`leanchecker --fresh` replays all of Mathlib as well, which takes most of its memory. With 8 CPUs the build should
take about 10 minutes. The two kernel checks together stay under 11 GB, below the judge's 14 GiB.

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
