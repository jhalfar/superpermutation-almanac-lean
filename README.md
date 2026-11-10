# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d`, the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d` and the fourth (5,899 for 7 symbols with
`native_decide`) is commit `a09f9ef`. This commit holds the fifth.

## This batch: 5,898 for 7 symbols, checked by the kernel

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one result:

| statement | meaning |
|---|---|
| `Almanac.LowerBoundAt 7 5898` | every superpermutation on 7 symbols has length at least 5,898 |

The bound is Justin Lebar's, whose Lean proof ([jlebar/superperm7-ge-5898](https://github.com/jlebar/superperm7-ge-5898))
evaluates its finite searches with `native_decide`; nothing of it is used here. This proof uses no
`native_decide`, no `Lean.ofReduceBool` and no compiled code: every finite search is evaluated by the kernel
(`decide +kernel`), and the theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.
The kernel-only bound the Almanac lists so far is William Echols's 5,897
([williamechols/superpermutations](https://github.com/williamechols/superpermutations)), which takes the same
route one unit lower, at cost 132, where the chain caps alone are enough. Nothing of his code is used here.

The proof is the coarse part of my proof of 5,899 (`proofs/lean/n7` of the main repository, here in
`LowerBounds/`), run at cost 133 instead of 134:

1. The model of standard configurations (Theorems W and N): if no valid configuration on 7 symbols has cost
   at most $`5! + 13 = 133`$, every superpermutation on 7 symbols has at least $`\mathrm{hpv}(7) + 14 = 5{,}898`$
   letters.
2. A configuration of cost at most 133 has value at least 55 and weight at most 78 (Lemma ACC), so its family
   of trails has weight $`\sum (\text{holes} + 6) \le 84`$ and value $`\sum (\text{rows} - \text{holes} - 5) \ge 50`$,
   whatever the costs of its links (Lemma FAM). In the proof of 5,899 this is the case that Lemma FF refutes with
   the chain caps and the five profile statements alone; here it is the whole proof (`K7/Final.lean`). The
   sequences with links, the rings and the hanging items of 5,899 are not needed.
3. The chain caps $`W(x)`$ for chains with $`x \le 78`$ holes (`tools/caps5898.txt`): the caps of 5,899 up to
   36 holes, and above that larger caps, as large as the knapsack allows (`K7/Arith.lean`, checked by
   `decide +kernel`: the only families of weight at most 84 and value 50 are the five profiles). Larger caps are
   weaker statements, and their search is about a hundred times smaller than that of 5,899 cut at 78 holes.
4. Two kinds of searches by the kernel finish the proof: the chain caps (`K7/CE/`, 12,296,167 calls of the
   search) and the five profile statements of 5,899 (`K7/FE/`, 779,347, 202,109, 403,989, 754,979 and
   3,263,423 calls).

The search engine is the one of my proof of 872 (`K6/Engine.lean`) written for 7 symbols (`K7/Engine.lean`): a
depth-first search over rows of blocks whose rotation classes are new, with the tables of the 5,040 words as
natural numbers read with shifts and the used classes as a natural number read as a set of bits, so that the
kernel computes with GMP. `K7/TabOK/` checks the tables against the words, `K7/Sound.lean` proves that the
search is complete and `K7/Prove.lean` that a search with the rules of `PSearch.lean` (read from bit tables,
which `K7/TabCheck/` checks against the rules) that answers `false` proves the statement of `PSeq.lean` for
those rules. From there the theorems of the proof of 5,899 give the chain caps and the profile statements.

The searches are too large for one evaluation, so they are cut into pieces as in the proof of 872
(`K7/Frontier.lean`): an evaluation computes the frontier of the search below a node and compares it with a list
written out in a file, and the search below the nodes of such lists is evaluated a few nodes at a time. For
the profile searches a node where a chain is complete tries all 5,040 words for the next chain; such a node is
cut by ranges of words (`jumpsR`). `tools/gen_k7te.py` finds the frontiers with a copy of the search in Python
and writes the files; nothing it computes is trusted. No evaluation goes above 12,000 weighted calls of the
search.

[`LowerLinks.lean`](LowerLinks.lean) holds the linking lemma. It proves that the covering predicate of the proof
(`SuperpermutationBounds.Covers` from Jay Pantone's `Challenge.lean`) is `Almanac.IsSuperpermutation` over
`List (Fin 7)`, and then the template statement from `K7.covers_lower_bound_7_kernel`.

The files of the batches of 872 (`K6/`) and of 5,899 (`LowerBounds/PFinalK16.lean` and the search engines
`KSearch`, `K16Search`) are still in the repository, but nothing of this batch imports them.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.lower_seven\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`.

On my machine (Linux under WSL 2, Mathlib from its cache, at most 3 Lean processes) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | about 14,300 s of CPU in all, so about half an hour on 8 CPUs | at most 3.1 GB for one evaluation file, about 3.7 GB for a module that loads Mathlib |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 16,816 s (4.7 hours) | 9.8 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.lower_seven` | 19 s, 129 MB | 7.0 GB |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 13,277 s (3.7 hours), "Checked 55723 declarations with no errors" | 1.3 GB |

The cuts are split into files of at most 150 theorems, so no single file needs much memory. The two kernel checks of the judge, side by side on one CPU each, should take under 5 hours and
about 11 GB together. There is nothing to re-evaluate: the batch has no `native_decide`.

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
