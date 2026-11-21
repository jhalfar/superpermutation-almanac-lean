# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). Each batch is one commit
that replaces the tree of the one before; the earlier batches are listed in the history of this branch (the
exponent-1/37 batch is commit `ad9477f`, the exponent-1/32 batch is commit `dd5dec1`). This commit holds the batch
below.

## This batch: the error after $`2(n-4)!`$ with exponent 1/29, up to a logarithm

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one custom result, `AlmanacAdapter.ExplicitErrorLog29`:

```math
\left|S(n) - \bigl(n! + (n-1)! + (n-2)! + 2(n-4)!\bigr)\right| \le 183\,(n-4)!\,(\ln n)^{3/29}\,n^{-1/29}
\qquad\text{for every } n \ge 5920\cdot 4161^{3}\cdot 6^{29}\cdot 4^3\ (\approx 1.01\cdot 10^{39}).
```

It has the form of Jay Pantone's statement for [b/42](https://superpermutations.com/b/42),
$`400\,(n-4)!\,n^{-1/61}`$ for $`n \ge 8\cdot 10^{12}\cdot 352^4\cdot 6^{61}`$, and of my earlier batches
$`306\,(n-4)!\,n^{-1/37}`$ and $`148\,(n-4)!\,(\ln n)^{3/32}\,n^{-1/32}`$. The same files also prove the clean power
$`180\,(n-4)!\,n^{-1/30}`$ for $`n \ge 94720\cdot 4161^3\cdot 6^{30}`$ (about $`1.51\cdot 10^{39}`$,
`CoefficientTwoPrecision.Asym29.explicit_error_30`). As in the earlier statements, the lower side uses the same
constant. It comes from Theorem B of my lower-bound files: Cole Fritsch's formula of 2020, proved in Lean on
Xiaolong Liu's library. It gives an error of $`4/n`$.

Jay Pantone has a written argument for the exponent 1/30 that is not in Lean. I have not read it, so I cannot say
how it relates to the step below.

### Whose proof this is

The construction and almost all of the proof are Jay Pantone's: his release "A polynomial error estimate for
superpermutation length",
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics),
commit `9ccbe66`, packaged for the Almanac in commit `882721e` (branch `almanac-submission`). This batch changes
four estimates and the parameters that follow from them, not the construction. Three are those of my earlier
batches; the fourth is new.

1. **The pending mass halves on every group of sparse blocks** (`Asym35.Pending`). After the sparse blocks a
   fraction $`p = \prod_i (1 - f_i)`$ of the classes is still open, and the dense tail closes it at cost $`16p`$.
   Jay's proof bounds $`p`$ by the invariant $`p\,(1 + \sum_i f_i) \le 1`$ over all blocks at once, so
   $`p \le 4/r`$ needs a family density $`\rho \ge r^2`$. Applied to consecutive groups of blocks whose densities
   add up to at least 1, the same invariant halves $`p`$ on every group, and $`\lfloor\log_2 r\rfloor + 1`$ groups
   give $`p \le 1/r`$ with only $`\rho \ge 4r(\lfloor\log_2 r\rfloor + 2)`$. The family then needs
   $`A = \lceil 4r^2(\lfloor\log_2 r\rfloor + 2)/\beta\rceil`$ blocks per letter (`Asym35.Width`), and the
   coefficient is $`2 + 26/r`$ instead of $`2 + 74/r`$.
2. **One count per pair of event types** (`Asym37.ProximityKeys`, `Asym33.IntervalCount`,
   `Asym33.IntervalKeys`). A candidate is deleted when two of its events for different forbidden pairs come
   close. For a fixed pair of event types the resulting congruences have the same linear form; only the constant
   changes, within $`|c| \le B = 14 r^2 W`$. So their union is the set where one linear form lands in an
   interval, and that set has at most $`4B + 2(d-1)^2 + 1`$ guard values. The proximity deletion is
   $`128\,r^8 W^3/m`$ (`Asym29.Retention`).
3. **The envelope degree is $`192\,r^7`$** (`Asym29.Sorted`, `Asym29.Degree`; new in this batch). Jay selects his
   labelled frames greedily: two frames conflict when their envelopes share a row, a frame has at most
   $`\Delta`$ conflicts, and so a fraction $`1/(\Delta+1)`$ of all frames can be kept. His $`\Delta = 64\,r^8`$ is
   $`(4r^2)^2`$ pairs of joint states times $`4r^4`$ reconstruction witnesses. A witness names the source slot
   that is left out, a cyclic offset, the slot of the target's sum point and the target slot that is left out,
   and the affine relation then gives the missing cut. A target frame is sorted, and because of that most
   witnesses give the same targets. Fix the source slot and the offset. If the target keeps its anchor, the
   translation is known, the missing cut takes at most $`4d + 6`$ values, and of two sorted targets the one with
   the smaller omitted slot has the smaller missing cut, so the value fixes the slot. If the anchor is the
   missing cut, $`(d-1)`$ times the translation takes at most $`2(d+1)`$ values, and two sorted targets with the
   same translation have the same offset. This leaves at most $`12\,r^3`$ targets for a pair of joint states, so
   $`\Delta = 192\,r^7`$. The frame density becomes $`\beta \ge 1/(1040\,r^3)`$ instead of $`1/(351\,r^4)`$, and the
   width $`W \le 4161\,r^7(\lfloor\log_2 r\rfloor + 2)`$ instead of $`1405\,r^8(\lfloor\log_2 r\rfloor + 2)`$
   (`Asym35.Width`).
4. **The threshold.** The block threshold is $`m \ge 2960\,r^8 W^3`$, which follows from
   $`n \ge 5920\cdot 4161^3\,r^{29}(\lfloor\log_2 r\rfloor + 2)^3`$ (`Asym29.finite_covering_word_log`, coefficient
   $`2 + 26/r`$ for every $`r \ge 6`$ with $`6 \mid r`$). Choosing $`r`$ as the largest such multiple of 6, as in
   Jay's rate argument, and using $`\lfloor\log_2 n\rfloor + 3 \le 2\ln n`$ gives the bound above
   (`Asym29.LogRate`; the constant is $`52\,(8\cdot 5920\cdot 4161^3)^{1/29} + 4 \approx 182.5`$). With
   $`(\lfloor\log_2 r\rfloor + 2)^3 \le 16r`$ the same theorem gives the clean power 1/30 (`Asym29.Main`,
   `Asym29.Rate`).

### Which files are whose

Jay's files in [`lean/`](lean/) are unchanged, except three, each with a note in its header:

- `Quantitative/ConstructionParameters.lean`: `sourceDegree` is $`192\,r^7`$ instead of $`64\,r^8`$, with the two
  proofs that unfold it. The bounds he states there still hold and are unchanged.
- `Quantitative/PackingSupply.lean`: the greedy selection uses `Asym29.degree_192` instead of his `degree_64`.
- `Quantitative/ProximityNormalization.lean`: one proof step, for the new `sourceDegree`.

[`lean/Asym29/`](lean/Asym29/) is new. `Sorted` and `Degree` are the new count; the witnesses it counts are his
(`PositionalExtraction.actual_reconstruction`). The other modules (`Params`, `Retention`, `CountRatio`,
`Transfer`, `Certificate`, `Stages`, `Rate`, `Main`, `LogRate`) are the chain of my exponent-1/32 batch with the new
width and threshold. From the earlier batches the tree keeps `Asym37/ProximityKeys`, `Asym35/Width`,
`Asym35/Pending`, `Asym35/Words`, `Asym33/IntervalCount` and `Asym33/IntervalKeys`; the modules that gave the
exponents 1/37, 1/35 and 1/33 are replaced by `Asym29` and are no longer in the tree. Parts copied from his files
with only names, the threshold or the constants changed say so in their docstrings.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.explicit_error_log29\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

On my machine (Linux under WSL 2, Mathlib from its cache, 4 CPUs) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | 1,833 s (3,773 jobs) | 0.87 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 2,407 s | 0.77 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.explicit_error_log29` | 69 s, 350 MB | |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 189 s, "Checked 43455 declarations with no errors" | 0.36 GB |

The statements NanoDa printed are in [`verification/almanac/`](verification/almanac/).

## Sources and licences

`lean/` (except `lean/Asym37/`, `lean/Asym35/`, `lean/Asym33/` and `lean/Asym29/`), `LICENSE`, `NOTICE`,
`licenses/`, `lake-manifest.json` and `lean-toolchain` come from commit `882721e` of Jay Pantone's repository, under
the Apache License 2.0, with the inherited sources and licences that his [`NOTICE`](NOTICE) lists (among them
Xiaolong Liu's files under CC BY 4.0, which keep that licence). His `NOTICE` and `LICENSE` are unchanged; the three
files of his that I changed are named above and carry a note. `lakefile.toml` is his, with the four `Asym`
libraries added to the globs and its comment changed. `lean/Asym37/`, `lean/Asym35/`, `lean/Asym33/`,
`lean/Asym29/` and `AlmanacAdapter.lean` are mine (the adapter's `fact_eq` and `covers_iff` are his lemmas), under
the Apache License 2.0. `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's
files, unchanged.
