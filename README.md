# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). Each batch is one commit
that replaces the tree of the one before; the earlier batches are listed in the history of this branch (the
exponent-1/37 batch is commit `ad9477f`). This commit holds the batch below.

## This batch: the error after $`2(n-4)!`$ with exponent 1/32, up to a logarithm

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one custom result, `AlmanacAdapter.ExplicitErrorLog32`:

```math
\left|S(n) - \bigl(n! + (n-1)! + (n-2)! + 2(n-4)!\bigr)\right| \le 148\,(n-4)!\,(\ln n)^{3/32}\,n^{-1/32}
\qquad\text{for every } n \ge 5920\cdot 1405^{3}\cdot 6^{32}\cdot 4^3\ (\approx 8.4\cdot 10^{39}).
```

It has the form of Jay Pantone's statement for [b/42](https://superpermutations.com/b/42),
$`400\,(n-4)!\,n^{-1/61}`$ for $`n \ge 8\cdot 10^{12}\cdot 352^4\cdot 6^{61}`$, and of my earlier batch
$`306\,(n-4)!\,n^{-1/37}`$ for $`n \ge 5920\cdot 352^3\cdot 6^{37}`$ (commit `ad9477f`), with an extra factor
$`(\ln n)^{3/32}`$; it is smaller than $`K\,n^{-1/(32+\varepsilon)}`$ for every $`\varepsilon > 0`$ and large $`n`$.
The same files also prove the clean power $`147\,(n-4)!\,n^{-1/33}`$ for $`n \ge 94720\cdot 1405^3\cdot 6^{33}`$
(about $`1.25\cdot 10^{40}`$, `CoefficientTwoPrecision.Asym33.explicit_error_33`). As in the earlier statements,
the lower side uses the same constant. It comes from Theorem B of my lower-bound files: Cole Fritsch's formula of
2020, proved in Lean on Xiaolong Liu's library. It gives an error of $`4/n`$.

Jay Pantone has a written argument for the exponent 1/30 that is not in Lean. This batch does not reach it.

### Whose proof this is

The construction and almost all of the proof are Jay Pantone's: his release "A polynomial error estimate for
superpermutation length",
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics),
commit `9ccbe66`, packaged for the Almanac in commit `882721e` (branch `almanac-submission`). His files in
[`lean/`](lean/) are unchanged. [`lean/Asym37/`](lean/Asym37/) is the exponent-1/37 count of my earlier batch.
[`lean/Asym35/`](lean/Asym35/) and [`lean/Asym33/`](lean/Asym33/) are new. They change three estimates and the
parameters that follow from them, not the construction:

1. **The pending mass halves on every group of sparse blocks** (`Asym35.Pending`). After the sparse blocks a
   fraction $`p = \prod_i (1 - f_i)`$ of the classes is still open, and the dense tail closes it at cost $`16p`$.
   Jay's proof bounds $`p`$ by the invariant $`p\,(1 + \sum_i f_i) \le 1`$ over all blocks at once, so
   $`p \le 4/r`$ needs a family density $`\rho \ge r^2`$. Applied to consecutive groups of blocks whose densities
   add up to at least 1, the same invariant halves $`p`$ on every group, and $`\lfloor\log_2 r\rfloor + 1`$ groups
   give $`p \le 1/r`$ with only $`\rho \ge 4r(\lfloor\log_2 r\rfloor + 2)`$. The family then needs
   $`A = \lceil 4r^2(\lfloor\log_2 r\rfloor + 2)/\beta\rceil`$ blocks per letter, so the width is
   $`W \le 1405\,r^8(\lfloor\log_2 r\rfloor + 2)`$ instead of $`352\,r^9`$ (`Asym35.Width`), and the coefficient
   is $`2 + 26/r`$ instead of $`2 + 74/r`$.
2. **One count per pair of event types** (`Asym33.IntervalCount`, `Asym33.IntervalKeys`). A candidate is
   deleted when two of its events for different forbidden pairs come close. My 1/37 batch counts the resulting
   congruences once per key: two event types and one constant $`c`$ with $`|c| \le B = 14 r^2 W`$, each key
   costing Jay's root count of at most $`2(d-1)^2`$ guard values. For a fixed pair of types every key has the
   same linear form; only the constant changes. So the union over the $`2B + 1`$ constants is the set where one
   linear form lands in an interval, and that set has at most $`4B + 2(d-1)^2 + 1`$ guard values
   (`linear_interval_count`: the values $`|a|x`$ are $`|a|`$ apart and meet at most $`|a| + 1`$ translates of the
   interval). This replaces $`(2B+1)\cdot 2(d-1)^2`$, so the proximity deletion is $`128\,r^8 W^3/m`$ instead of
   $`128\,r^{10} W^3/m`$ (`Asym33.Retention`).
3. **The threshold.** The block threshold is $`m \ge 2960\,r^8 W^3`$, which follows from
   $`n \ge 5920\cdot 1405^3\,r^{32}(\lfloor\log_2 r\rfloor + 2)^3`$ (`Asym33.finite_covering_word_log`, coefficient
   $`2 + 26/r`$ for every $`r \ge 6`$ with $`6 \mid r`$). Choosing $`r`$ as the largest such multiple of 6, as in
   Jay's rate argument, and using $`\lfloor\log_2 n\rfloor + 3 \le 2\ln n`$ gives the bound above
   (`Asym33.LogRate`; the constant is $`52\,(8\cdot 5920\cdot 1405^3)^{1/32} + 4 \approx 147.6`$). With
   $`(\lfloor\log_2 r\rfloor + 2)^3 \le 16r`$ the same theorem gives the clean power 1/33 (`Asym33.Main`,
   `Asym33.Rate`).

`Asym35` has the new width (`Width`: the new $`A`$, $`W`$, $`\rho`$, and the width-dependent definitions of Jay's
`CandidateFactorization`, `ConstructionSize`, `CandidateSpace` and `SourceSelection` repeated for the new $`A`$),
the pending bound (`Pending`) and his word bound with 26 in place of 74 (`Words`); its other modules give the
weaker exponent 1/35 and are not used by `Asym33`. `Asym33` has the interval count and the modules of the chain
for the new threshold (`Params`, `Retention`, `CountRatio`, `Transfer`, `Certificate`, `Stages`, `Rate`, `Main`,
`LogRate`). Parts copied from his files or from `Asym37`/`Asym35` with only names, the threshold or the constants
changed say so in their docstrings.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.explicit_error_log32\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

On my machine (Linux under WSL 2, Mathlib from its cache, 2 CPUs, a busy machine) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | 6,223 s (3,772 jobs) | 0.85 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 2,710 s | 0.77 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.explicit_error_log32` | 81 s, 349 MB | |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 223 s, "Checked 43368 declarations with no errors" | 0.36 GB |

The statements NanoDa printed are in [`verification/almanac/`](verification/almanac/).

## Sources and licences

`lean/` (except `lean/Asym37/`, `lean/Asym35/` and `lean/Asym33/`), `LICENSE`, `NOTICE`, `licenses/`,
`lake-manifest.json` and `lean-toolchain` come from commit `882721e` of Jay Pantone's repository, under the Apache
License 2.0, with the inherited sources and licences that his [`NOTICE`](NOTICE) lists (among them Xiaolong Liu's
files under CC BY 4.0, which keep that licence). His `NOTICE` and `LICENSE` are unchanged. `lakefile.toml` is his,
with `Asym37.+`, `Asym35.+` and `Asym33.+` added to the library globs and its comment changed. `lean/Asym37/`,
`lean/Asym35/`, `lean/Asym33/` and `AlmanacAdapter.lean` are new (the adapter's `fact_eq` and `covers_iff` are his
lemmas), under the Apache License 2.0. `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean`
are the Almanac's files, unchanged.
