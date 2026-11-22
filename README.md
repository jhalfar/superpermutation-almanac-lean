# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). Each batch is one commit
that replaces the tree of the one before; the earlier batches are listed in the history of this branch (the
exponent-1/37 batch is commit `ad9477f`, the exponent-1/32 batch is commit `dd5dec1`, the exponent-1/29 batch is
commit `8ab3685`). This commit holds the batch below.

## This batch: the error after $`2(n-4)!`$ with exponent 1/28, up to a logarithm

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one custom result, `AlmanacAdapter.ExplicitErrorLog28`:

```math
\left|S(n) - \bigl(n! + (n-1)! + (n-2)! + 2(n-4)!\bigr)\right| \le 205\,(n-4)!\,(\ln n)^{3/28}\,n^{-1/28}
\qquad\text{for every } n \ge 5920\cdot 8320^{3}\cdot 6^{28}\cdot 4^3\ (\approx 1.34\cdot 10^{39}).
```

It has the form of Jay Pantone's statement for [b/42](https://superpermutations.com/b/42),
$`400\,(n-4)!\,n^{-1/61}`$ for $`n \ge 8\cdot 10^{12}\cdot 352^4\cdot 6^{61}`$, and of my earlier batches
$`306\,(n-4)!\,n^{-1/37}`$, $`148\,(n-4)!\,(\ln n)^{3/32}\,n^{-1/32}`$ and $`183\,(n-4)!\,(\ln n)^{3/29}\,n^{-1/29}`$.
The same files also prove the clean power $`201\,(n-4)!\,n^{-1/29}`$ for $`n \ge 94720\cdot 8320^3\cdot 6^{29}`$
(about $`2.01\cdot 10^{39}`$, `CoefficientTwoPrecision.Asym28.explicit_error_29`). As in the earlier statements,
the lower side uses the same constant. It comes from Theorem B of my lower-bound files: Cole Fritsch's formula of
2020, proved in Lean on Xiaolong Liu's library. It gives an error of $`4/n`$.

Jay Pantone has a written argument for the exponent 1/30 that is not in Lean. I have not read it, so I cannot say
how it relates to the steps below.

### Whose proof this is

The construction and almost all of the proof are Jay Pantone's: his release "A polynomial error estimate for
superpermutation length",
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics),
commit `9ccbe66`, packaged for the Almanac in commit `882721e` (branch `almanac-submission`). This batch changes
five estimates and the parameters that follow from them. Four are those of my earlier batches; the fifth, the
incidence structure of the controls, is new.

1. **The pending mass halves on every group of sparse blocks** (`Asym35.Pending`). After the sparse blocks a
   fraction $`p = \prod_i (1 - f_i)`$ of the classes is still open, and the dense tail closes it at cost $`16p`$.
   Jay's proof bounds $`p`$ by the invariant $`p\,(1 + \sum_i f_i) \le 1`$ over all blocks at once, so
   $`p \le 4/r`$ needs a family density $`\rho \ge r^2`$. Applied to consecutive groups of blocks whose densities
   add up to at least 1, the same invariant halves $`p`$ on every group, and $`\lfloor\log_2 r\rfloor + 1`$ groups
   give $`p \le 1/r`$ with only $`\rho \ge 4r(\lfloor\log_2 r\rfloor + 2)`$. The family then needs
   $`A = \lceil 4r^2(\lfloor\log_2 r\rfloor + 2)/\beta\rceil`$ blocks per letter (`Asym35.Width`), and the
   coefficient is $`2 + 26/r`$ instead of $`2 + 74/r`$.
2. **One count per pair of event types** (`Asym28.ProximityKeys`, `Asym33.IntervalCount`,
   `Asym28.IntervalKeys`). A candidate is deleted when two of its events for different forbidden pairs come
   close. For a fixed pair of event types the resulting congruences have the same linear form; only the constant
   changes, within $`|c| \le B = 14 r^2 W`$. So their union is the set where one linear form lands in an
   interval, and that set has at most $`4B + 2(d-1)^2 + 1`$ guard values.
3. **The envelope degree is $`192\,r^7`$** (`Asym29.Sorted`, `Asym29.Degree`). Jay selects his labelled frames
   greedily, and a fraction $`1/(\Delta+1)`$ of all frames can be kept, where $`\Delta`$ bounds the frames whose
   envelopes can meet a given one. Because target frames are sorted, his reconstruction witnesses give at most
   $`12\,r^3`$ targets for a pair of joint states, so $`\Delta = 192\,r^7`$ instead of $`64\,r^8`$, and the frame
   density is $`\beta \ge 1/(1040\,r^3)`$.
4. **The controls form a transversal design** (`Asym28.Prime`, `Asym28.TD`, `Asym28.Width`; new in this batch).
   Jay's controls are the points $`(i, j)`$ with $`i < r`$ and $`j < rA`$, and the block with slope $`a < A`$ and
   intercept $`b`$ takes the control $`(i, (ai + b) \bmod rA)`$ in row $`i`$. Two blocks with different slopes
   that agreed in two rows $`i \ne j`$ would give $`rA \mid (a - a')(i - j)`$, impossible since $`0 < |(a - a')(i - j)| < rA`$, so
   distinct blocks share at most one control. The same formula modulo a prime $`q`$ with $`q \ge A`$ and
   $`q \ge r`$ has the same property, because then $`q`$ divides neither $`a - a'`$ nor $`i - j`$: this is the
   transversal design $`\mathrm{TD}(r, q)`$ restricted to $`A`$ parallel classes. Every control still lies in
   exactly one block of each slope, and a block still meets $`r(A-1)`$ others, but a stage now has
   $`W = rq`$ controls instead of $`r^2 A`$. With $`q`$ the least prime $`\ge A`$, Bertrand's postulate gives
   $`q \le 2A`$, so $`W \le 8320\,r^6(\lfloor\log_2 r\rfloor + 2)`$ instead of
   $`4161\,r^7(\lfloor\log_2 r\rfloor + 2)`$. The price is that a block's neighbour count $`r(A-1)`$ is now only
   bounded by $`W`$, not by $`W/r`$, so the number of event types is at most $`r^4 W`$ (it was $`r^3 W`$) and the
   proximity deletion is $`128\,r^{10} W^3/m`$ (it was $`128\,r^8 W^3/m`$). In total one power of $`r`$ is gained.
5. **The threshold.** The block threshold is $`m \ge 2960\,r^{10} W^3`$, which follows from
   $`n \ge 5920\cdot 8320^3\,r^{28}(\lfloor\log_2 r\rfloor + 2)^3`$ (`Asym28.finite_covering_word_log`,
   coefficient $`2 + 26/r`$ for every $`r \ge 6`$ with $`6 \mid r`$). Choosing $`r`$ as the largest such multiple
   of 6, as in Jay's rate argument, and using $`\lfloor\log_2 n\rfloor + 3 \le 2\ln n`$ gives the bound above
   (`Asym28.LogRate`; the constant is $`52\,(8\cdot 5920\cdot 8320^3)^{1/28} + 4 \approx 204.9`$). With
   $`(\lfloor\log_2 r\rfloor + 2)^3 \le 16r`$ the same theorem gives the clean power 1/29 (`Asym28.Main`,
   `Asym28.Rate`).

### Which files are whose

Jay's files in [`lean/`](lean/) are unchanged, except three, each with a note in its header (the same three as in
the exponent-1/29 batch):

- `Quantitative/ConstructionParameters.lean`: `sourceDegree` is $`192\,r^7`$ instead of $`64\,r^8`$, with the two
  proofs that unfold it. The bounds he states there still hold and are unchanged.
- `Quantitative/PackingSupply.lean`: the greedy selection uses `Asym29.degree_192` instead of his `degree_64`.
- `Quantitative/ProximityNormalization.lean`: one proof step, for the new `sourceDegree`.

His grid is not changed in place. [`lean/Asym28/TD/`](lean/Asym28/TD/) holds copies of the 33 files of his that
depend on `Quantitative.ActiveGrid` and are needed here (namespace `CoefficientTwoPrecision.TD`, imports pointed
at the copies), each with a note in its header. In 25 of them nothing else changed. In the other eight the column
count `r * A` becomes `tdQ r A`: `ActiveGrid` (the columns and the proof that blocks meet at most once),
`GuardCatalogue`, `GridAlphabet`, `GuardCandidateLoss` and `ProximityDeletion` (the guard and block counts),
`CandidateSpace` (the block count; two lemmas about his own `sourceA` are left out), `CatalogueBounds` (the width
$`W = rq`$, and the bounds that used $`rA = W/r`$ carry the extra powers of $`r`$) and `GuardRelativeLoss` (the
guard-only deletion is $`18\,r^3W^3/m`$ instead of $`18\,r^2W^3/m`$). His `GlobalRetention`, `SourceSelection` and
`SparseFamilyConstruction` are not copied; their roles are taken by `Asym28.IntervalKeys`, `Asym28.Retention` and
`Asym28.Certificate`. His originals stay in the tree, unchanged, and are not imported by `AlmanacSolution`.

[`lean/Asym28/Bertrand.lean`](lean/Asym28/Bertrand.lean) is a copy of the part of Mathlib's
`NumberTheory/Primorial.lean` and `NumberTheory/Bertrand.lean` that proves Bertrand's postulate for
$`n \ge 512`$ (Patrick Stevens, Bolton Bailey, Yury Kudryashov, Bhavik Mehta; Apache License 2.0), with only the
namespace changed. Mathlib's own module cannot be imported here: it brings in `Mathlib.Data.List.GetD`, which
declares the same lemma name as the inherited `Lean435Compatibility.lean`.

[`lean/Asym28/`](lean/Asym28/) is otherwise new. `Prime` is the column modulus and the intersection proof;
`Width` is the width of the design and the definitions that depend on it. `ProximityKeys` and `IntervalKeys` are
the modules of the earlier batches (`Asym37/ProximityKeys`, `Asym33/IntervalKeys`) on the copies, with the type
count $`r^4 W`$. The chain `Params`, `Retention`, `CountRatio`, `Transfer`, `Certificate`, `Stages`, `Rate`,
`Main`, `LogRate` is the chain of my exponent-1/29 batch with the new width and threshold. From the earlier
batches the tree keeps `Asym29/Sorted`, `Asym29/Degree`, `Asym35/Width` (now only the block count $`A`$),
`Asym35/Pending`, `Asym35/Words` and `Asym33/IntervalCount`; the modules that gave the exponent 1/29 are replaced
by `Asym28` and are no longer in the tree. Parts copied from his files with only names, the threshold or the
constants changed say so in their docstrings.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.explicit_error_log28\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

On my machine (Linux under WSL 2, Mathlib from its cache, 4 CPUs) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | 1,517 s (3,781 jobs) | 0.88 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 1,202 s | 0.77 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.explicit_error_log28` | 37 s, 380 MB | |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 317 s, "Checked 46103 declarations with no errors" | 0.38 GB |

The statements NanoDa printed are in [`verification/almanac/`](verification/almanac/).

## Sources and licences

`lean/` (except `lean/Asym35/`, `lean/Asym33/`, `lean/Asym29/` and `lean/Asym28/`), `LICENSE`, `NOTICE`,
`licenses/`, `lake-manifest.json` and `lean-toolchain` come from commit `882721e` of Jay Pantone's repository, under
the Apache License 2.0, with the inherited sources and licences that his [`NOTICE`](NOTICE) lists (among them
Xiaolong Liu's files under CC BY 4.0, which keep that licence). His `NOTICE` and `LICENSE` are unchanged; the three
files of his that I changed are named above and carry a note. `lean/Asym28/TD/` holds copies of his files, under his
licence, with the changes named in each header. `lean/Asym28/Bertrand.lean` is copied from Mathlib under the Apache
License 2.0, with its authors named in its header. `lakefile.toml` is his, with the four `Asym` libraries added to
the globs and its comment changed. The rest of `lean/Asym35/`, `lean/Asym33/`, `lean/Asym29/`, `lean/Asym28/` and
`AlmanacAdapter.lean` are mine (the adapter's `fact_eq` and `covers_iff` are his lemmas), under the Apache License
2.0. `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
