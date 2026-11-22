# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). Each batch is one commit
that replaces the tree of the one before; the earlier batches are listed in the history of this branch (the
exponent-1/37 batch is commit `ad9477f`, the exponent-1/32 batch is commit `dd5dec1`, the exponent-1/29 batch is
commit `8ab3685`, the exponent-1/28 batch is commit `e5c5a22`). This commit holds the batch below.

## This batch: the error after $`2(n-4)!`$ with exponent 1/20, up to a logarithm

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one custom result, `AlmanacAdapter.ExplicitErrorLog20`:

```math
\left|S(n) - \bigl(n! + (n-1)! + (n-2)! + 2(n-4)!\bigr)\right| \le 214\,(n-4)!\,(\ln n)^{1/10}\,n^{-1/20}
\qquad\text{for every } n \ge 2904\cdot 10400^{2}\cdot 6^{20}\cdot 4^2\ (\approx 1.84\cdot 10^{28}).
```

It has the form of Jay Pantone's statement for [b/42](https://superpermutations.com/b/42),
$`400\,(n-4)!\,n^{-1/61}`$ for $`n \ge 8\cdot 10^{12}\cdot 352^4\cdot 6^{61}`$, and of my earlier batches
$`306\,(n-4)!\,n^{-1/37}`$, $`148\,(n-4)!\,(\ln n)^{3/32}\,n^{-1/32}`$, $`183\,(n-4)!\,(\ln n)^{3/29}\,n^{-1/29}`$ and
$`205\,(n-4)!\,(\ln n)^{3/28}\,n^{-1/28}`$. The same files also prove the clean power $`214\,(n-4)!\,n^{-1/21}`$ for
$`n \ge 46464\cdot 10400^2\cdot 6^{21}`$ (about $`1.10\cdot 10^{29}`$,
`CoefficientTwoPrecision.Asym22.explicit_error_21`). As in the earlier statements, the lower side uses the same
constant. It comes from Theorem B of my lower-bound files: Cole Fritsch's formula of 2020, proved in Lean on
Xiaolong Liu's library. It gives an error of $`4/n`$.

Jay Pantone has a written argument for the exponent 1/30 that is not in Lean. I have not read it, so I cannot say
how it relates to the steps below.

### Whose proof this is

The construction and almost all of the proof are Jay Pantone's: his release "A polynomial error estimate for
superpermutation length",
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics),
commit `9ccbe66`, packaged for the Almanac in commit `882721e` (branch `almanac-submission`). This batch changes
seven estimates and the parameters that follow from them. Five are those of my earlier batches; the last two
(items 5 and 6) are new.

1. **The pending mass halves on every group of sparse blocks** (`Asym35.Pending`). After the sparse blocks a
   fraction $`p = \prod_i (1 - f_i)`$ of the classes is still open, and the dense tail closes it at cost $`16p`$.
   Jay's proof bounds $`p`$ by the invariant $`p\,(1 + \sum_i f_i) \le 1`$ over all blocks at once, so
   $`p \le 4/r`$ needs a family density $`\rho \ge r^2`$. Applied to consecutive groups of blocks whose densities
   add up to at least 1, the same invariant halves $`p`$ on every group, and $`\lfloor\log_2 r\rfloor + 1`$ groups
   give $`p \le 1/r`$ with only $`\rho \ge 4r(\lfloor\log_2 r\rfloor + 2)`$. The family then needs
   $`A = \lceil 4r^2(\lfloor\log_2 r\rfloor + 2)/\beta\rceil`$ blocks per letter (`Asym35.Width`), and the
   coefficient is $`2 + 26/r`$ instead of $`2 + 74/r`$.
2. **One count per pair of event types** (`Asym22.ProximityKeys`, `Asym33.IntervalCount`,
   `Asym22.IntervalKeys`). A candidate is deleted when two of its events for different forbidden pairs come
   close. For a fixed pair of event types the resulting congruences have the same linear form; only the constant
   changes, within an interval $`[-B, B]`$. So their union is the set where one linear form lands in an
   interval, and that set has at most $`4B + |\gamma| + 1`$ values of one variable with coefficient $`\gamma`$.
3. **Aligned repairs: the envelope degree is $`240\,r^6`$** (`Asym29.Sorted`, `Asym29.Degree`, `Asym25.Parking`,
   `Asym25.Cut`, `Asym25.Aligned`, `Asym25.Envelope`, `Asym25.Degree`, `Asym25.Params`, `Asym25.Packing`). Jay
   selects his labelled frames greedily, and a fraction $`1/(\Delta+1)`$ of all frames can be kept, where
   $`\Delta`$ bounds the frames whose envelopes can meet a given one. Because target frames are sorted, his
   reconstruction witnesses give at most $`12\,r^3`$ targets for a pair of joint states (this gave
   $`\Delta = 192\,r^7`$ instead of $`64\,r^8`$ in the earlier batches). A joint state is a role phase $`s`$ (the
   number of normal batches modulo $`r`$) with a prefix of a parking pair, and his envelope allows every joint
   state at every translation $`t`$. In a normal batch $`s`$ is the batch index, so $`s \equiv t`$ once the safe
   cut is a multiple of $`r`$. Only parking breaks this: he starts a parking interval at the phase where the
   forbidden control is mobile, which can be any phase. Here parking always uses the normal order and starts at
   role phase 0 or 2. During pairs of the normal order and its reverse a control stays in the slot it started
   in, the next slot of the normal cycle, or the mobile role; the two slots for phase 0 and the two for phase 2
   are different, so one of the two phases keeps the control out of the forbidden slot. The safe cut is taken
   among the multiples of $`r`$, which costs a factor $`r`$ in the room condition and nothing in the threshold.
   So a joint state $`(s, \cdot)`$ occurs at translation $`t`$ only if $`s \in \{0, 2\}`$ or
   $`s \equiv t \pmod r`$. If both states of a meeting are tied to their translations, the role phase of the
   target is fixed by the source and the translation difference, and the reconstruction fixes that difference;
   so the $`12\,r^3`$ targets cover all $`r`$ role phases of the target at once. The degree is at most
   $`12\,r^3\cdot 5\cdot r\,(2r)^2 = 240\,r^6`$ and the frame density is $`\beta \ge 1/(1300\,r^2)`$. The normal
   contours alone, without any repair, already meet about $`r^6`$ others (for one frame with $`r = 6`$ I counted
   8,015 and with $`r = 12`$ 1,405,843), so this is where a count of the degree stops.
4. **The controls form a transversal design** (`Asym22.Prime`, `Asym22.TD`, `Asym22.Width`). Jay's controls are
   the points $`(i, j)`$ with $`i < r`$ and $`j < rA`$, and the block with slope $`a < A`$ and intercept $`b`$
   takes the control $`(i, (ai + b) \bmod rA)`$ in row $`i`$. The same formula modulo a prime $`q`$ with
   $`q \ge A`$ and $`q \ge r`$ keeps the property that distinct blocks share at most one control: this is the
   transversal design $`\mathrm{TD}(r, q)`$ restricted to $`A`$ parallel classes. A stage then has $`W = rq`$
   controls instead of $`r^2 A`$, and with $`q`$ the least prime $`\ge A`$, Bertrand's postulate gives
   $`W \le 10400\,r^5(\lfloor\log_2 r\rfloor + 2)`$. The number of event types is at most $`r^4 W`$.
5. **The collision equations are written in local positions** (`Asym22.LocalPos`, `TD.PhysicalOldCuts`,
   `TD.GuardCatalogue`, `TD.PhysicalGuardExclusion`, `TD.CollisionToPrimary`, `TD.PrimaryCatalogue`,
   `TD.ProximityCatalogue`; new in this batch). A candidate has $`G = W - r`$ guards, each placed before one of
   the $`m`$ old letters, and a cyclic background of $`M = m + G`$ letters. Jay writes every collision equation
   in the original cuts $`x`$ of the guards, modulo $`m`$. A local cut of the background is $`x + e`$, where
   $`e`$ counts the guards before it, and he lets $`e`$ be any number from $`0`$ to $`G`$. Each term of a foreign
   relation then carries a slack $`G`$, so the constant of one event ranges over about $`13\,rW`$ values and the
   constant of a proximity equation over $`[-14r^2W, 14r^2W]`$. But two candidates that share a row see the same
   letters. The foreign local cut of a control and its position in the current background differ only by the
   active controls of the two blocks that stand before it, at most $`r`$ from each block. So I write the equations
   in the local position $`P_u = x_u + \#\{w : x_w < x_u\}`$ of each guard, modulo $`M`$: the foreign local cut of
   a guard is $`P_u + e`$ with $`|e| \le r + 1`$ (`resident_guard_local`), and the same holds for the control the
   two blocks share (`common_resident_local`). The constant of one event is then at most $`2r^2`$, and the
   constant of a proximity equation at most $`9r^3`$; there is no wrap term, because the event times and the
   equations now live on the same circle. The counts go through because $`x \mapsto P(x)`$ is injective
   (`localPos_injective`): the guard backgrounds whose positions satisfy a condition are at most all position
   tuples modulo $`M`$ that satisfy it, and $`(m + G)^G \le 2m^G`$ once $`m \ge 2G^2`$ (`power_double`). The
   guard-only deletion becomes $`20\,r^4W^2/m`$ (it was $`18\,r^3W^3/m`$).
6. **The constant of a proximity equation is taken pair by pair** (`Asym22.ProximityKeys`: `pairConstant`,
   `pairBound_sum`; new in this batch). The constant of the equation for two event types is at most
   $`(|a| + |a'|)\,2r^2 + |a|\,|a'|\,(4r + 2)`$, where $`a`$ and $`a'`$ are the coefficients of the two shared
   controls. A coefficient is $`\pm 1`$ for all but one coefficient assignment in $`r - 1`$, and $`r - 4`$ for that
   one; summed over the assignments of a fixed control it is $`2(r-3)(r-2)`$ (Jay's `fixed_label_abs_sum`, which
   he uses for the number of event times). Summing the interval counts of item 2 over all pairs of types, instead
   of using the largest constant for every pair, gives at most $`45\,r^2`$ per pair on average, not $`37\,r^3`$.
   The proximity deletion is $`181\,r^{10}W^2/m`$ (it was $`128\,r^{10}W^3/m`$).
7. **The threshold.** The block threshold is $`m \ge 1452\,r^{10} W^2`$, which follows from
   $`n \ge 2904\cdot 10400^2\,r^{20}(\lfloor\log_2 r\rfloor + 2)^2`$ (`Asym22.finite_covering_word_log`,
   coefficient $`2 + 26/r`$ for every $`r \ge 6`$ with $`6 \mid r`$). Choosing $`r`$ as the largest such multiple
   of 6, as in Jay's rate argument, and using $`\lfloor\log_2 n\rfloor + 3 \le 2\ln n`$ gives the bound above
   (`Asym22.LogRate`; the constant is $`52\,(4\cdot 2904\cdot 10400^2)^{1/20} + 4 \approx 213.4`$). With
   $`(\lfloor\log_2 r\rfloor + 2)^2 \le 16r`$ the same theorem gives the clean power 1/21 (`Asym22.Main`,
   `Asym22.Rate`).

In terms of the envelope degree $`\Delta \sim r^{\delta}`$ of item 3 ($`\delta = 7`$ here), the exponent is now
$`8 + 2\delta`$; in the exponent-1/28 batch it was $`7 + 3\delta`$.

### Which files are whose

Jay's files in [`lean/`](lean/) are unchanged, except three, each with a note in its header (the same three as in
the exponent-1/29 and exponent-1/28 batches):

- `Quantitative/ConstructionParameters.lean`: `sourceDegree` is $`192\,r^7`$ instead of $`64\,r^8`$, with the two
  proofs that unfold it. The bounds he states there still hold and are unchanged.
- `Quantitative/PackingSupply.lean`: the greedy selection uses `Asym29.degree_192` instead of his `degree_64`.
- `Quantitative/ProximityNormalization.lean`: one proof step, for the new `sourceDegree`.

His packing parameters and statements keep their meaning (the degree $`192\,r^7`$ of his envelopes); the ones for
the tied envelopes are new definitions next to them (`Asym25.Params`: `sourceDegree25`, `sourceEta25`,
`sourceBeta25`; `Asym25.Packing`, which repeats his `PackingSupply`, `LiteralPacking` and `UniformPacking` and needs
$`r \mid M`$). The end of his own chain on his grid (`Precision`, `Quantitative/MainTheorems`, `StatementAudit` and
the files they import) is not used by the statement of this batch; `Asym25.JayChain` imports it into the build, so a
build of `AlmanacSolution` checks that it still compiles here.

[`lean/Asym25/`](lean/Asym25/) is new. `Parking` is the role lemma for parking with the normal order and the choice
of the phase, with his two avoidance theorems restated for it. `Cut` finds the safe cut among the multiples of
$`r`$; its other four theorems are his `exists_grouped_circle`, `exists_repair_program`, `construct_repair` and
`construct_counted_repair` with the cut as a parameter, his text with that one change. `Aligned` shows that his
compiler produces a program in which the role phase follows the batch index, and that every row then lies in the
tied envelope. `Envelope` converts that envelope to the form that is counted, as his `PhysicalEnvelope` does.
`Degree` is the count. Of the copies in `lean/Asym22/TD/`, `CanonicalEventAvoidance`, `CandidateConstruction`,
`CandidateRowState`, `GlobalSourceFamily`, `CandidateCollision` and `ProximityNormalization` change for this.

His grid is not changed in place. [`lean/Asym22/TD/`](lean/Asym22/TD/) holds copies of the 33 files of his that
depend on `Quantitative.ActiveGrid` and are needed here (namespace `CoefficientTwoPrecision.TD`, imports pointed
at the copies), each with a note in its header that says what was changed and in which batch. In 17 of them
nothing else changed. Three carry only the column count `tdQ r A` of the transversal design in place of `r * A`
(`ActiveGrid`, `GridAlphabet`, `CandidateSpace`). The other thirteen were changed for the local positions of
item 5:

- `PhysicalOldCuts`: four theorems added at the end. They compare a foreign local cut with the local position
  of the same control in the current background (`common_guard_cut`, `before_le_add`, `resident_guard_local`,
  `common_resident_local`). His theorems above them are unchanged.
- `GuardCatalogue`, `PhysicalGuardExclusion`, `GuardCandidateLoss`, `GuardRelativeLoss`: the guard-only relations
  are congruences modulo $`m + G`$ in the local positions, with constants up to `localOffsetBound d` $`= 2r^2`$.
- `PrimaryCatalogue`, `CollisionToPrimary`, `ProximityCatalogue`, `ProximitySurvivors`: the same for the events and
  the proximity equation; `rightSide` has no wrap term.
- `CatalogueBounds`: the bounds for the new constants.
- `GuardCollisionProjection`, `ProximityPairCount`, `ProximityDeletion`: theorems of his that the construction no
  longer uses are left out (`no_guard_only_frame`; the two per-equation counts; the count by the maximum of the
  two rank cases).

His `GlobalRetention`, `SourceSelection` and `SparseFamilyConstruction` are not copied; their roles are taken by
`Asym22.IntervalKeys`, `Asym22.Retention` and `Asym22.Certificate`. His originals stay in the tree, unchanged,
and are not imported by `AlmanacSolution`.

[`lean/Asym22/Bertrand.lean`](lean/Asym22/Bertrand.lean) is a copy of the part of Mathlib's
`NumberTheory/Primorial.lean` and `NumberTheory/Bertrand.lean` that proves Bertrand's postulate for
$`n \ge 512`$ (Patrick Stevens, Bolton Bailey, Yury Kudryashov, Bhavik Mehta; Apache License 2.0), with only the
namespace changed. Mathlib's own module cannot be imported here: it brings in `Mathlib.Data.List.GetD`, which
declares the same lemma name as the inherited `Lean435Compatibility.lean`.

[`lean/Asym22/`](lean/Asym22/) is otherwise mine. `LocalPos` is new: the position map, its injectivity, the
literal index of an old-cut block, the foreign relation with bounded offsets, and the power ratio. `Prime` is the
column modulus and the intersection proof; `Width` is the width of the design and the definitions that depend on
it. `ProximityKeys` and `IntervalKeys` are the modules of the earlier batches in local positions, with the
constants of item 6. The chain `Params`, `Retention`, `CountRatio`, `Transfer`, `Certificate`, `Stages`, `Rate`,
`Main`, `LogRate` is the chain of my exponent-1/28 batch with the new deletion bounds and threshold. From the
earlier batches the tree keeps `Asym29/Sorted`, `Asym29/Degree`, `Asym35/Width` (the block count $`A`$),
`Asym35/Pending`, `Asym35/Words` and `Asym33/IntervalCount`; the modules that gave the exponent 1/28 are replaced
by `Asym22` and are no longer in the tree. Parts copied from his files with only names, the threshold or the
constants changed say so in their docstrings.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.explicit_error_log20\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

On my machine (Linux under WSL 2, Mathlib from its cache, 2 CPUs) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory | 2,402 s (3,829 jobs) | 0.84 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 1,177 s | 0.77 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.explicit_error_log20` | 43 s, 381 MB | |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 176 s, "Checked 46198 declarations with no errors" | 0.39 GB |

The statements NanoDa printed are in [`verification/almanac/`](verification/almanac/).

## Sources and licences

`lean/` (except `lean/Asym35/`, `lean/Asym33/`, `lean/Asym29/` and `lean/Asym22/`), `LICENSE`, `NOTICE`,
`licenses/`, `lake-manifest.json` and `lean-toolchain` come from commit `882721e` of Jay Pantone's repository, under
the Apache License 2.0, with the inherited sources and licences that his [`NOTICE`](NOTICE) lists (among them
Xiaolong Liu's files under CC BY 4.0, which keep that licence). His `NOTICE` and `LICENSE` are unchanged; the three
files of his that I changed are named above and carry a note. `lean/Asym22/TD/` holds copies of his files, under his
licence, with the changes named in each header. `lean/Asym22/Bertrand.lean` is copied from Mathlib under the Apache
License 2.0, with its authors named in its header. `lakefile.toml` is his, with the four `Asym` libraries added to
the globs and its comment changed. The rest of `lean/Asym35/`, `lean/Asym33/`, `lean/Asym29/`, `lean/Asym22/` and
`AlmanacAdapter.lean` are mine (the adapter's `fact_eq` and `covers_iff` are his lemmas), under the Apache License
2.0. `AlmanacDefs.lean`, `AlmanacStatement.lean` and `AlmanacChallenge.lean` are the Almanac's files, unchanged.
