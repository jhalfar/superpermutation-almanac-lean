# Superpermutation bounds in Lean

Lean proofs of bounds on the length of the shortest superpermutation, laid out as batch submissions to the
[Superpermutation Almanac](https://superpermutations.com). The full development, with the words and the other
proofs, is in [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations). My first batch (two upper
bounds for large $`n`$) is commit `af99e83`, the second (a lower bound for 8 symbols) is commit `7e6664d`, the
third (872 for 6 symbols, checked by the kernel) is commit `7b7b96d`, the fourth (5,899 for 7 symbols with
`native_decide`) is commit `a09f9ef`, the fifth (5,898 for 7 symbols, checked by the kernel) is commit
`5cc0ac3` and the sixth (12 and 13 symbols from Theorem C) is commit `7ed009a`. This commit holds the seventh.

## This batch: the error after $`2(n-4)!`$ with exponent 1/37

[`AlmanacSolution.lean`](AlmanacSolution.lean) states one custom result, `AlmanacAdapter.ExplicitError37`:

```math
\left|S(n) - \bigl(n! + (n-1)! + (n-2)! + 2(n-4)!\bigr)\right| \le 306\,(n-4)!\,n^{-1/37}
\qquad\text{for every } n \ge 5920\cdot 352^{3}\cdot 6^{37}\ (\approx 1.6\cdot 10^{40}).
```

It has the same form as Jay Pantone's statement for [b/42](https://superpermutations.com/b/42),
$`400\,(n-4)!\,n^{-1/61}`$ for $`n \ge 8\cdot 10^{12}\cdot 352^4\cdot 6^{61}`$ ($`\approx 3.6\cdot 10^{70}`$). As in
his statement the lower side uses the same constant; it comes from my Theorem B, which gives an error of $`4/n`$.

### Whose proof this is

The construction and almost all of the proof are Jay Pantone's: his release "A polynomial error estimate for
superpermutation length",
[jaypantone/2026-10-superpermutation-asymptotics](https://github.com/jaypantone/2026-10-superpermutation-asymptotics),
commit `9ccbe66`, packaged for the Almanac in commit `882721e` (branch `almanac-submission`). His files in
[`lean/`](lean/) are unchanged. The new part is [`lean/Asym37/`](lean/Asym37/) (9 modules, 2,368 lines). It changes
how the proof counts, not the construction:

1. **His lemma already gives $`r^{59}`$, and $`10^{12}`$ can be $`36\cdot 10^6`$.** His finite theorem assumes
   $`n \ge C r^{61}`$; his lemma `primitive_threshold_le_polynomial` proves $`8 r E \le C r^{59}`$ and then weakens
   it, and his error budget `CountErrorBudget.numerator_bound` needs only $`36\cdot 10^6`$ in place of the
   $`10^{12}`$ in $`E = 10^{12} r^{22} W^4`$. This alone gives exponent 1/59. The two points below go further.
2. **A new count of the proximity equations.** A candidate is deleted when two of its events for different
   forbidden pairs come close. The equation that pair gives depends only on the two event types and on one
   integer constant, so the deleted set is a union over distinct (type pair, constant) keys. There are at most
   $`r^3 W`$ types and the constant has absolute value at most $`14 r^2 W`$, which gives a deletion of
   $`128\,r^{10} W^3/m`$ in place of $`7{,}118{,}280\,r^{22} W^4/m`$ (`ProximityKeys`, `Retention`).
3. **A deletion bound that only needs the ratio $`g/f`$.** The transfer uses the cost per selected class, and in
   that ratio the guard, rounding, retention and insertion factors cancel. So the deletions only have to stay below
   $`1/8`$ instead of below $`1/r`$ (`CountRatio`, `Transfer`).

Together: coefficient $`2 + 74/r`$ for every $`r \ge 6`$ with $`6 \mid r`$ and $`n \ge 5920\cdot 352^3\, r^{37}`$
($`\approx 2.6\cdot 10^{11} r^{37}`$), `CoefficientTwoPrecision.Asym37.finite_covering_word_37`, and from it the
bound above (`shortest_length_error_37`, `explicit_error_37`; the constant is $`148\,C^{1/37} + 4 \approx 305.1`$).

The modules: `Params` (the new threshold $`2960\,r^{10} W^3`$ and the size estimates that depended on the old one),
`ProximityKeys` and `Retention` (point 2), `CountRatio` and `Transfer` (point 3), `Certificate` and `Stages` (his
source families and stage iteration for the new interface), `Rate` (his parameter choice and real exponent, with 37)
and `Main`. Parts copied from his files with only the threshold hypothesis or the interface changed say so in
their docstrings.

## Build

Lean `leanprover/lean4:v4.35.0`, Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`:

```
lake exe cache get
lake build AlmanacSolution
printf 'import AlmanacSolution\n#print axioms AlmanacSubmission.explicit_error_37\n' > Axioms.lean
lake env lean Axioms.lean
```

The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `native_decide`.

On my machine (Linux under WSL 2, Mathlib from its cache, 4 CPUs, a busy machine) I measured:

| step | time | memory |
|---|---|---|
| `lake build AlmanacSolution` from an empty build directory (3,658 jobs) | 2,312 s | 0.9 GB |
| `lake env leanchecker --fresh AlmanacSolution`, 1 CPU | 1,197 s | 0.8 GB |
| `lake env leanexport AlmanacSolution -- AlmanacSubmission.explicit_error_37` | 46 s, 288 MB | |
| NanoDa of the Lean toolchain on that export, 1 CPU, only the three axioms permitted | 107 s, "Checked 36120 declarations with no errors" | 0.3 GB |

The statements NanoDa printed are in [`verification/almanac/`](verification/almanac/).

## Sources and licences

`lean/` (except `lean/Asym37/`), `LICENSE`, `NOTICE`, `licenses/`, `lake-manifest.json` and `lean-toolchain` come
from commit `882721e` of Jay Pantone's repository, under the Apache License 2.0, with the inherited sources and
licences that his [`NOTICE`](NOTICE) lists (among them Xiaolong Liu's files under CC BY 4.0, which keep that
licence). His `NOTICE` and `LICENSE` are unchanged. `lakefile.toml` is his, with `Asym37.+` added to the library
globs and its comment changed. `lean/Asym37/` and `AlmanacAdapter.lean` are new (the adapter's `fact_eq` and
`covers_iff` are his lemmas), under the Apache License 2.0. `AlmanacDefs.lean`, `AlmanacStatement.lean` and
`AlmanacChallenge.lean` are the Almanac's files, unchanged.
