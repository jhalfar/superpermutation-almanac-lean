import Asym35.Certificate
import Asym35.Stages
import Asym35.Rate

/-!
# The quantitative superpermutation theorem with exponent 1/35

Addition to Jay Pantone's quantitative development (release 9ccbe66); the
construction and almost all of the proof are his. Three changes to the
bookkeeping give the exponent 35 in place of 61 (the first two are those of
the exponent-37 batch, `Asym37`):

* the proximity deletion is counted by (event-type pair, constant) keys
  (`ProximityKeys`, `Retention`): `128 r^10 W^3 / m` instead of
  `7118280 r^22 W^4 / m`;
* the transfer uses the cost-to-density ratio, in which the guard, rounding,
  retention, background and insertion factors cancel (`CountRatio`,
  `Transfer`), so the deletions only need to stay below `1/8`;
* the pending mass halves on every group of sparse blocks (`Pending`), so
  `ρ ≥ 4 r (log₂ r + 2)` blocks of density are enough for a pending mass of
  `1/r` (Jay's argument needs `ρ ≥ r^2` for `4/r`). The source family has
  `A = ⌈4 r^2 (log₂ r + 2)/β⌉` blocks per letter (`Width`), the width is
  `W ≤ 1405 r^8 (log₂ r + 2)` instead of `352 r^9`, and the coefficient is
  `2 + 26/r` instead of `2 + 74/r`.

The block threshold is `m ≥ 2960 r^10 W^3`, which with
`W ≤ 1405 r^8 (log₂ r + 2)`, `(log₂ r + 2)^3 ≤ 16 r` and `n ≤ 2m` is implied
by `n ≥ 94720 · 1405^3 · r^35`.
`Covers`, `F3` and the minimum length `L` are the original definitions.
-/

namespace CoefficientTwoPrecision.Asym35

open Asymptotics

/-- The finite bound for an actual covering word, threshold `94720 · 1405^3 · r^35`. -/
theorem finite_covering_word_35 (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (94720 * 1405 ^ 3) * r ^ 35 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 26) * (n - 4).factorial :=
  finite_word35 n r hr ((logThreshold_le r (by omega)).trans hn) (supplier35 r hr)

theorem original_finite_bound_35 : OriginalWordFiniteBound35 := by
  intro r hr hdiv n hn
  exact finite_covering_word_35 n r hr hdiv hn

/-- The explicit normalised error for the original minimum covering length,
with `remainderConstant35 = 52 · (94720 · 1405^3)^(1/35) + 4 ≈ 138.27`. -/
theorem shortest_length_error_35 (n : Nat)
    (hn : transferConstant35 * 6 ^ 35 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant35 * (n : ℝ) ^ (-1 / 35 : ℝ) :=
  conditional_normalized_error_bound35 original_finite_bound_35 n hn hn8

/-- The two-sided error term with exponent 1/35. -/
theorem shortest_length_asymptotic_35 :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 35 : ℝ)) :=
  conditional_asymptotic_35 original_finite_bound_35

/-- The constant of the error bound is at most 139. -/
theorem remainderConstant35_le : remainderConstant35 ≤ 139 := by
  have h : ((transferConstant35 : ℕ) : ℝ) ^ (1 / 35 : ℝ) ≤ 135 / 52 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (35 : ℝ) = ((35 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [transferConstant35]
  unfold remainderConstant35
  linarith

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ 94720 · 1405^3 · 6^35`
(about `4.52 · 10^41`) the shortest superpermutation length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 139 (n-4)! n^(-1/35)`. -/
def ExplicitError35 : Prop :=
  ∀ n : Nat, 94720 * 1405 ^ 3 * 6 ^ 35 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        139 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 35 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        139 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 35 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `shortest_length_error_35`
(the proof is that of Jay's `AlmanacAdapter.explicit_error`). -/
theorem explicit_error_35 : ExplicitError35 := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := shortest_length_error_35 n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 35 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant35_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : remainderConstant35 * (n : ℝ) ^ (-1 / 35 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 139 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 35 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hp hf.le)
    linarith
  constructor
  · obtain ⟨w, hw, hwl⟩ := ConstAsym.L_spec n
    refine ⟨w, hw, ?_⟩
    rw [hwl]
    nlinarith
  · intro w hw
    have hmin : (ConstAsym.L n : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast ConstAsym.L_le_length hw
    nlinarith

end CoefficientTwoPrecision.Asym35

#print axioms CoefficientTwoPrecision.Asym35.supplier35
#print axioms CoefficientTwoPrecision.Asym35.finite_covering_word_35
#print axioms CoefficientTwoPrecision.Asym35.original_finite_bound_35
#print axioms CoefficientTwoPrecision.Asym35.shortest_length_error_35
#print axioms CoefficientTwoPrecision.Asym35.shortest_length_asymptotic_35
#print axioms CoefficientTwoPrecision.Asym35.remainderConstant35_le
#print axioms CoefficientTwoPrecision.Asym35.explicit_error_35
