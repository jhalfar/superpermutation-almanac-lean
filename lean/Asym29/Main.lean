import Asym29.Certificate
import Asym29.Stages
import Asym29.Rate

/-!
# The quantitative superpermutation theorem with exponent 1/30

Addition to Jay Pantone's quantitative development (release 9ccbe66); the
construction and almost all of the proof are his. Five changes to the
bookkeeping give the exponent 30 in place of 61 (the first four are those of
the earlier batches, `Asym37`, `Asym35` and `Asym33`):

* the proximity deletion is counted by (event-type pair, constant) keys
  (`Asym37.ProximityKeys`);
* the transfer uses the cost-to-density ratio, in which the guard, rounding,
  retention, background and insertion factors cancel (`CountRatio`,
  `Transfer`), so the deletions only need to stay below `1/8`;
* the pending mass halves on every group of sparse blocks (`Asym35.Pending`),
  so `ρ ≥ 4 r (log₂ r + 2)` blocks of density are enough for a pending mass of
  `1/r` (Jay's argument needs `ρ ≥ r^2` for `4/r`). The source family has
  `A = ⌈4 r^2 (log₂ r + 2)/β⌉` blocks per letter (`Asym35.Width`) and the
  coefficient is `2 + 26/r` instead of `2 + 74/r`;
* for a fixed pair of event types the keys differ only in the constant, so
  their union is the set where one linear form lands in an interval: the
  proximity deletion is `128 r^8 W^3 / m` (`Asym33.IntervalCount`,
  `Asym33.IntervalKeys`, `Retention`);
* a target frame is sorted, so the reconstruction witnesses for one pair of
  joint states give at most `12 r^3` labelled frames instead of `4 r^4`. The
  packing degree is `192 r^7` in place of `64 r^8` (`Sorted`, `Degree`), the
  density is `β ≥ 1/(1040 r^3)`, and the width is
  `W ≤ 4161 r^7 (log₂ r + 2)` in place of `1405 r^8 (log₂ r + 2)`.

The block threshold is `m ≥ 2960 r^8 W^3`, which with
`W ≤ 4161 r^7 (log₂ r + 2)`, `(log₂ r + 2)^3 ≤ 16 r` and `n ≤ 2m` is implied
by `n ≥ 94720 · 4161^3 · r^30`.
`Covers`, `F3` and the minimum length `L` are the original definitions.
-/

namespace CoefficientTwoPrecision.Asym29

open CoefficientTwoPrecision.Asym35

open Asymptotics

/-- The finite bound for an actual covering word, threshold `94720 · 4161^3 · r^30`. -/
theorem finite_covering_word_30 (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (94720 * 4161 ^ 3) * r ^ 30 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 26) * (n - 4).factorial :=
  finite_word29 n r hr ((logThreshold_le r (by omega)).trans hn) (supplier29 r hr)

theorem original_finite_bound_30 : OriginalWordFiniteBound29 := by
  intro r hr hdiv n hn
  exact finite_covering_word_30 n r hr hdiv hn

/-- The explicit normalised error for the original minimum covering length,
with `remainderConstant29 = 52 · (94720 · 4161^3)^(1/30) + 4 ≈ 179.4`. -/
theorem shortest_length_error_30 (n : Nat)
    (hn : transferConstant29 * 6 ^ 30 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant29 * (n : ℝ) ^ (-1 / 30 : ℝ) :=
  conditional_normalized_error_bound29 original_finite_bound_30 n hn hn8

/-- The two-sided error term with exponent 1/30. -/
theorem shortest_length_asymptotic_30 :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 30 : ℝ)) :=
  conditional_asymptotic_30 original_finite_bound_30

/-- The constant of the error bound is at most 180. -/
theorem remainderConstant29_le : remainderConstant29 ≤ 180 := by
  have h : ((transferConstant29 : ℕ) : ℝ) ^ (1 / 30 : ℝ) ≤ 176 / 52 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [transferConstant29]
  unfold remainderConstant29
  linarith

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ 94720 · 4161^3 · 6^30`
(about `1.51 · 10^39`) the shortest superpermutation length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 180 (n-4)! n^(-1/30)`. -/
def ExplicitError30 : Prop :=
  ∀ n : Nat, 94720 * 4161 ^ 3 * 6 ^ 30 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        180 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 30 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        180 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 30 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `shortest_length_error_30`
(the proof is that of Jay's `AlmanacAdapter.explicit_error`). -/
theorem explicit_error_30 : ExplicitError30 := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := shortest_length_error_30 n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 30 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant29_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : remainderConstant29 * (n : ℝ) ^ (-1 / 30 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 180 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 30 : ℝ) := by
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

end CoefficientTwoPrecision.Asym29

#print axioms CoefficientTwoPrecision.Asym29.supplier29
#print axioms CoefficientTwoPrecision.Asym29.finite_covering_word_30
#print axioms CoefficientTwoPrecision.Asym29.original_finite_bound_30
#print axioms CoefficientTwoPrecision.Asym29.shortest_length_error_30
#print axioms CoefficientTwoPrecision.Asym29.shortest_length_asymptotic_30
#print axioms CoefficientTwoPrecision.Asym29.remainderConstant29_le
#print axioms CoefficientTwoPrecision.Asym29.explicit_error_30
