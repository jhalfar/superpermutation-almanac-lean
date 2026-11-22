import Asym28.Certificate
import Asym28.Stages
import Asym28.Rate

/-!
# The quantitative superpermutation theorem with exponent 1/29

Addition to Jay Pantone's quantitative development (release 9ccbe66); the
construction and almost all of the proof are his. Six changes to the
bookkeeping give the exponent 29 in place of 61 (the first five are those of
the earlier batches of exponents 1/37, 1/35, 1/32 and 1/29):

* the proximity deletion is counted by (event-type pair, constant) keys
  (`ProximityKeys`);
* the transfer uses the cost-to-density ratio, in which the guard, rounding,
  retention, background and insertion factors cancel (`CountRatio`,
  `Transfer`), so the deletions only need to stay below `1/8`;
* the pending mass halves on every group of sparse blocks (`Asym35.Pending`),
  so `ρ ≥ 4 r (log₂ r + 2)` blocks of density are enough for a pending mass of
  `1/r` (Jay's argument needs `ρ ≥ r^2` for `4/r`). The source family has
  `A = ⌈4 r^2 (log₂ r + 2)/β⌉` blocks per letter (`Asym35.Width`) and the
  coefficient is `2 + 26/r` instead of `2 + 74/r`;
* for a fixed pair of event types the keys differ only in the constant, so
  their union is the set where one linear form lands in an interval
  (`Asym33.IntervalCount`, `IntervalKeys`, `Retention`);
* a target frame is sorted, so the packing degree is `192 r^7` in place of
  `64 r^8` (`Asym29.Sorted`, `Asym29.Degree`) and `β ≥ 1/(1040 r^3)`;
* the controls form a transversal design, `r` rows and `q` columns with `q`
  the least prime `≥ A`, in place of Jay's grid of `r A` columns
  (`Asym28.TD`, `Asym28.Prime`). Distinct blocks still meet in at most one
  control, and the width is `W = r q ≤ 8320 r^6 (log₂ r + 2)` in place of
  `r^2 A ≤ 4161 r^7 (log₂ r + 2)` (`Width`). The event-type count is then
  only `≤ r^4 W` (on the grid `r^3 W`), so the proximity deletion is
  `128 r^10 W^3 / m`.

The block threshold is `m ≥ 2960 r^10 W^3`, which with
`W ≤ 8320 r^6 (log₂ r + 2)`, `(log₂ r + 2)^3 ≤ 16 r` and `n ≤ 2m` is implied
by `n ≥ 94720 · 8320^3 · r^29`.
`Covers`, `F3` and the minimum length `L` are the original definitions.
-/

namespace CoefficientTwoPrecision.Asym28

open CoefficientTwoPrecision.Asym35

open Asymptotics

/-- The finite bound for an actual covering word, threshold `94720 · 8320^3 · r^29`. -/
theorem finite_covering_word_29 (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (94720 * 8320 ^ 3) * r ^ 29 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 26) * (n - 4).factorial :=
  finite_word28 n r hr ((logThreshold_le r (by omega)).trans hn) (supplier28 r hr)

theorem original_finite_bound_29 : OriginalWordFiniteBound28 := by
  intro r hr hdiv n hn
  exact finite_covering_word_29 n r hr hdiv hn

/-- The explicit normalised error for the original minimum covering length,
with `remainderConstant28 = 52 · (94720 · 8320^3)^(1/29) + 4 ≈ 179.4`. -/
theorem shortest_length_error_29 (n : Nat)
    (hn : transferConstant28 * 6 ^ 29 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant28 * (n : ℝ) ^ (-1 / 29 : ℝ) :=
  conditional_normalized_error_bound28 original_finite_bound_29 n hn hn8

/-- The two-sided error term with exponent 1/29. -/
theorem shortest_length_asymptotic_29 :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 29 : ℝ)) :=
  conditional_asymptotic_29 original_finite_bound_29

/-- The constant of the error bound is at most 201. -/
theorem remainderConstant28_le : remainderConstant28 ≤ 201 := by
  have h : ((transferConstant28 : ℕ) : ℝ) ^ (1 / 29 : ℝ) ≤ 197 / 52 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (29 : ℝ) = ((29 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [transferConstant28]
  unfold remainderConstant28
  linarith

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ 94720 · 8320^3 · 6^29`
(about `2.01 · 10^39`) the shortest superpermutation length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 201 (n-4)! n^(-1/29)`. -/
def ExplicitError28 : Prop :=
  ∀ n : Nat, 94720 * 8320 ^ 3 * 6 ^ 29 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        201 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 29 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        201 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 29 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `shortest_length_error_29`
(the proof is that of Jay's `AlmanacAdapter.explicit_error`). -/
theorem explicit_error_29 : ExplicitError28 := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := shortest_length_error_29 n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 29 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant28_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : remainderConstant28 * (n : ℝ) ^ (-1 / 29 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 201 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 29 : ℝ) := by
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

end CoefficientTwoPrecision.Asym28

#print axioms CoefficientTwoPrecision.Asym28.supplier28
#print axioms CoefficientTwoPrecision.Asym28.finite_covering_word_29
#print axioms CoefficientTwoPrecision.Asym28.original_finite_bound_29
#print axioms CoefficientTwoPrecision.Asym28.shortest_length_error_29
#print axioms CoefficientTwoPrecision.Asym28.shortest_length_asymptotic_29
#print axioms CoefficientTwoPrecision.Asym28.remainderConstant28_le
#print axioms CoefficientTwoPrecision.Asym28.explicit_error_29
