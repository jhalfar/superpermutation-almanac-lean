import Asym37.Certificate
import Asym37.Stages
import Asym37.Rate

/-!
# The quantitative superpermutation theorem with exponent 1/37

Addition to Jay Pantone's quantitative development (release 9ccbe66); the
construction and almost all of the proof are his. Two changes to the
bookkeeping give the exponent 37 in place of 61:

* the proximity deletion is counted by (event-type pair, constant) keys
  (`ProximityKeys`, `Retention`): `128 r^10 W^3 / m` instead of
  `7118280 r^22 W^4 / m`;
* the transfer uses the cost-to-density ratio, in which the guard, rounding,
  retention, background and insertion factors cancel (`CountRatio`,
  `Transfer`), so the deletions only need to stay below `1/8`.

The block threshold is `m ≥ 2960 r^10 W^3`, which with `W ≤ 352 r^9` and
`n ≤ 2m` is implied by `n ≥ 5920 · 352^3 · r^37`.
`Covers`, `F3` and the minimum length `L` are the original definitions.
-/

namespace CoefficientTwoPrecision.Asym37

open Asymptotics

/-- The finite bound for an actual covering word, threshold `5920 · 352^3 · r^37`. -/
theorem finite_covering_word_37 (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (5920 * 352 ^ 3) * r ^ 37 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 74) * (n - 4).factorial :=
  finite_word37 n r hr hn (supplier37 r hr)

theorem original_finite_bound_37 : OriginalWordFiniteBound37 := by
  intro r hr hdiv n hn
  exact finite_covering_word_37 n r hr hdiv hn

/-- The explicit normalised error for the original minimum covering length,
with `remainderConstant37 = 148 · (5920 · 352^3)^(1/37) + 4 ≈ 305.09`. -/
theorem shortest_length_error_37 (n : Nat)
    (hn : transferConstant37 * 6 ^ 37 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant37 * (n : ℝ) ^ (-1 / 37 : ℝ) :=
  conditional_normalized_error_bound37 original_finite_bound_37 n hn hn8

/-- The two-sided error term with exponent 1/37. -/
theorem shortest_length_asymptotic_37 :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 37 : ℝ)) :=
  conditional_asymptotic_37 original_finite_bound_37

/-- The constant of the error bound is at most 306. -/
theorem remainderConstant37_le : remainderConstant37 ≤ 306 := by
  have h : ((transferConstant37 : ℕ) : ℝ) ^ (1 / 37 : ℝ) ≤ 151 / 74 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (37 : ℝ) = ((37 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [transferConstant37]
  unfold remainderConstant37
  linarith

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ 5920 · 352^3 · 6^37`
(about `1.598 · 10^40`) the shortest superpermutation length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 306 (n-4)! n^(-1/37)`. -/
def ExplicitError37 : Prop :=
  ∀ n : Nat, 5920 * 352 ^ 3 * 6 ^ 37 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        306 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 37 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        306 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 37 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `shortest_length_error_37`
(the proof is that of Jay's `AlmanacAdapter.explicit_error`). -/
theorem explicit_error_37 : ExplicitError37 := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := shortest_length_error_37 n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 37 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant37_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : remainderConstant37 * (n : ℝ) ^ (-1 / 37 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 306 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 37 : ℝ) := by
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

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.supplier37
#print axioms CoefficientTwoPrecision.Asym37.finite_covering_word_37
#print axioms CoefficientTwoPrecision.Asym37.original_finite_bound_37
#print axioms CoefficientTwoPrecision.Asym37.shortest_length_error_37
#print axioms CoefficientTwoPrecision.Asym37.shortest_length_asymptotic_37
#print axioms CoefficientTwoPrecision.Asym37.remainderConstant37_le
#print axioms CoefficientTwoPrecision.Asym37.explicit_error_37
