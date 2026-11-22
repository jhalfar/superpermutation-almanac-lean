import Asym22.Certificate
import Asym22.Stages
import Asym22.Rate

/-!
# The quantitative superpermutation theorem with exponent 1/21

Addition to Jay Pantone's quantitative development (release 9ccbe66); the
construction and almost all of the proof are his. Eight changes to the
bookkeeping give the exponent 23 in place of 61 (the first six are those of
the earlier batches of exponents 1/37, 1/35, 1/32, 1/29 and 1/28):

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
  (`Asym22.TD`, `Asym22.Prime`), so the width is
  `W = r q ≤ 10400 r^5 (log₂ r + 2)` (`Width`) and there are at most `r^4 W`
  event types;
* the collision equations are written in the local positions of the guards
  modulo `m + G` instead of their original cuts modulo `m` (`LocalPos`,
  `TD.PhysicalOldCuts`, `TD.CollisionToPrimary`). Two candidates that share
  a row see the same letters, so a foreign local cut differs from the local
  position by at most `r + 1`, where an original cut differs from it by up
  to `G`. The constants of an event are then bounded by `2 r^2` (they were
  of order `r W`), those of a proximity equation by `9 r^3` (`14 r^2 W`);
* the constant of a proximity equation is taken for each pair of event
  types from the coefficients of the two shared controls, which are `1` for
  all but one coefficient assignment in `d + 2`, and the counts are summed
  over the pairs (`ProximityKeys.pairBound_sum`): `45 r^2` values per pair
  on average. The proximity deletion is `181 r^10 W^2 / m`
  (`128 r^10 W^3 / m`).

The block threshold is `m ≥ 1452 r^10 W^2`, which with
`W ≤ 10400 r^5 (log₂ r + 2)`, `(log₂ r + 2)^2 ≤ 16 r` and `n ≤ 2m` is implied
by `n ≥ 46464 · 10400^2 · r^21`.
`Covers`, `F3` and the minimum length `L` are the original definitions.
-/

namespace CoefficientTwoPrecision.Asym22

open CoefficientTwoPrecision.Asym35

open Asymptotics

/-- The finite bound for an actual covering word, threshold `46464 · 10400^2 · r^21`. -/
theorem finite_covering_word_23 (n r : Nat) (hr : 6 ≤ r) (_hdiv : 6 ∣ r)
    (hn : (46464 * 10400 ^ 2) * r ^ 21 ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 26) * (n - 4).factorial :=
  finite_word22 n r hr ((logThreshold_le r (by omega)).trans hn) (supplier22 r hr)

theorem original_finite_bound_23 : OriginalWordFiniteBound22 := by
  intro r hr hdiv n hn
  exact finite_covering_word_23 n r hr hdiv hn

/-- The explicit normalised error for the original minimum covering length,
with `remainderConstant22 = 52 · (46464 · 10400^2)^(1/21) + 4 ≈ 213.3`. -/
theorem shortest_length_error_23 (n : Nat)
    (hn : transferConstant22 * 6 ^ 21 ≤ n) (hn8 : 8 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      remainderConstant22 * (n : ℝ) ^ (-1 / 21 : ℝ) :=
  conditional_normalized_error_bound22 original_finite_bound_23 n hn hn8

/-- The two-sided error term with exponent 1/21. -/
theorem shortest_length_asymptotic_23 :
    (fun n : Nat => (ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ) -
      2 * ((n - 4).factorial : ℝ)) =O[Filter.atTop]
      (fun n : Nat => ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 21 : ℝ)) :=
  conditional_asymptotic_23 original_finite_bound_23

/-- The constant of the error bound is at most 214. -/
theorem remainderConstant28_le : remainderConstant22 ≤ 214 := by
  have h : ((transferConstant22 : ℕ) : ℝ) ^ (1 / 21 : ℝ) ≤ 210 / 52 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [transferConstant22]
  unfold remainderConstant22
  linarith

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ 46464 · 10400^2 · 6^21`
(about `1.10 · 10^29`) the shortest superpermutation length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 214 (n-4)! n^(-1/21)`. -/
def ExplicitError21 : Prop :=
  ∀ n : Nat, 46464 * 10400 ^ 2 * 6 ^ 21 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        214 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 21 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        214 * ((n - 4).factorial : Real) * (n : Real) ^ (-1 / 21 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `shortest_length_error_23`
(the proof is that of Jay's `AlmanacAdapter.explicit_error`). -/
theorem explicit_error_21 : ExplicitError21 := by
  intro n hn
  have hn8 : 8 ≤ n := le_trans (by norm_num) hn
  have herr := shortest_length_error_23 n (by exact hn) hn8
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 21 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK := remainderConstant28_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : remainderConstant22 * (n : ℝ) ^ (-1 / 21 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 214 * ((n - 4).factorial : ℝ) * (n : ℝ) ^ (-1 / 21 : ℝ) := by
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

end CoefficientTwoPrecision.Asym22

#print axioms CoefficientTwoPrecision.Asym22.supplier22
#print axioms CoefficientTwoPrecision.Asym22.finite_covering_word_23
#print axioms CoefficientTwoPrecision.Asym22.original_finite_bound_23
#print axioms CoefficientTwoPrecision.Asym22.shortest_length_error_23
#print axioms CoefficientTwoPrecision.Asym22.shortest_length_asymptotic_23
#print axioms CoefficientTwoPrecision.Asym22.remainderConstant28_le
#print axioms CoefficientTwoPrecision.Asym22.explicit_error_21
