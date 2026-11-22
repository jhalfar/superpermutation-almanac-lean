import Asym22.TD.GuardCandidateLoss

/-!
Copy of Jay Pantone's `Quantitative/GuardRelativeLoss.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.GuardRelativeLoss`, imports of the copied modules
redirected to `Asym22.TD`. Changed: `guard_positive` uses `tdQ ≥ 2`, and the
guard-only deletion was `18 r^3 W^3 / m` in the exponent-28 batch (Jay: `18 r^2 W^3 / m`).
Changed for the exponent-22 batch (November 2026): in local positions the guard-only
deletion is `20 r^4 W^2 / m`; it needs `2 G^2 ≤ m` (the position tuples are counted modulo
`m + G`, and `(m + G)^G ≤ 2 m^G`).

# The relative cost of deleting guard-only collisions

The actual cardinality inequality is normalized using the falling
factorial lower bound. The selected frame cardinality stays as the same
factor on both sides throughout the argument.
-/

namespace CoefficientTwoPrecision.TD.GuardRelativeLoss

open GuardCatalogue GuardCandidateLoss CandidateSpace LabelledReconstruction CatalogueBounds

theorem falling_half (m G : Nat) (hm : 0 < m) (hG : G ≤ m) (hsize : G ^ 2 ≤ m) :
    m ^ G ≤ 2 * m.descFactorial G := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hsizeQ : (G : ℚ) ^ 2 ≤ m := by exact_mod_cast hsize
  have hG0 : (0 : ℚ) ≤ G := by positivity
  have he : (G : ℚ) * ((G : ℚ) - 1) / (2 * m) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * m)).mpr
    nlinarith
  have hfall := (CountingRatios.falling_bounds m G hm hG).1
  have hlo : (1 / 2 : ℚ) ≤ (m.descFactorial G : ℚ) / (m : ℚ) ^ G := by linarith
  have hmul := (le_div_iff₀ (pow_pos hmQ G)).mp hlo
  have h : (m : ℚ) ^ G ≤ 2 * (m.descFactorial G : ℚ) := by linarith
  exact_mod_cast h

theorem guard_positive (d A : Nat) (hA : 0 < A) : 0 < guardNumber d A := by
  have hq : 2 ≤ tdQ (d + 3) A := (tdQ_prime (d + 3) A).two_le
  have h := Nat.mul_le_mul_left (d + 3) hq
  unfold guardNumber
  omega

theorem scaled_loss (m d A : Nat) (hm : 0 < m) (hA : 0 < A)
    (hsize : 2 * guardNumber d A ^ 2 ≤ m) :
    m * lossBound m d A ≤
      (20 * (d + 3) ^ 4 * width d A ^ 2) * m.descFactorial (guardNumber d A) := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hhalf := falling_half m (guardNumber d A) hm hGm (by omega)
  have hdouble := LocalPos.power_double m (guardNumber d A) hsize
  have hcoef : GuardCatalogue.eventCount d A * (d - 1) ≤
      5 * (d + 3) ^ 4 * width d A ^ 2 := by
    calc
      GuardCatalogue.eventCount d A * (d - 1) ≤
          (5 * (d + 3) ^ 3 * width d A ^ 2) * (d + 3) :=
        Nat.mul_le_mul (guard_event_bound d A hA) (by omega)
      _ = 5 * (d + 3) ^ 4 * width d A ^ 2 := by ring
  have hpower : (m + guardNumber d A) * (m + guardNumber d A) ^ (guardNumber d A - 1) =
      (m + guardNumber d A) ^ guardNumber d A := by
    rw [← pow_succ', Nat.sub_add_cancel hG]
  calc
    m * lossBound m d A =
        (GuardCatalogue.eventCount d A * (d - 1)) *
          (m * (m + guardNumber d A) ^ (guardNumber d A - 1)) := by
      unfold lossBound
      ring
    _ ≤ (GuardCatalogue.eventCount d A * (d - 1)) *
          ((m + guardNumber d A) * (m + guardNumber d A) ^ (guardNumber d A - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
    _ = (GuardCatalogue.eventCount d A * (d - 1)) * (m + guardNumber d A) ^ guardNumber d A := by
      rw [hpower]
    _ ≤ (5 * (d + 3) ^ 4 * width d A ^ 2) * (m + guardNumber d A) ^ guardNumber d A :=
      Nat.mul_le_mul_right _ hcoef
    _ ≤ (5 * (d + 3) ^ 4 * width d A ^ 2) * (2 * m ^ guardNumber d A) :=
      Nat.mul_le_mul_left _ hdouble
    _ ≤ (5 * (d + 3) ^ 4 * width d A ^ 2) * (2 * (2 * m.descFactorial (guardNumber d A))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hhalf)
    _ = (20 * (d + 3) ^ 4 * width d A ^ 2) * m.descFactorial (guardNumber d A) := by ring

theorem retained_loss (m d A : Nat) (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (hsize : 2 * guardNumber d A ^ 2 ≤ m)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    ((candidates m d A S).card : ℚ) - (retained m d A hA S).card ≤
      (candidates m d A S).card *
        ((20 : ℚ) * (d + 3) ^ 4 * (width d A : ℚ) ^ 2 / m) := by
  have hbase := Nat.mul_le_mul_left m (retained_lower m d A hm hd hA S)
  have hscaled := Nat.mul_le_mul_left ((A * tdQ (d + 3) A) * S.card)
    (scaled_loss m d A hm hA hsize)
  have hnat : m * (candidates m d A S).card ≤ m * (retained m d A hA S).card +
      (20 * (d + 3) ^ 4 * width d A ^ 2) * (candidates m d A S).card := by
    rw [candidates_card] at hbase ⊢
    nlinarith
  have hrat : (m : ℚ) * (candidates m d A S).card ≤
      (m : ℚ) * (retained m d A hA S).card +
        (20 * ((d : ℚ) + 3) ^ 4 * (width d A : ℚ) ^ 2) * (candidates m d A S).card := by
    exact_mod_cast hnat
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hmQ).mpr
  nlinarith

end CoefficientTwoPrecision.TD.GuardRelativeLoss

#print axioms CoefficientTwoPrecision.TD.GuardRelativeLoss.scaled_loss
#print axioms CoefficientTwoPrecision.TD.GuardRelativeLoss.retained_loss
