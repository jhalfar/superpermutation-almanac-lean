import Asym37.Params
import Asym37.ProximityKeys
import Quantitative.SourceSelection

/-!
# Exponent 37: the retained fraction of the candidate set

Addition to Jay Pantone's quantitative development (release 9ccbe66).
`GlobalRetention.proximity_loss` bounds the proximity deletion by
`7118280 r^22 W^4 / m`. With the key count of `ProximityKeys` the same
deletion is at most `128 r^10 W^3 / m` (using `W ≥ 128 r^9`). The guard-only
deletion `GuardRelativeLoss.retained_loss` is unchanged. The selection
theorem is `SourceSelection.exists_selection` with the new threshold.
-/

namespace CoefficientTwoPrecision.Asym37

open GuardCatalogue CandidateSpace LabelledReconstruction CatalogueBounds
open ProximitySurvivors ProximityDeletion ProximityNormalization GuardRelativeLoss
open SortedFrameSupply ProximityCatalogue CandidateFactorization

/-- The key count of `ProximityKeys`, normalised: the arithmetic part. -/
theorem key_constant_bound (d A : Nat) (hA : 0 < A)
    (hW9 : 128 * (d + 3) ^ 9 ≤ width d A) :
    guardKeyCount d A * (4 * (d - 1) ^ 2) + freeKeyCount d A * (1560 * (d + 3) ^ 13) ≤
      128 * (d + 3) ^ 10 * width d A ^ 3 := by
  set r := d + 3 with hr
  set W := width d A with hWdef
  have hr1 : 1 ≤ r := by omega
  have hW1 : 1 ≤ W := le_trans (by omega) (width_ge d A hA)
  have hrW : 1 ≤ r ^ 2 * W := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hB : 2 * constantBound d A + 1 ≤ 29 * (r ^ 2 * W) := by
    unfold constantBound
    rw [← hr, ← hWdef]
    have : 14 * r ^ 2 * W = 14 * (r ^ 2 * W) := by ring
    omega
  have hT : typeTotal d A ^ 2 ≤ r ^ 6 * W ^ 2 := by
    calc
      typeTotal d A ^ 2 ≤ (r ^ 3 * W) ^ 2 := Nat.pow_le_pow_left (typeTotal_le d A) 2
      _ = r ^ 6 * W ^ 2 := by ring
  have hd1 : (d - 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hguard : guardKeyCount d A * (4 * (d - 1) ^ 2) ≤ 116 * r ^ 10 * W ^ 3 := by
    unfold guardKeyCount
    calc
      typeTotal d A ^ 2 * (2 * constantBound d A + 1) * (4 * (d - 1) ^ 2) ≤
          (r ^ 6 * W ^ 2) * (29 * (r ^ 2 * W)) * (4 * r ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hT hB) (Nat.mul_le_mul_left 4 hd1)
      _ = 116 * r ^ 10 * W ^ 3 := by ring
  have hfirst : 2 * (d - 1) ^ 2 + 1 ≤ 2 * r ^ 2 := by
    have : (d - 1) ^ 2 + 1 ≤ r ^ 2 := by
      have h1 : d - 1 + 1 ≤ r := by omega
      have h2 := Nat.pow_le_pow_left h1 2
      nlinarith
    omega
  have hsecond : (d + 2) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hK2 : freeKeyCount d A ≤ 58 * (r ^ 6 * W) := by
    unfold freeKeyCount
    calc
      (2 * (d - 1) ^ 2 + 1) * (d + 2) ^ 2 * (2 * constantBound d A + 1) ≤
          (2 * r ^ 2) * r ^ 2 * (29 * (r ^ 2 * W)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hB
      _ = 58 * (r ^ 6 * W) := by ring
  have hWsq : 16384 * r ^ 18 ≤ W ^ 2 := by
    calc
      16384 * r ^ 18 = (128 * r ^ 9) ^ 2 := by ring
      _ ≤ W ^ 2 := Nat.pow_le_pow_left hW9 2
  have hr9 : 1 ≤ r ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hfree : freeKeyCount d A * (1560 * r ^ 13) ≤ 12 * r ^ 10 * W ^ 3 := by
    calc
      freeKeyCount d A * (1560 * r ^ 13) ≤ 58 * (r ^ 6 * W) * (1560 * r ^ 13) :=
        Nat.mul_le_mul_right _ hK2
      _ = 90480 * (r ^ 19 * W) := by ring
      _ ≤ 196608 * (r ^ 19 * W) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 196608 * (r ^ 9 * (r ^ 19 * W)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity))
      _ = 12 * r ^ 10 * W * (16384 * r ^ 18) := by ring
      _ ≤ 12 * r ^ 10 * W * W ^ 2 := Nat.mul_le_mul_left _ hWsq
      _ = 12 * r ^ 10 * W ^ 3 := by ring
  calc
    guardKeyCount d A * (4 * (d - 1) ^ 2) + freeKeyCount d A * (1560 * r ^ 13) ≤
        116 * r ^ 10 * W ^ 3 + 12 * r ^ 10 * W ^ 3 := Nat.add_le_add hguard hfree
    _ = 128 * r ^ 10 * W ^ 3 := by ring

/-- `GlobalRetention.proximity_loss` with the key count. -/
theorem proximity_loss37 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (hW9 : 128 * (d + 3) ^ 9 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card *
        ((128 : ℚ) * (d + 3) ^ 10 * (width d A : ℚ) ^ 3 / m) := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hguards : m ^ (guardNumber d A) ≤ 2 * (m.descFactorial (guardNumber d A)) := falling_half m (guardNumber d A) hm hGm hsize
  have hselection := selected_scaled d (m + guardNumber d A) S.card hhalf
  have hframe : m * frameBound m d A ≤
      (d - 1).factorial * (1560 * (d + 3) ^ 13 * (m.descFactorial (guardNumber d A)) * S.card) := by
    have h := frame_bound_scaled m (m + guardNumber d A) d (m.descFactorial (guardNumber d A)) S.card (by omega) (by omega) hselection
    simpa only [frameBound, mul_assoc] using h
  have hpower : m * m ^ ((guardNumber d A) - 1) = m ^ (guardNumber d A) := by rw [← pow_succ', Nat.sub_add_cancel hG]
  have hguardPart : m * (S.card * (m ^ ((guardNumber d A) - 1) * (2 * (d - 1) ^ 2))) ≤
      (4 * (d - 1) ^ 2) * ((m.descFactorial (guardNumber d A)) * S.card) := by
    calc
      m * (S.card * (m ^ ((guardNumber d A) - 1) * (2 * (d - 1) ^ 2))) =
          S.card * (2 * (d - 1) ^ 2) * (m * m ^ ((guardNumber d A) - 1)) := by ring
      _ = S.card * (2 * (d - 1) ^ 2) * m ^ (guardNumber d A) := by rw [hpower]
      _ ≤ S.card * (2 * (d - 1) ^ 2) * (2 * (m.descFactorial (guardNumber d A))) := Nat.mul_le_mul_left _ hguards
      _ = (4 * (d - 1) ^ 2) * ((m.descFactorial (guardNumber d A)) * S.card) := by ring
  have hdel := deleted_keys hm hM hd hA S hS
  let removed := (GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card
  have hcand : (candidates m d A S).card = (A * ((d + 3) * A)) * (m.descFactorial (guardNumber d A)) * S.card := candidates_card m d A S
  have hconst := key_constant_bound d A hA hW9
  have hscaled : (d - 1).factorial * (m * removed) ≤
      (d - 1).factorial * ((128 * (d + 3) ^ 10 * width d A ^ 3) * (candidates m d A S).card) := by
    calc
      (d - 1).factorial * (m * removed) = m * ((d - 1).factorial * removed) := by ring
      _ ≤ m * ((A * ((d + 3) * A)) *
          ((d - 1).factorial * (guardKeyCount d A *
              (S.card * (m ^ ((guardNumber d A) - 1) * (2 * (d - 1) ^ 2)))) +
            freeKeyCount d A * frameBound m d A)) := Nat.mul_le_mul_left m hdel
      _ = (A * ((d + 3) * A)) *
          ((d - 1).factorial * guardKeyCount d A *
              (m * (S.card * (m ^ ((guardNumber d A) - 1) * (2 * (d - 1) ^ 2)))) +
            freeKeyCount d A * (m * frameBound m d A)) := by ring
      _ ≤ (A * ((d + 3) * A)) *
          ((d - 1).factorial * guardKeyCount d A * ((4 * (d - 1) ^ 2) * ((m.descFactorial (guardNumber d A)) * S.card)) +
            freeKeyCount d A * ((d - 1).factorial * (1560 * (d + 3) ^ 13 * (m.descFactorial (guardNumber d A)) * S.card))) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hguardPart)
          (Nat.mul_le_mul_left _ hframe))
      _ = (d - 1).factorial * ((guardKeyCount d A * (4 * (d - 1) ^ 2) +
            freeKeyCount d A * (1560 * (d + 3) ^ 13)) *
            ((A * ((d + 3) * A)) * (m.descFactorial (guardNumber d A)) * S.card)) := by ring
      _ ≤ (d - 1).factorial * ((128 * (d + 3) ^ 10 * width d A ^ 3) *
            ((A * ((d + 3) * A)) * (m.descFactorial (guardNumber d A)) * S.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hconst)
      _ = _ := by rw [hcand]
  have hnat := Nat.le_of_mul_le_mul_left hscaled (Nat.factorial_pos (d - 1))
  have hsub := Finset.card_le_card (survivors_subset hA S)
  have hrat : (m : ℚ) *
      (((GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card) ≤
        (128 * ((d : ℚ) + 3) ^ 10 * (width d A : ℚ) ^ 3) * (candidates m d A S).card := by
    have hcast : ((m * removed : Nat) : ℚ) ≤
        (((128 * (d + 3) ^ 10 * width d A ^ 3) * (candidates m d A S).card : Nat) : ℚ) := by
      exact_mod_cast hnat
    simpa only [removed, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat] using hcast
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (show (0 : ℚ) < m by exact_mod_cast hm)).mpr
  nlinarith

theorem total_loss37 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (hW9 : 128 * (d + 3) ^ 9 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((candidates m d A S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card * (deletionNumerator37 (d + 3) (width d A) / m) := by
  have hfirst := GuardRelativeLoss.retained_loss m d A hm (by omega) hA hsize S
  have hsecond := proximity_loss37 hm hd hA hM hsize hW9 S hS hhalf
  have hsum := add_le_add hfirst hsecond
  unfold deletionNumerator37
  convert hsum using 1 <;> ring

theorem retention_error37 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : guardNumber d A ^ 2 ≤ m)
    (hW9 : 128 * (d + 3) ^ 9 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    |((survivors m d A hA S).card : ℚ) / (candidates m d A S).card - 1| ≤
      deletionNumerator37 (d + 3) (width d A) / m := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hguards : 0 < m.descFactorial (guardNumber d A) := Nat.descFactorial_pos.mpr hGm
  have heta := CandidateFactorization.eta_pos (d + 3) (by omega)
  have hMpos : (0 : ℚ) < ((m + guardNumber d A : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < m + guardNumber d A)
  have hselected : 0 < S.card := by
    have hpositive : 0 < sourceEta (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 := by
      positivity
    exact_mod_cast hpositive.trans_le hhalf
  have hraw : 0 < (candidates m d A S).card := by rw [candidates_card]; positivity
  have hrawQ : (0 : ℚ) < (candidates m d A S).card := by exact_mod_cast hraw
  have hupper : ((survivors m d A hA S).card : ℚ) ≤ (candidates m d A S).card := by
    exact_mod_cast Finset.card_le_card
      ((survivors_subset hA S).trans (GuardCandidateLoss.retained_subset m d A hA S))
  have hloss := total_loss37 hm hd hA hM hsize hW9 S hS hhalf
  have hlo : 1 - deletionNumerator37 (d + 3) (width d A) / m ≤
      ((survivors m d A hA S).card : ℚ) / (candidates m d A S).card := by
    apply (le_div_iff₀ hrawQ).mpr
    nlinarith
  have hhi := (div_le_one hrawQ).mpr hupper
  have herror : 0 ≤ deletionNumerator37 (d + 3) (width d A) / m := by
    unfold deletionNumerator37
    positivity
  apply abs_le.mpr
  constructor <;> linarith

/-- `SourceSelection.size_conditions` from the new threshold. -/
theorem size_conditions37 (d m : Nat) (hd : 3 ≤ d)
    (hm : threshold37 (d + 3) ≤ m) :
    0 < m ∧ 2 * (d + 2) ≤ m + guardNumber d (sourceA (d + 3)) ∧
      38 * (d + 3) ^ 4 ≤ m + guardNumber d (sourceA (d + 3)) ∧
      m + guardNumber d (sourceA (d + 3)) ≤ 2 * m ∧
      guardNumber d (sourceA (d + 3)) ^ 2 ≤ m ∧
      radius d < m + guardNumber d (sourceA (d + 3)) ∧
      (2 * (2 * (d + 3) + 1) + 1) * PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) <
        m + guardNumber d (sourceA (d + 3)) := by
  have hs := threshold_conditions37 (d + 3) m (by omega) hm
  have hA := sourceA_pos (d + 3) (by omega)
  have hG := guard_le d (sourceA (d + 3))
  have hW : width d (sourceA (d + 3)) = sourceWidth (d + 3) := rfl
  have hM : m + guardNumber d (sourceA (d + 3)) = backgroundSize (d + 3) m := by
    rw [guard_number_eq]
    rfl
  have hpower : d + 3 ≤ (d + 3) ^ 4 := le_self_pow₀ (by omega) (by decide)
  have hsmall : 4 * (d + 3) + 2 < backgroundSize (d + 3) m := by omega
  have hK := occurrence_bound d (sourceA (d + 3)) hA
  rw [hW] at hG hK
  have hG2 := Nat.pow_le_pow_left hG 2
  have hroom := (Nat.mul_le_mul_left (4 * (d + 3) + 3) hK).trans_lt hs.2.2.2.2.2.2
  rw [hM]
  refine ⟨hs.1, by omega, hs.2.2.2.1, by omega, by omega, ?_, ?_⟩
  · simpa only [radius] using hsmall
  · simpa only [show 2 * (2 * (d + 3) + 1) + 1 = 4 * (d + 3) + 3 by ring] using hroom

/-- `SourceSelection.exists_selection` from the new threshold, with the new
deletion numerator. -/
theorem exists_selection37 (d m : Nat) [NeZero (m + guardNumber d (sourceA (d + 3)))]
    (hd : 3 ≤ d)
    (hm : threshold37 (d + 3) ≤ m) :
    ∃ S : Finset (Labelled (m + guardNumber d (sourceA (d + 3))) d),
      S ⊆ labelledFrames (m + guardNumber d (sourceA (d + 3))) d ∧
      S.card = ⌊sourceEta (d + 3) *
        ((m + guardNumber d (sourceA (d + 3)) : Nat) : ℚ) ^ d⌋₊ ∧
      (candidates m d (sourceA (d + 3)) S).card = candidateCount (d + 3) m ∧
      |((survivors m d (sourceA (d + 3)) (sourceA_pos (d + 3) (by omega)) S).card : ℚ) /
        candidateCount (d + 3) m - 1| ≤
          deletionNumerator37 (d + 3) (sourceWidth (d + 3)) / m ∧
      ∀ {α : Type} (background : Fin (m + guardNumber d (sourceA (d + 3))) → α)
        (embed : FiniteRoles.Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ∀ first second : List α, LiteralPacking.InEnvelope background embed source first →
            LiteralPacking.InEnvelope background embed target second →
              ¬ first.IsRotated second := by
  have hs := size_conditions37 d m hd hm
  obtain ⟨S, hS, hcard, hsep⟩ := UniformPacking.exists_uniform_literal_separated hd
    (show 2 ≤ m + guardNumber d (sourceA (d + 3)) by omega) hs.2.2.1
  have hcandidates := prescribed_card m d S hcard
  have hhalf : sourceEta (d + 3) *
      ((m + guardNumber d (sourceA (d + 3)) : Nat) : ℚ) ^ d / 2 ≤ S.card := by
    rw [hcard, guard_number_eq]
    simpa only [Nat.add_sub_cancel, backgroundSize] using
      selected_floor_half37 (d + 3) m (by omega) hm
  have hW9 : 128 * (d + 3) ^ 9 ≤ width d (sourceA (d + 3)) :=
    sourceWidth_lower37 (d + 3) (by omega)
  have hretention := retention_error37 hs.1 hd (sourceA_pos (d + 3) (by omega))
    hs.2.2.2.1 hs.2.2.2.2.1 hW9 S hS hhalf
  rw [hcandidates] at hretention
  exact ⟨S, hS, hcard, hcandidates, hretention, hsep⟩

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.key_constant_bound
#print axioms CoefficientTwoPrecision.Asym37.proximity_loss37
#print axioms CoefficientTwoPrecision.Asym37.retention_error37
#print axioms CoefficientTwoPrecision.Asym37.exists_selection37
