import Asym25.Packing
import Asym22.Params
import Asym22.IntervalKeys
import Asym22.TD.ProximityNormalization
import Asym22.TD.CandidateEvents

/-!
# The retained fraction of the candidate set

Addition to Jay Pantone's quantitative development (release 9ccbe66).
Jay's `GlobalRetention.proximity_loss` bounds the proximity deletion by
`7118280 r^22 W^4 / m`. With the count of `IntervalKeys` in local positions (one interval
for each pair of event types, `45 r^2` values per pair on average) the same deletion is at
most `181 r^10 W^2 / m` on the transversal design (using `W ≥ 512 r^5`). The guard-only deletion
is `TD.GuardRelativeLoss.retained_loss`, `20 r^4 W^2 / m`. The selection theorem is
`SourceSelection.exists_selection` with the new threshold.
-/

namespace CoefficientTwoPrecision.Asym22

open CoefficientTwoPrecision.Asym33

open CoefficientTwoPrecision.Asym35

open TD.GuardCatalogue TD.CandidateSpace LabelledReconstruction TD.CatalogueBounds
open TD.ProximitySurvivors TD.ProximityDeletion TD.ProximityNormalization TD.GuardRelativeLoss
open SortedFrameSupply TD.ProximityCatalogue CandidateFactorization

/-- The type-pair count of `IntervalKeys`, normalised: the arithmetic part. -/
theorem key_constant_bound (d A : Nat) (hA : 0 < A)
    (hW8 : 512 * (d + 3) ^ 5 ≤ width d A) :
    typeTotal d A ^ 2 * (4 * typeBound d A) + freeKeyCount d A * (1560 * (d + 3) ^ 13) ≤
      181 * (d + 3) ^ 10 * width d A ^ 2 := by
  set r := d + 3 with hr
  set W := width d A with hWdef
  have hr33 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hB : 2 * constantBound d A + 1 ≤ 19 * r ^ 3 := by
    unfold constantBound
    rw [← hr]
    omega
  have hT : typeTotal d A ^ 2 ≤ r ^ 8 * W ^ 2 := by
    calc
      typeTotal d A ^ 2 ≤ (r ^ 4 * W) ^ 2 := Nat.pow_le_pow_left (typeTotal_le d A) 2
      _ = r ^ 8 * W ^ 2 := by ring
  have hguard : typeTotal d A ^ 2 * (4 * typeBound d A) ≤ 180 * r ^ 10 * W ^ 2 := by
    calc
      typeTotal d A ^ 2 * (4 * typeBound d A) ≤ (r ^ 8 * W ^ 2) * (4 * (45 * r ^ 2)) :=
        Nat.mul_le_mul hT (Nat.mul_le_mul_left 4 (le_of_eq rfl))
      _ = 180 * r ^ 10 * W ^ 2 := by ring
  have hfirst : 2 * (d - 1) ^ 2 + 1 ≤ 2 * r ^ 2 := by
    have : (d - 1) ^ 2 + 1 ≤ r ^ 2 := by
      have h1 : d - 1 + 1 ≤ r := by omega
      have h2 := Nat.pow_le_pow_left h1 2
      nlinarith
    omega
  have hsecond : (d + 2) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hK2 : freeKeyCount d A ≤ 38 * r ^ 7 := by
    unfold freeKeyCount
    calc
      (2 * (d - 1) ^ 2 + 1) * (d + 2) ^ 2 * (2 * constantBound d A + 1) ≤
          (2 * r ^ 2) * r ^ 2 * (19 * r ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hB
      _ = 38 * r ^ 7 := by ring
  have hWsq : 262144 * r ^ 10 ≤ W ^ 2 := by
    calc
      262144 * r ^ 10 = (512 * r ^ 5) ^ 2 := by ring
      _ ≤ W ^ 2 := Nat.pow_le_pow_left hW8 2
  have hfree : freeKeyCount d A * (1560 * r ^ 13) ≤ r ^ 10 * W ^ 2 := by
    calc
      freeKeyCount d A * (1560 * r ^ 13) ≤ 38 * r ^ 7 * (1560 * r ^ 13) :=
        Nat.mul_le_mul_right _ hK2
      _ = 59280 * r ^ 20 := by ring
      _ ≤ 262144 * r ^ 20 := Nat.mul_le_mul_right _ (by norm_num)
      _ = r ^ 10 * (262144 * r ^ 10) := by ring
      _ ≤ r ^ 10 * W ^ 2 := Nat.mul_le_mul_left _ hWsq
  calc
    typeTotal d A ^ 2 * (4 * typeBound d A) + freeKeyCount d A * (1560 * r ^ 13) ≤
        180 * r ^ 10 * W ^ 2 + r ^ 10 * W ^ 2 := Nat.add_le_add hguard hfree
    _ = 181 * r ^ 10 * W ^ 2 := by ring

/-- `GlobalRetention.proximity_loss` with the type-pair count. -/
theorem proximity_loss22 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : 2 * guardNumber d A ^ 2 ≤ m)
    (hW8 : 512 * (d + 3) ^ 5 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta25 (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((TD.GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card *
        ((181 : ℚ) * (d + 3) ^ 10 * (width d A : ℚ) ^ 2 / m) := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hguards : m ^ (guardNumber d A) ≤ 2 * (m.descFactorial (guardNumber d A)) :=
    falling_half m (guardNumber d A) hm hGm (by omega)
  have hdouble := TD.LocalPos.power_double m (guardNumber d A) hsize
  have hselection := selected_scaled d (m + guardNumber d A) S.card hhalf
  have hframe : m * frameBound m d A ≤
      (d - 1).factorial * (1560 * (d + 3) ^ 13 * (m.descFactorial (guardNumber d A)) * S.card) := by
    have h := frame_bound_scaled m (m + guardNumber d A) d (m.descFactorial (guardNumber d A)) S.card (by omega) (by omega) hselection
    simpa only [frameBound, mul_assoc] using h
  have hpower : (m + guardNumber d A) * (m + guardNumber d A) ^ ((guardNumber d A) - 1) =
      (m + guardNumber d A) ^ (guardNumber d A) := by
    rw [← pow_succ', Nat.sub_add_cancel hG]
  have hguardPart : m * (S.card * ((m + guardNumber d A) ^ ((guardNumber d A) - 1) *
      typeBound d A)) ≤ (4 * typeBound d A) * ((m.descFactorial (guardNumber d A)) * S.card) := by
    calc
      m * (S.card * ((m + guardNumber d A) ^ ((guardNumber d A) - 1) * typeBound d A)) =
          S.card * typeBound d A *
            (m * (m + guardNumber d A) ^ ((guardNumber d A) - 1)) := by ring
      _ ≤ S.card * typeBound d A *
            ((m + guardNumber d A) * (m + guardNumber d A) ^ ((guardNumber d A) - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      _ = S.card * typeBound d A * (m + guardNumber d A) ^ (guardNumber d A) := by rw [hpower]
      _ ≤ S.card * typeBound d A * (2 * m ^ (guardNumber d A)) := Nat.mul_le_mul_left _ hdouble
      _ ≤ S.card * typeBound d A * (2 * (2 * (m.descFactorial (guardNumber d A)))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hguards)
      _ = (4 * typeBound d A) * ((m.descFactorial (guardNumber d A)) * S.card) := by ring
  have hdel := deleted_types hm hM hd hA S hS
  let removed := (TD.GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card
  have hcand : (candidates m d A S).card = (A * TD.tdQ (d + 3) A) * (m.descFactorial (guardNumber d A)) * S.card := candidates_card m d A S
  have hconst := key_constant_bound d A hA hW8
  have hscaled : (d - 1).factorial * (m * removed) ≤
      (d - 1).factorial * ((181 * (d + 3) ^ 10 * width d A ^ 2) * (candidates m d A S).card) := by
    calc
      (d - 1).factorial * (m * removed) = m * ((d - 1).factorial * removed) := by ring
      _ ≤ m * ((A * TD.tdQ (d + 3) A) *
          ((d - 1).factorial * (typeTotal d A ^ 2 *
              (S.card * ((m + guardNumber d A) ^ ((guardNumber d A) - 1) * typeBound d A))) +
            freeKeyCount d A * frameBound m d A)) := Nat.mul_le_mul_left m hdel
      _ = (A * TD.tdQ (d + 3) A) *
          ((d - 1).factorial * typeTotal d A ^ 2 *
              (m * (S.card * ((m + guardNumber d A) ^ ((guardNumber d A) - 1) * typeBound d A))) +
            freeKeyCount d A * (m * frameBound m d A)) := by ring
      _ ≤ (A * TD.tdQ (d + 3) A) *
          ((d - 1).factorial * typeTotal d A ^ 2 * ((4 * typeBound d A) * ((m.descFactorial (guardNumber d A)) * S.card)) +
            freeKeyCount d A * ((d - 1).factorial * (1560 * (d + 3) ^ 13 * (m.descFactorial (guardNumber d A)) * S.card))) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hguardPart)
          (Nat.mul_le_mul_left _ hframe))
      _ = (d - 1).factorial * ((typeTotal d A ^ 2 * (4 * typeBound d A) +
            freeKeyCount d A * (1560 * (d + 3) ^ 13)) *
            ((A * TD.tdQ (d + 3) A) * (m.descFactorial (guardNumber d A)) * S.card)) := by ring
      _ ≤ (d - 1).factorial * ((181 * (d + 3) ^ 10 * width d A ^ 2) *
            ((A * TD.tdQ (d + 3) A) * (m.descFactorial (guardNumber d A)) * S.card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hconst)
      _ = _ := by rw [hcand]
  have hnat := Nat.le_of_mul_le_mul_left hscaled (Nat.factorial_pos (d - 1))
  have hsub := Finset.card_le_card (survivors_subset hA S)
  have hrat : (m : ℚ) *
      (((TD.GuardCandidateLoss.retained m d A hA S).card : ℚ) - (survivors m d A hA S).card) ≤
        (181 * ((d : ℚ) + 3) ^ 10 * (width d A : ℚ) ^ 2) * (candidates m d A S).card := by
    have hcast : ((m * removed : Nat) : ℚ) ≤
        (((181 * (d + 3) ^ 10 * width d A ^ 2) * (candidates m d A S).card : Nat) : ℚ) := by
      exact_mod_cast hnat
    simpa only [removed, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat] using hcast
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (show (0 : ℚ) < m by exact_mod_cast hm)).mpr
  nlinarith

theorem total_loss22 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : 2 * guardNumber d A ^ 2 ≤ m)
    (hW8 : 512 * (d + 3) ^ 5 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta25 (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    ((candidates m d A S).card : ℚ) - (survivors m d A hA S).card ≤
      (candidates m d A S).card * (deletionNumerator22 (d + 3) (width d A) / m) := by
  have hfirst := TD.GuardRelativeLoss.retained_loss m d A hm (by omega) hA hsize S
  have hsecond := proximity_loss22 hm hd hA hM hsize hW8 S hS hhalf
  have hsum := add_le_add hfirst hsecond
  unfold deletionNumerator22
  convert hsum using 1 <;> ring

theorem retention_error22 {m d A : Nat} [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hd : 3 ≤ d) (hA : 0 < A)
    (hM : m + guardNumber d A ≤ 2 * m) (hsize : 2 * guardNumber d A ^ 2 ≤ m)
    (hW8 : 512 * (d + 3) ^ 5 ≤ width d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ SortedFrameSupply.labelledFrames (m + guardNumber d A) d)
    (hhalf : sourceEta25 (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 ≤ S.card) :
    |((survivors m d A hA S).card : ℚ) / (candidates m d A S).card - 1| ≤
      deletionNumerator22 (d + 3) (width d A) / m := by
  have hG := guard_positive d A hA
  have hGm : guardNumber d A ≤ m := by nlinarith
  have hguards : 0 < m.descFactorial (guardNumber d A) := Nat.descFactorial_pos.mpr hGm
  have heta := sourceEta25_pos (d + 3) (by omega)
  have hMpos : (0 : ℚ) < ((m + guardNumber d A : Nat) : ℚ) := by
    exact_mod_cast (by omega : 0 < m + guardNumber d A)
  have hselected : 0 < S.card := by
    have hpositive : 0 < sourceEta25 (d + 3) * ((m + guardNumber d A : Nat) : ℚ) ^ d / 2 := by
      positivity
    exact_mod_cast hpositive.trans_le hhalf
  have hq := TD.tdQ_pos (d + 3) A
  have hraw : 0 < (candidates m d A S).card := by rw [candidates_card]; positivity
  have hrawQ : (0 : ℚ) < (candidates m d A S).card := by exact_mod_cast hraw
  have hupper : ((survivors m d A hA S).card : ℚ) ≤ (candidates m d A S).card := by
    exact_mod_cast Finset.card_le_card
      ((survivors_subset hA S).trans (TD.GuardCandidateLoss.retained_subset m d A hA S))
  have hloss := total_loss22 hm hd hA hM hsize hW8 S hS hhalf
  have hlo : 1 - deletionNumerator22 (d + 3) (width d A) / m ≤
      ((survivors m d A hA S).card : ℚ) / (candidates m d A S).card := by
    apply (le_div_iff₀ hrawQ).mpr
    nlinarith
  have hhi := (div_le_one hrawQ).mpr hupper
  have herror : 0 ≤ deletionNumerator22 (d + 3) (width d A) / m := by
    unfold deletionNumerator22
    positivity
  apply abs_le.mpr
  constructor <;> linarith

/-- `SourceSelection.size_conditions` from the new threshold. -/
theorem size_conditions22 (d m : Nat) (hd : 3 ≤ d)
    (hm : threshold22 (d + 3) ≤ m) :
    0 < m ∧ 2 * (d + 2) ≤ m + guardNumber d (sourceA35 (d + 3)) ∧
      38 * (d + 3) ^ 4 ≤ m + guardNumber d (sourceA35 (d + 3)) ∧
      m + guardNumber d (sourceA35 (d + 3)) ≤ 2 * m ∧
      2 * guardNumber d (sourceA35 (d + 3)) ^ 2 ≤ m ∧
      radius d < m + guardNumber d (sourceA35 (d + 3)) ∧
      (d + 3) * ((2 * (2 * (d + 3) + 1) + 1) *
          TD.PrimaryCatalogue.occurrenceBound d (sourceA35 (d + 3))) <
        m + guardNumber d (sourceA35 (d + 3)) := by
  have hs := threshold_conditions22 (d + 3) m (by omega) hm
  have hA := sourceA35_pos (d + 3) (by omega)
  have hG := guard_le d (sourceA35 (d + 3))
  have hW : width d (sourceA35 (d + 3)) = sourceWidth22 (d + 3) := rfl
  have hM : m + guardNumber d (sourceA35 (d + 3)) = backgroundSize22 (d + 3) m := by
    rw [guard_number_eq22]
    rfl
  have hpower : d + 3 ≤ (d + 3) ^ 4 := le_self_pow₀ (by omega) (by decide)
  have hsmall : 4 * (d + 3) + 2 < backgroundSize22 (d + 3) m := by omega
  have hK := occurrence_bound d (sourceA35 (d + 3)) hA
  rw [hW] at hG hK
  have hG2 := Nat.pow_le_pow_left hG 2
  have hroom := (Nat.mul_le_mul_left (d + 3)
    (Nat.mul_le_mul_left (4 * (d + 3) + 3) hK)).trans_lt hs.2.2.2.2.2.2
  rw [hM]
  refine ⟨hs.1, by omega, hs.2.2.2.1, by omega, by omega, ?_, ?_⟩
  · simpa only [radius] using hsmall
  · simpa only [show 2 * (2 * (d + 3) + 1) + 1 = 4 * (d + 3) + 3 by ring] using hroom

/-- `SourceSelection.exists_selection` from the new threshold, with the new
deletion numerator. -/
theorem exists_selection22 (d m : Nat) [NeZero (m + guardNumber d (sourceA35 (d + 3)))]
    (hd : 3 ≤ d)
    (hm : threshold22 (d + 3) ≤ m)
    (hdiv : d + 3 ∣ m + guardNumber d (sourceA35 (d + 3))) :
    ∃ S : Finset (Labelled (m + guardNumber d (sourceA35 (d + 3))) d),
      S ⊆ labelledFrames (m + guardNumber d (sourceA35 (d + 3))) d ∧
      S.card = ⌊sourceEta25 (d + 3) *
        ((m + guardNumber d (sourceA35 (d + 3)) : Nat) : ℚ) ^ d⌋₊ ∧
      (candidates m d (sourceA35 (d + 3)) S).card = candidateCount22 (d + 3) m ∧
      |((survivors m d (sourceA35 (d + 3)) (sourceA35_pos (d + 3) (by omega)) S).card : ℚ) /
        candidateCount22 (d + 3) m - 1| ≤
          deletionNumerator22 (d + 3) (sourceWidth22 (d + 3)) / m ∧
      ∀ {α : Type} (background : Fin (m + guardNumber d (sourceA35 (d + 3))) → α)
        (embed : FiniteRoles.Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ∀ first second : List α, Asym25.InEnvelope background embed source first →
            Asym25.InEnvelope background embed target second →
              ¬ first.IsRotated second := by
  have hs := size_conditions22 d m hd hm
  obtain ⟨S, hS, hcard, hsep⟩ := Asym25.exists_uniform_literal_separated hd
    (show 2 ≤ m + guardNumber d (sourceA35 (d + 3)) by omega) hs.2.2.1 hdiv
  have hcandidates := prescribed_card22 m d S hcard
  have hhalf : sourceEta25 (d + 3) *
      ((m + guardNumber d (sourceA35 (d + 3)) : Nat) : ℚ) ^ d / 2 ≤ S.card := by
    rw [hcard, guard_number_eq22]
    simpa only [Nat.add_sub_cancel, backgroundSize22] using
      selected_floor_half22 (d + 3) m (by omega) hm
  have hW8 : 512 * (d + 3) ^ 5 ≤ width d (sourceA35 (d + 3)) := by
    have h := sourceWidth28_lower5 (d + 3) (by omega)
    have hL := logFactor_pos (d + 3)
    have h1 : 512 * (d + 3) ^ 5 ≤ 1920 * (d + 3) ^ 5 * logFactor (d + 3) := by
      calc
        512 * (d + 3) ^ 5 ≤ 1920 * (d + 3) ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ 1920 * (d + 3) ^ 5 * logFactor (d + 3) := Nat.le_mul_of_pos_right _ (by omega)
    exact h1.trans h
  have hretention := retention_error22 hs.1 hd (sourceA35_pos (d + 3) (by omega))
    hs.2.2.2.1 hs.2.2.2.2.1 hW8 S hS hhalf
  rw [hcandidates] at hretention
  exact ⟨S, hS, hcard, hcandidates, hretention, hsep⟩

end CoefficientTwoPrecision.Asym22

#print axioms CoefficientTwoPrecision.Asym22.key_constant_bound
#print axioms CoefficientTwoPrecision.Asym22.proximity_loss22
#print axioms CoefficientTwoPrecision.Asym22.retention_error22
#print axioms CoefficientTwoPrecision.Asym22.exists_selection22
