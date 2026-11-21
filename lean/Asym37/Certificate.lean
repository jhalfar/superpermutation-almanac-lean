import Asym37.Retention
import Asym37.Transfer
import Quantitative.SparseFamilyConstruction

/-!
# Exponent 37: construction of the ratio-based sparse-family supplier

Addition to Jay Pantone's quantitative development (release 9ccbe66).
This is `StageSourceCertificate.from_contours` and
`SparseFamilyConstruction.supplier` with the new threshold, the new
retention bound (`Retention.exists_selection37`) and the ratio estimates
(`CountRatio.estimates37`). The geometric construction (labels, packing,
global family, canonical relabelling) is Jay's, used unchanged.
-/

namespace CoefficientTwoPrecision.Asym37

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse SourceFamilyAdapter SourceAdvancement
open CandidateFactorization StageSourceCertificate

theorem from_contours37 {m : Nat} (r : Nat) (hr : 6 ≤ r) (S : BuiltStage m)
    (hm : threshold37 r ≤ m)
    (F : List (SourceContour (controls S (sourceWidth r) ++ S.A0) (m + sourceWidth r - 2)))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove (controls S (sourceWidth r)) S.A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base))
    (hretention : |(F.length : ℚ) / candidateCount r m - 1| ≤
      deletionNumerator37 r (sourceWidth r) / m)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * backgroundSize r m)| ≤
      10 * (r : ℚ) ^ 2 * (52 * r ^ 4 * sourceWidth r ^ 2 : Nat) * backgroundSize r m)
    (hcharge : ∀ C ∈ F,
      (C.rows.map Row.charge).sum = 2 * (r - 1) * backgroundSize r m)
    (hg : ∀ C ∈ F, portGcd C.rows (m + sourceWidth r - 2) ≤ r - 1) :
    Nonempty (SparseBlockCertificate37 r S) := by
  have hW := ConstructionSize.width_positive r hr
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ := alphabet_data S (sourceWidth r) hW
  have hsize : (controls S (sourceWidth r) ++ S.A0).length = m + sourceWidth r - 2 + 2 := by
    rw [List.length_append, hwidth, S.size]
    have hlarge := ConstructionSize.width_linear r hr
    omega
  have hthree : 3 ≤ m + sourceWidth r - 2 + 2 := by
    have hlarge := ConstructionSize.width_linear r hr
    omega
  have hm0 := (threshold_conditions37 r m hr hm).1
  have hold : 0 < S.A0.length := by rwa [S.size]
  have hold9 : 9 ∉ S.A0 := fun h => h9 (List.mem_append_right _ h)
  let K : Block S (sourceWidth r) := CanonicalSourceFamily.widthBlock
    S.A0 (controls S (sourceWidth r)) (next m (sourceWidth r)) (m + sourceWidth r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  have hcounts := CanonicalSourceFamily.widthBlock_counts
    S.A0 (controls S (sourceWidth r)) (next m (sourceWidth r)) (m + sourceWidth r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  change K.sourceRows = _ ∧ K.sourceCharge = _ ∧ K.advancedCircles = _ at hcounts
  have hc : K.advancedCircles = (circles F).length := hcounts.2.2.trans (circles_length F).symm
  obtain ⟨hdensity, hcost, hratio⟩ :=
    estimates37 F r m (52 * r ^ 4 * sourceWidth r ^ 2) hr hm
      (Nat.le_refl _) hretention hperturb hcharge hg
  refine ⟨{
    family := K
    density_lower := ?_
    cost_ratio := ?_
    circle_ratio := ?_ }⟩
  · simpa only [hcounts.1] using hdensity
  · rw [hcounts.2.1, hc, hcounts.1]
    exact hcost
  · simpa only [hcounts.2.1, hc] using hratio

theorem supplier37 (r : Nat) (hr : 6 ≤ r) : SparseFamilySupplier37 r := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d : Nat, r = d + 3 := ⟨r - 3, by omega⟩
  have hd : 3 ≤ d := by omega
  intro m stage hdiv hm
  have hs := size_conditions37 d m hd hm
  have hA := sourceA_pos (d + 3) hr
  letI : NeZero (m + GuardCatalogue.guardNumber d (sourceA (d + 3))) := ⟨by omega⟩
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ :=
    alphabet_data stage (sourceWidth (d + 3)) (ConstructionSize.width_positive (d + 3) hr)
  have hwidthGrid : (controls stage (sourceWidth (d + 3))).length =
      (d + 3) * ((d + 3) * sourceA (d + 3)) :=
    hwidth.trans (SourceSelection.control_width d)
  obtain ⟨old, physical, ho, hl, hcross, hword, hcontrol, hold⟩ :=
    GridAlphabet.exists_labels (controls stage (sourceWidth (d + 3))) stage.A0
      hwidthGrid stage.size hnd
  obtain ⟨S, hS, hcard, hraw, hretention, hpacking⟩ := exists_selection37 d m hd hm
  let rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3) :=
    Fintype.equivFinOfCardEq (by simp [FiniteRoles.Role])
  have holdPos : 0 < stage.A0.length := by rw [stage.size]; exact hs.1
  have hfamily := GlobalSourceFamily.exists_family hA old ho physical hl hcross
    (controls stage (sourceWidth (d + 3))) stage.A0 rowIndex S hs.1 hd hs.2.1
    hs.2.2.2.1 (SourceSelection.background_divisible d m hd hdiv)
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 holdPos hnd h9 hword hold hcontrol hS
    (fun bg embed hb he hc => hpacking bg embed hb he hc)
  rw [SourceSelection.contour_height d m hd] at hfamily
  obtain ⟨F, hlength, hinsertion, hdistinct, hcounts⟩ := hfamily
  have hM : m + GuardCatalogue.guardNumber d (sourceA (d + 3)) = backgroundSize (d + 3) m := by
    rw [CandidateSpace.guard_number_eq]
    rfl
  have hK := CatalogueBounds.occurrence_bound d (sourceA (d + 3)) hA
  change PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) ≤
    52 * (d + 3) ^ 4 * sourceWidth (d + 3) ^ 2 at hK
  apply from_contours37 (d + 3) hr stage hm F hinsertion hdistinct
  · rw [hlength]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hretention
  · intro C hC
    have herror := (hcounts C hC).2.2
    have hbound :
        ((10 * (d + 3) ^ 2 * PrimaryCatalogue.occurrenceBound d (sourceA (d + 3)) *
          (m + GuardCatalogue.guardNumber d (sourceA (d + 3))) : Nat) : ℚ) ≤
        ((10 * (d + 3) ^ 2 * (52 * (d + 3) ^ 4 * sourceWidth (d + 3) ^ 2) *
          (m + GuardCatalogue.guardNumber d (sourceA (d + 3))) : Nat) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (m + GuardCatalogue.guardNumber d (sourceA (d + 3)))
        (Nat.mul_le_mul_left (10 * (d + 3) ^ 2) hK)
    have hfinal := herror.trans hbound
    rw [hM] at hfinal
    have hbaseline :
        (((backgroundSize (d + 3) m) *
          ((d + 3 - 2) * backgroundSize (d + 3) m + (d + 3) * (d + 3 - 1) + 1) : Nat) : ℚ) =
        (((d + 3 : Nat) : ℚ) - 2) * (backgroundSize (d + 3) m : ℚ) ^ 2 +
          (((d + 3 : Nat) : ℚ) * (((d + 3 : Nat) : ℚ) - 1) + 1) * backgroundSize (d + 3) m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (show 2 ≤ d + 3 by omega),
        Nat.cast_sub (show 1 ≤ d + 3 by omega), Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hbaseline] at hfinal
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal
  · intro C hC
    simpa only [hM] using (hcounts C hC).1
  · intro C hC
    exact (hcounts C hC).2.1

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.from_contours37
#print axioms CoefficientTwoPrecision.Asym37.supplier37
