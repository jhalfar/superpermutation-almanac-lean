import Asym28.Retention
import Asym28.Transfer
import Asym28.TD.GlobalSourceFamily
import Quantitative.StageSourceCertificate

/-!
# Exponent 28: construction of the ratio-based sparse-family supplier

Addition to Jay Pantone's quantitative development (release 9ccbe66).
This is `StageSourceCertificate.from_contours` and
`SparseFamilyConstruction.supplier` with the new threshold, the new
retention bound (`Retention.exists_selection28`) and the ratio estimates
(`CountRatio.estimates28`). The geometric construction (labels, packing,
global family, canonical relabelling) is Jay's, used unchanged.
-/

namespace CoefficientTwoPrecision.Asym28

open CoefficientTwoPrecision.Asym35

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse SourceFamilyAdapter SourceAdvancement
open CandidateFactorization StageSourceCertificate

theorem from_contours28 {m : Nat} (r : Nat) (hr : 6 ≤ r) (S : BuiltStage m)
    (hm : threshold28 r ≤ m)
    (F : List (SourceContour (controls S (sourceWidth28 r) ++ S.A0) (m + sourceWidth28 r - 2)))
    (hinsertion : ∀ row ∈ sourceRows F, InsertionAbove (controls S (sourceWidth28 r)) S.A0 row.base)
    (hdistinct : (sourceRows F).Pairwise (fun row other => ¬ CyclicEq row.base other.base))
    (hretention : |(F.length : ℚ) / candidateCount28 r m - 1| ≤
      deletionNumerator28 r (sourceWidth28 r) / m)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (backgroundSize28 r m : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * backgroundSize28 r m)| ≤
      10 * (r : ℚ) ^ 2 * (52 * r ^ 5 * sourceWidth28 r ^ 2 : Nat) * backgroundSize28 r m)
    (hcharge : ∀ C ∈ F,
      (C.rows.map Row.charge).sum = 2 * (r - 1) * backgroundSize28 r m)
    (hg : ∀ C ∈ F, portGcd C.rows (m + sourceWidth28 r - 2) ≤ r - 1) :
    Nonempty (SparseBlockCertificate28 r S) := by
  have hW := width_positive28 r hr
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ := alphabet_data S (sourceWidth28 r) hW
  have hsize : (controls S (sourceWidth28 r) ++ S.A0).length = m + sourceWidth28 r - 2 + 2 := by
    rw [List.length_append, hwidth, S.size]
    have hlarge := width_linear28 r hr
    omega
  have hthree : 3 ≤ m + sourceWidth28 r - 2 + 2 := by
    have hlarge := width_linear28 r hr
    omega
  have hm0 := (threshold_conditions28 r m hr hm).1
  have hold : 0 < S.A0.length := by rwa [S.size]
  have hold9 : 9 ∉ S.A0 := fun h => h9 (List.mem_append_right _ h)
  let K : Block S (sourceWidth28 r) := CanonicalSourceFamily.widthBlock
    S.A0 (controls S (sourceWidth28 r)) (next m (sourceWidth28 r)) (m + sourceWidth28 r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  have hcounts := CanonicalSourceFamily.widthBlock_counts
    S.A0 (controls S (sourceWidth28 r)) (next m (sourceWidth28 r)) (m + sourceWidth28 r - 2)
    hold hnd hold9 hsize hthree hnext hnext9 h10 F hinsertion hdistinct
  change K.sourceRows = _ ∧ K.sourceCharge = _ ∧ K.advancedCircles = _ at hcounts
  have hc : K.advancedCircles = (circles F).length := hcounts.2.2.trans (circles_length F).symm
  obtain ⟨hdensity, hcost, hratio⟩ :=
    estimates28 F r m (52 * r ^ 5 * sourceWidth28 r ^ 2) hr hm
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

theorem supplier28 (r : Nat) (hr : 6 ≤ r) : SparseFamilySupplier28 r := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d : Nat, r = d + 3 := ⟨r - 3, by omega⟩
  have hd : 3 ≤ d := by omega
  intro m stage hdiv hm
  have hs := size_conditions28 d m hd hm
  have hA := sourceA35_pos (d + 3) hr
  letI : NeZero (m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3))) := ⟨by omega⟩
  obtain ⟨hwidth, hnd, h9, h10, hnext, hnext9⟩ :=
    alphabet_data stage (sourceWidth28 (d + 3)) (width_positive28 (d + 3) hr)
  have hwidthGrid : (controls stage (sourceWidth28 (d + 3))).length =
      (d + 3) * TD.tdQ (d + 3) (sourceA35 (d + 3)) :=
    hwidth.trans (control_width28 d)
  obtain ⟨old, physical, ho, hl, hcross, hword, hcontrol, hold⟩ :=
    TD.GridAlphabet.exists_labels (controls stage (sourceWidth28 (d + 3))) stage.A0
      hwidthGrid stage.size hnd
  obtain ⟨S, hS, hcard, hraw, hretention, hpacking⟩ := exists_selection28 d m hd hm
  let rowIndex : FiniteRoles.Role (d + 2) ≃ Fin (d + 3) :=
    Fintype.equivFinOfCardEq (by simp [FiniteRoles.Role])
  have holdPos : 0 < stage.A0.length := by rw [stage.size]; exact hs.1
  have hfamily := TD.GlobalSourceFamily.exists_family hA old ho physical hl hcross
    (controls stage (sourceWidth28 (d + 3))) stage.A0 rowIndex S hs.1 hd hs.2.1
    hs.2.2.2.1 (background_divisible28 d m hd hdiv)
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 holdPos hnd h9 hword hold hcontrol hS
    (fun bg embed hb he hc => hpacking bg embed hb he hc)
  rw [contour_height28 d m hd] at hfamily
  obtain ⟨F, hlength, hinsertion, hdistinct, hcounts⟩ := hfamily
  have hM : m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)) = backgroundSize28 (d + 3) m := by
    rw [guard_number_eq28]
    rfl
  have hK := TD.CatalogueBounds.occurrence_bound d (sourceA35 (d + 3)) hA
  change TD.PrimaryCatalogue.occurrenceBound d (sourceA35 (d + 3)) ≤
    52 * (d + 3) ^ 5 * sourceWidth28 (d + 3) ^ 2 at hK
  apply from_contours28 (d + 3) hr stage hm F hinsertion hdistinct
  · rw [hlength]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hretention
  · intro C hC
    have herror := (hcounts C hC).2.2
    have hbound :
        ((10 * (d + 3) ^ 2 * TD.PrimaryCatalogue.occurrenceBound d (sourceA35 (d + 3)) *
          (m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3))) : Nat) : ℚ) ≤
        ((10 * (d + 3) ^ 2 * (52 * (d + 3) ^ 5 * sourceWidth28 (d + 3) ^ 2) *
          (m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3))) : Nat) : ℚ) := by
      exact_mod_cast Nat.mul_le_mul_right (m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)))
        (Nat.mul_le_mul_left (10 * (d + 3) ^ 2) hK)
    have hfinal := herror.trans hbound
    rw [hM] at hfinal
    have hbaseline :
        (((backgroundSize28 (d + 3) m) *
          ((d + 3 - 2) * backgroundSize28 (d + 3) m + (d + 3) * (d + 3 - 1) + 1) : Nat) : ℚ) =
        (((d + 3 : Nat) : ℚ) - 2) * (backgroundSize28 (d + 3) m : ℚ) ^ 2 +
          (((d + 3 : Nat) : ℚ) * (((d + 3 : Nat) : ℚ) - 1) + 1) * backgroundSize28 (d + 3) m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub (show 2 ≤ d + 3 by omega),
        Nat.cast_sub (show 1 ≤ d + 3 by omega), Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hbaseline] at hfinal
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hfinal
  · intro C hC
    simpa only [hM] using (hcounts C hC).1
  · intro C hC
    exact (hcounts C hC).2.1

end CoefficientTwoPrecision.Asym28

#print axioms CoefficientTwoPrecision.Asym28.from_contours28
#print axioms CoefficientTwoPrecision.Asym28.supplier28
