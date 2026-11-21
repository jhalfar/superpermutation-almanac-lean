import Asym33.Transfer
import Asym35.Words
import Quantitative.ActualWordBound

/-!
# Exponent 33: the actual stages and the finite word bound

Addition to Jay Pantone's quantitative development (release 9ccbe66).
This is the `Schedule` section of `SparseStageIteration`, then
`ActualStageAssembly.final_stage` and `ActualWordBound.finite_word`, with
`SparseFamilySupplier33` in place of `SparseFamilySupplier` and the
threshold `n ≥ logThreshold r`. The proofs are Jay's, with the
numerical data read from the ratio certificates.
-/

namespace CoefficientTwoPrecision.Asym33

open CoefficientTwoPrecision.Asym35

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse SparseStageIteration

section Schedule

variable (n r : ℕ) (hr : 6 ≤ r) (hn : logThreshold r ≤ n)
  (supplier : SparseFamilySupplier33 r)

include hr hn in
private theorem initial_size33 : 9 ≤ scheduleStart n r := by
  obtain ⟨_, _, hJ, _, _, hs⟩ := source_schedule_valid33 n r hr hn
  have hhalf := (hs 0 hJ).2.2.1
  simp only [sparseStart, Nat.zero_mul, Nat.add_zero] at hhalf
  have hsize := (construction_threshold_conditions33 r n hr hn).2.1
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
  nlinarith only [hhalf, hsize, hrpow]

include hr hn in
private theorem initial_stage_exist33 :
    ∃ S : BuiltStage (sparseStart n r (sourceWidth35 r) 0),
      S.p = 1 ∧ S.X = 0 ∧ S.zmass = 0 := by
  obtain ⟨S, hp, hX, hz⟩ :=
    StageState.initial (scheduleStart n r) (initial_size33 n r hr hn)
  let T := S.reindex (show scheduleStart n r = sparseStart n r (sourceWidth35 r) 0 by
    simp only [sparseStart, Nat.zero_mul, Nat.add_zero])
  refine ⟨T, ?_, ?_, ?_⟩
  · simpa only [T, BuiltStage.reindex_p] using hp
  · simpa only [T, BuiltStage.reindex_X] using hX
  · simpa only [T, BuiltStage.reindex_zmass] using hz

noncomputable def startStage33 : BuiltStage (sparseStart n r (sourceWidth35 r) 0) :=
  Classical.choose (initial_stage_exist33 n r hr hn)

private theorem startStage35_values :
    (startStage33 n r hr hn).p = 1 ∧ (startStage33 n r hr hn).X = 0 ∧
      (startStage33 n r hr hn).zmass = 0 :=
  Classical.choose_spec (initial_stage_exist33 n r hr hn)

noncomputable def selectBlock33 (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth35 r))
    (S : BuiltStage (sparseStart n r (sourceWidth35 r) i)) : SparseBlockCertificate33 r S :=
  Classical.choice (supplier _ S
    ((source_schedule_valid33 n r hr hn).2.2.2.2.2 i hi).1
    ((source_schedule_valid33 n r hr hn).2.2.2.2.2 i hi).2.1)

private theorem next_size33 (i : ℕ) :
    sparseStart n r (sourceWidth35 r) i + sourceWidth35 r =
      sparseStart n r (sourceWidth35 r) (i + 1) := by
  simp only [sparseStart, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

noncomputable def stages33 : (i : ℕ) → BuiltStage (sparseStart n r (sourceWidth35 r) i)
  | 0 => startStage33 n r hr hn
  | i + 1 =>
    let S := stages33 i
    if hi : i < sparseBlocks n r (sourceWidth35 r) then
      (advance S (source_schedule_valid33 n r hr hn).2.1
        (selectBlock33 n r hr hn supplier i hi S).family).reindex (next_size33 n r i)
    else
      (Classical.choose (empty_to S (sourceWidth35 r))).reindex (next_size33 n r i)

noncomputable def blockAt33 (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth35 r)) :
    SparseBlockCertificate33 r (stages33 n r hr hn supplier i) :=
  selectBlock33 n r hr hn supplier i hi (stages33 n r hr hn supplier i)

/-- The numerical records are read from the selected actual block families. -/
noncomputable def sourceData33 : SparseNumericalData33 n r where
  rows i := if hi : i < sparseBlocks n r (sourceWidth35 r) then
    (blockAt33 n r hr hn supplier i hi).family.sourceRows else 0
  charge i := if hi : i < sparseBlocks n r (sourceWidth35 r) then
    (blockAt33 n r hr hn supplier i hi).family.sourceCharge else 0
  circles i := if hi : i < sparseBlocks n r (sourceWidth35 r) then
    (blockAt33 n r hr hn supplier i hi).family.advancedCircles else 0
  rows_le i hi := by
    simp only [dite_eq_left hi]
    have h := (blockAt33 n r hr hn supplier i hi).family.sourceBound
    simpa only [scheduledDenominator33, List.length_append, freshExtra_length,
      List.length_singleton, (stages33 n r hr hn supplier i).size,
      Nat.sub_add_cancel (show 1 ≤ sourceWidth35 r from
        (source_schedule_valid33 n r hr hn).2.1)] using h
  density_lower i hi := by
    simp only [dite_eq_left hi, scheduledDenominator33]
    exact (blockAt33 n r hr hn supplier i hi).density_lower
  cost_ratio i hi := by
    simp only [dite_eq_left hi, scheduledDenominator33]
    exact (blockAt33 n r hr hn supplier i hi).cost_ratio
  circle_ratio i hi := by
    simp only [dite_eq_left hi]
    exact (blockAt33 n r hr hn supplier i hi).circle_ratio

theorem step_values33 (i : ℕ) (hi : i < sparseBlocks n r (sourceWidth35 r)) :
    (stages33 n r hr hn supplier (i + 1)).p =
      (stages33 n r hr hn supplier i).p * (1 - (sourceData33 n r hr hn supplier).density i) ∧
    (stages33 n r hr hn supplier (i + 1)).X =
      (stages33 n r hr hn supplier i).X + (stages33 n r hr hn supplier i).p *
        (sourceData33 n r hr hn supplier).totalRate i ∧
    (stages33 n r hr hn supplier (i + 1)).zmass =
      (stages33 n r hr hn supplier i).zmass + (stages33 n r hr hn supplier i).p *
        (sourceData33 n r hr hn supplier).circleRate i := by
  simp only [stages33, dite_eq_left hi, BuiltStage.reindex_p, BuiltStage.reindex_X,
    BuiltStage.reindex_zmass, advance_p, advance_X, advance_zmass,
    sourceData33, SparseNumericalData33.density, SparseNumericalData33.totalRate,
    SparseNumericalData33.circleRate, scheduledDenominator33, blockAt33]
  trivial

theorem stage_values33 (j : ℕ) (hj : j ≤ sparseBlocks n r (sourceWidth35 r)) :
    (stages33 n r hr hn supplier j).p = pending (sourceData33 n r hr hn supplier).density j ∧
    (stages33 n r hr hn supplier j).X = accumulatedCost
      (sourceData33 n r hr hn supplier).density (sourceData33 n r hr hn supplier).totalRate j ∧
    (stages33 n r hr hn supplier j).zmass = accumulatedCost
      (sourceData33 n r hr hn supplier).density
        (sourceData33 n r hr hn supplier).circleRate j := by
  induction j with
  | zero => exact startStage35_values n r hr hn
  | succ j ih =>
    obtain ⟨hp, hX, hz⟩ := ih (by omega)
    obtain ⟨hps, hXs, hzs⟩ := step_values33 n r hr hn supplier j (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hps, hp]
      rfl
    · rw [hXs, hX, hp]
      rfl
    · rw [hzs, hz, hp]
      rfl

end Schedule

private theorem schedule_endpoints33 (n r : ℕ) (hr : 6 ≤ r)
    (hn : logThreshold r ≤ n) :
    sparseEnd n r (sourceWidth35 r) ≤ tailStart n ∧
      tailStart n + 3 * denseBlocks n = n - 3 := by
  have hs := source_schedule_valid33 n r hr hn
  have hroom := (construction_threshold_conditions33 r n hr hn).2.2
  have h := schedule_bounds n r (sourceWidth35 r) hr hs.1 hs.2.1
    (sourceWidth35_dvd r) hroom
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

/-- `ActualStageAssembly.final_stage` for the exponent-33 supplier. -/
theorem final_stage33 (n r : ℕ) (hr : 6 ≤ r)
    (hn : logThreshold r ≤ n) (supplier : SparseFamilySupplier33 r) :
    ∃ F : BuiltStage (n - 3),
      (n : ℚ) * F.X + (n : ℚ) * F.zmass + 2 * (n : ℚ) * F.p ≤ 2 + 26 / (r : ℚ) := by
  let D := sourceData33 n r hr hn supplier
  let J := sparseBlocks n r (sourceWidth35 r)
  let S := stages33 n r hr hn supplier J
  obtain ⟨hsp, hsX, hsz⟩ := stage_values33 n r hr hn supplier J le_rfl
  have hsp' : S.p = pending D.density J := hsp
  have hsX' : S.X = accumulatedCost D.density D.totalRate J := hsX
  have hsz' : S.zmass = accumulatedCost D.density D.circleRate J := hsz
  obtain ⟨hend, hlast⟩ := schedule_endpoints33 n r hr hn
  obtain ⟨P0, hpp, hpX, hpz⟩ := empty_to S (tailStart n - sparseEnd n r (sourceWidth35 r))
  have hpad : sparseStart n r (sourceWidth35 r) J +
      (tailStart n - sparseEnd n r (sourceWidth35 r)) = tailStart n := by
    change sparseEnd n r (sourceWidth35 r) +
      (tailStart n - sparseEnd n r (sourceWidth35 r)) = tailStart n
    omega
  let P := P0.reindex hpad
  have hp : P.p = pending D.density J := by
    simpa only [P, BuiltStage.reindex_p] using hpp.trans hsp'
  have hX : P.X = accumulatedCost D.density D.totalRate J := by
    simpa only [P, BuiltStage.reindex_X] using hpX.trans hsX'
  have hz : P.zmass = accumulatedCost D.density D.circleRate J := by
    simpa only [P, BuiltStage.reindex_zmass] using hpz.trans hsz'
  have hb : 49 ≤ tailStart n := (source_schedule_valid33 n r hr hn).2.2.2.2.1
  let T := DenseStageIteration.trace n P hb (pending D.density J) hp
  let F := (DenseStageIteration.stages P hb (denseBlocks n)).reindex hlast
  have hbound := scheduled_numerical_bound33 n r hr hn D T
  refine ⟨F, ?_⟩
  have heq : (n : ℚ) * F.X + (n : ℚ) * F.zmass + 2 * (n : ℚ) * F.p =
      (n : ℚ) * accumulatedCost D.density D.totalRate J + (n : ℚ) * T.X (denseBlocks n) +
        ((n : ℚ) * (accumulatedCost D.density D.circleRate J + T.z (denseBlocks n)) +
          2 * (n : ℚ) * T.p (denseBlocks n)) := by
    simp only [F, BuiltStage.reindex_X, BuiltStage.reindex_zmass, BuiltStage.reindex_p,
      T, DenseStageIteration.trace]
    rw [hX, hz]
    ring
  rw [heq]
  exact hbound

/-- `ActualWordBound.finite_word` for the exponent-33 supplier. -/
theorem finite_word33 (n r : ℕ) (hr : 6 ≤ r)
    (hn : logThreshold r ≤ n) (supplier : SparseFamilySupplier33 r) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * F3 n + (2 * r + 26) * (n - 4).factorial := by
  obtain ⟨S, hS⟩ := final_stage33 n r hr hn supplier
  have hm : 2 ≤ n - 3 := by simpa only [S.size] using S.valid.two
  have hsize : n - 3 + 3 = n := Nat.sub_add_cancel (by omega)
  have hindex : n - 3 - 1 = n - 4 := by omega
  let Claim : ℕ → Prop := fun N =>
    ∃ w : List (Fin N), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * F3 N + (2 * r + 26) * (n - 4).factorial
  have H : Claim (n - 3 + 3) := by
    obtain ⟨w, hw, hlength⟩ := word_of_bounded_stage35 S r (by omega)
      (by simpa only [hsize] using hS)
    exact ⟨w, hw, by simpa only [hindex] using hlength⟩
  exact Eq.mp (congrArg Claim hsize) H

end CoefficientTwoPrecision.Asym33

#print axioms CoefficientTwoPrecision.Asym33.sourceData33
#print axioms CoefficientTwoPrecision.Asym33.stage_values33
#print axioms CoefficientTwoPrecision.Asym33.final_stage33
#print axioms CoefficientTwoPrecision.Asym33.finite_word33
