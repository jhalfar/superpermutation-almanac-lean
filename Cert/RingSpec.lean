import Cert.RingT
import Cert.PStmtC
import Cert.PCut
import Cert.WSpec
import LowerBounds.PLevels

/-!
# The rule of FR from its tables, and the jumps

`rBad_eq`, `rKeep_eq`: the tables of `RingT.lean` are `PS.ringBad PRtab 77` and `PS.ringKeep Mtab PRtab 77`
(given the kernel checks `ringChk`); `ringKeepF_eq` is the closed form.  `penc`: the records with the rows
`orbT` satisfy `PEnc` (given the checks `pO`).  `ringCapT_of_psearchC`: the ring cap of FR from the kernel
search.
-/

namespace SuperpermLowerBounds
namespace Cert

open S (PermW)
open PS (PStmt noRule SeqCapLt RingCapT)

theorem ble_decide (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; cases h
    exact (decide_eq_false this).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

/-- The closed form of the inner test of `ringKeep`. -/
theorem inner_eq (pr mh mr r d H : ℕ) :
    ((List.range (mh + 1)).any fun T => pr < T && r < T && d * T ≤ r * H && T ≤ r + mr) =
      (Nat.ble (max pr r + 1) mh && Nat.ble (max pr r + 1) (r + mr) && Nat.ble (d * (max pr r + 1)) (r * H)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq]
  constructor
  · rintro ⟨T, hT, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hlo : max pr r + 1 ≤ T := by omega
    exact ⟨⟨by omega, by omega⟩, le_trans (Nat.mul_le_mul_left d hlo) h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨max pr r + 1, by omega, ⟨⟨by omega, by omega⟩, h3⟩, h2⟩

theorem ringKeepF_eq (r d : ℕ) : ringKeepF r d = PS.ringKeep T5899.Mtab T5899.PRtab 77 0 r d := by
  unfold ringKeepF PS.ringKeep
  congr 1
  funext H
  rw [inner_eq, ble_decide d H]

theorem prtab_le : ∀ d, T5899.PRtab.getD d 0 ≤ 134 := by
  intro d
  by_cases h : d < 78
  · revert d; decide
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [T5899.PRtab]; omega)]
    simp

theorem mtab_le : ∀ x, T5899.Mtab.getD x 0 ≤ 133 := by
  intro x
  by_cases h : x < 85
  · revert x; decide
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [T5899.Mtab]; omega)]
    simp

section

variable (hc : ∀ r d, r < 135 → d ≤ 77 → ringChk r d = true)
include hc

theorem rBad_eq : rBad = PS.ringBad T5899.PRtab 77 := by
  funext t r d
  by_cases hin : r < 135 ∧ d ≤ 77
  · have h := hc r d hin.1 hin.2
    unfold ringChk at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    unfold rBad PS.ringBad at h ⊢
    exact h.1
  · unfold rBad PS.ringBad
    have e : (Nat.blt r 135 && Nat.ble d 77) = false := by
      cases h1 : Nat.blt r 135 <;> cases h2 : Nat.ble d 77
      all_goals first | rfl | exact absurd ⟨by simpa [Nat.blt_eq] using h1, by simpa [Nat.ble_eq] using h2⟩ hin
    rw [e, Bool.cond_false]
    rw [ble_decide, ble_decide]
    by_cases hd : d ≤ 77
    · have hr : 135 ≤ r := by omega
      have := prtab_le d
      rw [decide_eq_true (show 2 ≤ r by omega), decide_eq_true hd,
        decide_eq_true (show T5899.PRtab.getD d 0 < r by omega)]
      rfl
    · rw [decide_eq_false hd]
      simp

theorem rKeep_eq : rKeep = PS.ringKeep T5899.Mtab T5899.PRtab 77 := by
  funext t r d
  by_cases hin : r < 135 ∧ d ≤ 77
  · have h := hc r d hin.1 hin.2
    unfold ringChk at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have e1 : rKeep t r d = rKeep 0 r d := rfl
    have e2 : PS.ringKeep T5899.Mtab T5899.PRtab 77 t r d = PS.ringKeep T5899.Mtab T5899.PRtab 77 0 r d := rfl
    rw [e1, e2, h.2, ringKeepF_eq]
  · unfold rKeep
    have e : (Nat.blt r 135 && Nat.ble d 77) = false := by
      cases h1 : Nat.blt r 135 <;> cases h2 : Nat.ble d 77
      all_goals first | rfl | exact absurd ⟨by simpa [Nat.blt_eq] using h1, by simpa [Nat.ble_eq] using h2⟩ hin
    rw [e, Bool.cond_false]
    symm
    unfold PS.ringKeep
    rw [List.any_eq_false]
    intro H hH
    simp only [List.mem_range] at hH
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, List.any_eq_true, List.mem_range, not_exists]
    intro hdH T hT h1 h2
    have := mtab_le H
    have : ¬ d ≤ 77 ∨ 135 ≤ r := by omega
    omega

end

theorem penc (F : WFacts) (ho : ∀ i, i < 5040 → pO i = true) :
    PEnc (PS.encB 7) crkT nxT wrecT orbT wsT where
  ce := cenc F
  orb_ok := fun v hv => orbB_spec _ _ _ (ho _ (encB_lt F hv))
  lt := fun v hv => encB_lt F hv
  st0 := F.st

/-- **FR from the kernel search.** -/
theorem ringCapT_of_psearchC (F : WFacts) (ho : ∀ i, i < 5040 → pO i = true)
    (hc : ∀ r d, r < 135 → d ≤ 77 → ringChk r d = true)
    (hM : SeqCapLt 7 0 (fun x => T5899.Mtab.getD x 0) (77 + 1)) {fuel : ℕ}
    (hs : psearchC noRule rBad rKeep noRule noRule false wrecT orbT wsT fuel [] ≠ none) :
    RingCapT 7 (fun x => T5899.PRtab.getD x 0) 77 := by
  have hst := PS.pstmt_of_psearchC (penc F ho) hs
  rw [rBad_eq hc, rKeep_eq hc] at hst
  exact PS.ringCap_of_stmt hM hst

end Cert
end SuperpermLowerBounds
