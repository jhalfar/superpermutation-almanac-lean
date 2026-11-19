import Cert.KComplete
import Cert.WDefs

/-!
# The word tables satisfy `CEnc`

The facts about the 5,040 words are Boolean checks (`pW`, `chkCodes`, `incB`) that the kernel evaluates
(`WCheck.lean`); this file proves that they give `CEnc (PS.encB 7) crkT nxT wrecT wsT`.
-/

namespace SuperpermLowerBounds
namespace Cert

open S (PermW WLink DoorEq code)

noncomputable section

/-! ### Checks over ranges of indices and lists -/

theorem allIdx_spec {p : Nat → Bool} {i0 : Nat} :
    ∀ n, allIdx p i0 n = true → ∀ i, i0 ≤ i → i < i0 + n → p i = true := by
  intro n
  induction n with
  | zero => intro _ i h1 h2; omega
  | succ n ih =>
    intro h i h1 h2
    have h' : (p (i0 + n) && allIdx p i0 n) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hi : i = i0 + n
    · rw [hi]; exact h'.1
    · exact ih h'.2 i h1 (by omega)

theorem chkCodes_spec : ∀ (l : List Nat) (i : Nat), chkCodes l i = true →
    ∀ j (h : j < l.length), cT (i + j) = l[j]
  | [], _, _, j, h => absurd h (Nat.not_lt_zero _)
  | c :: cs, i, hc, j, h => by
    have h' : (Nat.beq (cT i) c && chkCodes cs (i + 1)) = true := hc
    rw [Bool.and_eq_true, Nat.beq_eq] at h'
    cases j with
    | zero => simpa using h'.1
    | succ j =>
      have := chkCodes_spec cs (i + 1) h'.2 j (by simpa using h)
      rw [show i + (j + 1) = i + 1 + j by omega, this]
      rfl

theorem incB_spec : ∀ (b : Nat) (l : List Nat), incB b l = true → (∀ x ∈ l, b < x) ∧ l.Nodup
  | _, [], _ => ⟨fun _ h => (by cases h), List.nodup_nil⟩
  | b, x :: l, h => by
    have h' : (Nat.blt b x && incB x l) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨h1, h2⟩ := incB_spec x l h'.2
    refine ⟨fun y hy => ?_, List.nodup_cons.mpr ⟨fun hx => absurd (h1 x hx) (lt_irrefl x), h2⟩⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h'.1
    · exact lt_trans h'.1 (h1 y hy)

/-! ### Rows and slots -/

theorem orbB_spec : ∀ (n D x : Nat), orbB n D x = true → OrbOK crkT nxT n D x := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro D x h
    have h' : (Nat.beq (x % 1024) (crkT D) && Nat.beq (x / 1024 % 8192) D && orbB n (nxT D) (x / 8388608))
      = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    exact ⟨h'.1.1, h'.1.2, ih _ _ h'.2⟩

theorem slotsB_spec : ∀ (n x : Nat), slotsB n x = true → SlotsOK crkT nxT n x := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro x h
    have h' : (orbB 6 (x % P138 / 1024 % 8192) (x % P138) && slotsB n (x / P138)) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨orbB_spec _ _ _ h'.1, ih _ h'.2⟩

theorem anySlot_spec {n x v : Nat} (h : anySlot n x v = true) : ∃ i < n, slotD x i = v := by
  unfold anySlot at h
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp h
  exact ⟨s, List.mem_range.mp hs, Nat.eq_of_beq_eq_true he⟩

/-! ### The check of a word -/

structure WFacts : Prop where
  pw : ∀ i, i < 5040 → pW i = true
  codes : chkCodes (PS.permCodes 7 7) 0 = true
  inc : incB 0 (PS.permCodes 7 7) = true
  len : (PS.permCodes 7 7).length = 5040
  st : PS.encB 7 (List.range' 1 7) = 0
  ws : orbB 6 0 wsT = true

section Facts

variable (F : WFacts)
include F

theorem nodup_jl : (PS.permCodes 7 7).Nodup := (incB_spec 0 _ F.inc).2

theorem cT_get (j : Nat) (h : j < (PS.permCodes 7 7).length) : cT j = (PS.permCodes 7 7)[j] := by
  have := chkCodes_spec _ 0 F.codes j h
  simpa using this

/-- The index of a word, and its code. -/
theorem encB_lt {u : List ℕ} (hu : PermW 7 u) : PS.encB 7 u < 5040 := by
  rw [← F.len]
  exact List.idxOf_lt_length_of_mem (PS.mem_perm (by norm_num) hu)

theorem cT_encB {u : List ℕ} (hu : PermW 7 u) : cT (PS.encB 7 u) = code u := by
  have hm := PS.mem_perm (k := 7) (by norm_num) hu
  have hi := List.idxOf_lt_length_of_mem hm
  show cT ((PS.permCodes 7 7).idxOf (code u)) = code u
  rw [cT_get F _ hi]
  exact List.getElem_idxOf hi

theorem encB_of_cT {j : Nat} (hj : j < 5040) {u : List ℕ} (h : cT j = code u) : PS.encB 7 u = j := by
  have hj' : j < (PS.permCodes 7 7).length := by rw [F.len]; exact hj
  unfold PS.encB
  rw [← h, cT_get F _ hj']
  exact (nodup_jl F).idxOf_getElem j hj'

theorem pW_of {u : List ℕ} (hu : PermW 7 u) : pW (PS.encB 7 u) = true := F.pw _ (encB_lt F hu)

theorem cenc : CEnc (PS.encB 7) crkT nxT wrecT wsT where
  crk_inj := fun u v hu hv h => by
    have pu := pW_of F hu
    have pv := pW_of F hv
    unfold pW at pu pv
    simp only [Bool.and_eq_true, Nat.beq_eq] at pu pv
    have hcu := pu.1.1.1.1.1.1.1.2
    have hcv := pv.1.1.1.1.1.1.1.2
    rw [cT_encB F hu] at hcu
    rw [cT_encB F hv] at hcv
    have e : PS.cidxF 7 (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (code u) =
        PS.cidxF 7 (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (code v) := by rw [hcu, hcv, h]
    rw [PS.cidxF_eq, PS.cidxF_eq] at e
    exact S.isRotated_of_ci_eq (by norm_num) (by norm_num) hu hv e
  nx_eq := fun a b ha h => by
    have pa := pW_of F ha
    unfold pW at pa
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at pa
    have h1 := pa.1.1.1.1.1.1.1.1.1
    have h2 := pa.1.1.1.1.1.1.1.1.2
    rw [cT_encB F ha, PS.nxtF_code (by norm_num) (by norm_num) ha h] at h2
    exact (encB_of_cT F h1 h2).symm
  slots3 := fun u hu => by
    have p := pW_of F hu
    unfold pW at p
    simp only [Bool.and_eq_true] at p
    exact slotsB_spec _ _ p.1.1.1.1.1.2
  slots4 := fun u hu => by
    have p := pW_of F hu
    unfold pW at p
    simp only [Bool.and_eq_true] at p
    exact slotsB_spec _ _ p.1.1.1.1.2
  s3 := fun u v hu hv h => by
    have pu := pW_of F hu
    have pv := pW_of F hv
    unfold pW at pu pv
    simp only [Bool.and_eq_true] at pu pv
    have hov := PS.ovlF_of_wlink (k := 7) (d := 3) (by norm_num) (by norm_num) (by norm_num) hu hv h
    unfold PS.ovlF at hov
    have hk : PS.excF (16 ^ (7 - 1) - 1) (code u) % 16 ^ (7 - 3) = code v / 16 ^ 3 :=
      Nat.eq_of_beq_eq_true hov
    have hmem := pv.1.2
    rw [cT_encB F hv, ← hk, ← cT_encB F hu] at hmem
    have hall := List.all_eq_true.mp pu.1.1.1.2 _ (List.elem_iff.mp hmem)
    exact anySlot_spec hall
  s4 := fun u v hu hv h => by
    have pu := pW_of F hu
    have pv := pW_of F hv
    unfold pW at pu pv
    simp only [Bool.and_eq_true] at pu pv
    have hov := PS.ovlF_of_wlink (k := 7) (d := 4) (by norm_num) (by norm_num) (by norm_num) hu hv h
    unfold PS.ovlF at hov
    have hk : PS.excF (16 ^ (7 - 1) - 1) (code u) % 16 ^ (7 - 4) = code v / 16 ^ 4 :=
      Nat.eq_of_beq_eq_true hov
    have hmem := pv.2
    rw [cT_encB F hv, ← hk, ← cT_encB F hu] at hmem
    have hall := List.all_eq_true.mp pu.1.1.2 _ (List.elem_iff.mp hmem)
    exact anySlot_spec hall
  cq := fun u hu => by
    have p := pW_of F hu
    unfold pW at p
    simp only [Bool.and_eq_true, Nat.beq_eq] at p
    exact p.1.1.1.1.1.1.2
  ws := by
    rw [F.st]
    exact orbB_spec _ _ _ F.ws

end Facts

end

end Cert
end SuperpermLowerBounds
