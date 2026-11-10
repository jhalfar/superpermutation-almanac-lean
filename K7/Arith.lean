import LowerBounds.PArith
import K7.CapTab
import K7.ArithTab

/-!
# The knapsack of the proof of 5,898

The part (B) of `LowerBounds/PArith.lean` (5,899) for the chain caps `W5898` of `K7/CapTab.lean`: a list of
pairs `(holes, rows)` with `rows ≤ W(holes)`, weight `Σ (holes + 6)` at most 84 and value
`Σ (rows - holes - 5)` at least 50 contains one of the five profiles of 5,899 (`profile_of_family8`).  The caps
agree with those of 5,899 up to 36 holes and are larger above (they are weaker statements there), so the
certificate `Btab8` is new; its closed statements are proved by `decide +kernel`.  The statements and proofs
are those of `PArith.lean` with `Mf` replaced by `Wf` and `Bf` by `Bf8`.
-/

namespace K7

open SuperpermLowerBounds SuperpermLowerBounds.T5899

/-- The chain caps of 5,898, `x = 0..78`. -/
def Wf (x : ℕ) : ℕ := PS.capF [W5898] 0 x

/-- The certificate. -/
def Bf8 (W : ℕ) : ℕ := Btab8.getD W 0

theorem B8_closure : ∀ x < 79, ∀ W < 79, W + x + 6 ≤ 84 →
    Wf x + Bf8 W ≤ Bf8 (W + x + 6) + x + 5 := by decide +kernel

theorem B8_mono : ∀ a < 85, ∀ b < 85, a ≤ b → Bf8 a ≤ Bf8 b := by decide +kernel

theorem B8_tight : ∀ x < 79, 55 + x ≤ Wf x + Bf8 (78 - x) →
    (x = 14 ∨ x = 16 ∨ x = 26 ∨ x = 34 ∨ x = 36) := by decide +kernel

theorem B8_eq : ∀ x < 79, (x = 14 ∨ x = 16 ∨ x = 26 ∨ x = 34 ∨ x = 36) →
    Wf x + Bf8 (78 - x) = 55 + x := by decide +kernel

theorem W_vals : Wf 14 = 31 ∧ Wf 16 = 34 ∧ Wf 26 = 50 ∧ Wf 34 = 63 ∧ Wf 36 = 66 := by
  decide +kernel

/-- Every pair has `rows ≤ W holes`. -/
def lOK8 (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, p.2 ≤ Wf p.1

theorem lE_le_B8 : ∀ l : List (ℕ × ℕ), lOK8 l → lW l ≤ 84 → lE l ≤ (Bf8 (lW l) : ℤ)
  | [], _, _ => by
      rw [lE_nil]
      exact Int.natCast_nonneg _
  | p :: l, hok, hW => by
      rw [lW_cons] at hW
      have ih := lE_le_B8 l (fun q hq => hok q (List.mem_cons_of_mem _ hq)) (by omega)
      have hp := hok p List.mem_cons_self
      have hc := B8_closure p.1 (by omega) (lW l) (by omega) (by omega)
      have e : lW l + p.1 + 6 = p.1 + 6 + lW l := by omega
      rw [e] at hc
      rw [lW_cons, lE_cons]
      omega

theorem mem_tight8 {l : List (ℕ × ℕ)} (hok : lOK8 l) (hW : lW l ≤ 84) (hE : 50 ≤ lE l)
    {p : ℕ × ℕ} (hp : p ∈ l) : InS p := by
  have h1 := lW_erase hp
  have h2 := lE_erase hp
  have hok' : lOK8 (l.erase p) := fun q hq => hok q (List.mem_of_mem_erase hq)
  have h3 := lE_le_B8 _ hok' (by omega)
  have hx : p.1 < 79 := by omega
  have h4 := B8_mono (lW (l.erase p)) (by omega) (78 - p.1) (by omega) (by omega)
  have h5 := hok p hp
  have h6 := B8_tight p.1 hx (by omega)
  have h7 := B8_eq p.1 hx h6
  have hr : p.2 = Wf p.1 := by omega
  obtain ⟨m14, m16, m26, m34, m36⟩ := W_vals
  obtain ⟨x, r⟩ := p
  simp only at hr h6
  subst hr
  unfold InS
  rcases h6 with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by rw [m14])
  · exact Or.inr (Or.inl (by rw [m16]))
  · exact Or.inr (Or.inr (Or.inl (by rw [m26])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [m34]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [m36]))))

/-- **(B) for 5,898.**  A list of pairs with `rows ≤ W holes`, weight at most 84 and value at least 50
contains one of the five profiles. -/
theorem profile_of_family8 {l : List (ℕ × ℕ)} (hok : lOK8 l) (hW : lW l ≤ 84) (hE : 50 ≤ lE l) :
    2 ≤ l.count (36, 66) ∨ 2 ≤ l.count (26, 50) ∨
      (1 ≤ l.count (34, 63) ∧ 1 ≤ l.count (16, 34)) ∨
      (1 ≤ l.count (36, 66) ∧ 1 ≤ l.count (14, 31)) ∨
      (2 ≤ l.count (14, 31) ∧ 2 ≤ l.count (16, 34)) := by
  obtain ⟨h1, h2⟩ := lW_counts l (fun p hp => mem_tight8 hok hW hE hp)
  rw [h1] at hW
  rw [h2] at hE
  generalize l.count (14, 31) = a at hW hE ⊢
  generalize l.count (16, 34) = b at hW hE ⊢
  generalize l.count (26, 50) = c at hW hE ⊢
  generalize l.count (34, 63) = d at hW hE ⊢
  generalize l.count (36, 66) = f at hW hE ⊢
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 2 := by omega
  have hd : d ≤ 2 := by omega
  have hf : f ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    interval_cases f <;> omega

end K7

#print axioms K7.profile_of_family8
