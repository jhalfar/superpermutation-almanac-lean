import Cert.WSpec
import Cert.RDefs
import LowerBounds.K16Rules

/-!
# The rule records of a statement F(s; lo - 1, hi), and the statement from the kernel search

A statement has rule records `rl t r d` for `t < A`, `r ≤ R`, `d < C` (49 bits: code, mask, `T1 + 2 off`,
`T2 + off`).  `codeR`, `maskR`, `cutR` read them (outside the table: code as at `R` rows or `0`, full mask,
the cut allows).  `pR t r d` is what the kernel checks about one record: the code is `KS.codeF`, the mask
has every bit whose row is not refused by the code, and where the code is at least `2`, `T1 ≤ A1`,
`T2 ≤ big` and `T2 + pk(hi) ≤ T1`.  Then `T2 ≤ A2` (`a2F_ge`), so the cut of the records allows every
continuation that the cut of the written proof allows.

`seqCap_of_searchC`: the statement F(s; lo - 1, hi) of `K16Rules.lean` from the kernel search (with Rule JS).
-/

namespace SuperpermLowerBounds
namespace Cert

open S (PermW)
open PS (TRow SeqCapLt capF)
open KS (codeF potN potS cutF a1F a2F uF segF pkF cF allowedF minLe maxLe big RuleK fK)
open K16 (KStmt16)

/-! ### Reading the records -/

/-! ### Small facts about the minima and maxima -/

theorem maxLe_le {f : ℕ → ℤ} {c : ℤ} : ∀ {n : ℕ}, (∀ x, x ≤ n → f x ≤ c) → maxLe f n ≤ c
  | 0, h => h 0 (le_refl 0)
  | n + 1, h => by
    simp only [maxLe]
    exact max_le (maxLe_le (fun x hx => h x (by omega))) (h _ (le_refl _))

theorem maxLe_mono {f : ℕ → ℤ} {n n' : ℕ} (hn : n ≤ n') : maxLe f n ≤ maxLe f n' :=
  maxLe_le (fun _ hx => KS.le_maxLe (by omega))

theorem le_minLe {p : ℕ → Bool} {f : ℕ → ℤ} {init V : ℤ} (hi : V ≤ init) :
    ∀ {n : ℕ}, (∀ x, x ≤ n → p x = true → V ≤ f x) → V ≤ minLe p f init n
  | 0, h => by
    simp only [minLe]
    split_ifs with hp
    · exact le_min hi (h 0 (le_refl 0) hp)
    · exact hi
  | n + 1, h => by
    have ih := le_minLe (p := p) (f := f) hi (n := n) (fun x hx => h x (by omega))
    simp only [minLe]
    split_ifs with hp
    · exact le_min ih (h _ (le_refl _) hp)
    · exact ih

/-- A lower bound of `A2` from `A1` and the largest peak. -/
theorem a2F_ge (P : ℕ → ℕ → ℕ) (s lo hi a b h t r d : ℕ) {V T : ℤ} (hV : V ≤ big)
    (hT : T ≤ a1F P s lo hi a b h t r d)
    (hVT : V + pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d hi ≤ T) :
    V ≤ a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h t r d := by
  unfold a2F
  refine le_minLe hV (fun x hx hp => ?_)
  have h1 : a1F P s lo hi a b h t r d ≤ cF P s a b h x := KS.minLe_le hx hp
  have h2 : pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d x ≤
      pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d hi := by
    unfold pkF
    exact maxLe_mono (by omega)
  linarith

/-! ### The records give the rule of the written proof -/

/-- `ruleK_mono` with the cut compared only where the code lets the sequence go on. -/
theorem ruleK_mono' {k : ℕ} {code code' : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut cut' : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} (hc : ∀ t r d, code t r d = code' t r d)
    (hcut : ∀ t r d m M, 2 ≤ code t r d → cut t r d m M = true → cut' t r d m M = true) :
    ∀ (rest : List TRow) (t r d : ℕ) (m M : ℤ), RuleK k code fN fS cut t r d m M rest →
      RuleK k code' fN fS cut' t r d m M rest
  | [], t, r, d, m, M, h => by
    simp only [RuleK] at h ⊢
    rw [← hc]
    exact h
  | (kd, Q) :: rest, t, r, d, m, M, h => by
    simp only [RuleK] at h ⊢
    rw [← hc]
    exact ⟨h.1, h.2.1, hcut _ _ _ _ _ (by omega) h.2.2.1, ruleK_mono' hc hcut rest _ _ _ _ _ h.2.2.2⟩

section Stmt

variable {P : ℕ → ℕ → ℕ} {s lo hi a b h : ℕ} {rl : ℕ → ℕ → ℕ → ℕ} {A R C : ℕ}

theorem rl_min (rl : ℕ → ℕ → ℕ → ℕ) (R t r d : ℕ) :
    (bif Nat.ble r R then rl t r d else rl t R d) = rl t (min r R) d := by
  cases h : Nat.ble r R
  · have : ¬ r ≤ R := fun hr => by rw [Nat.ble_eq_true_of_le hr] at h; cases h
    rw [Bool.cond_false, Nat.min_eq_right (by omega)]
  · rw [Bool.cond_true, Nat.min_eq_left (Nat.le_of_ble_eq_true h)]

theorem codeR_eq (hA : A = s + 1) (hC : C = hi + 1) (hRb : ∀ x, x ≤ hi → P s x < R)
    (hp : ∀ t r d, t < A → r ≤ R → d < C → pR P s lo hi a b h rl A R C t r d = true) (t r d : ℕ) :
    codeR rl A R C t r d = codeF P s lo hi t r d := by
  unfold codeR
  by_cases hin : t < A ∧ d < C
  · have e : (Nat.blt t A && Nat.blt d C) = true := by simp [Nat.blt_eq, hin.1, hin.2]
    rw [e, cond_true, rl_min]
    have hq := hp t (min r R) d hin.1 (Nat.min_le_right r R) hin.2
    unfold pR at hq
    simp only [Bool.and_eq_true, Nat.beq_eq] at hq
    rw [hq.1.1]
    by_cases hr : r ≤ R
    · rw [Nat.min_eq_left hr]
    · rw [Nat.min_eq_right (by omega)]
      exact (KS.codeF_big hRb (by omega)).symm
  · have e : (Nat.blt t A && Nat.blt d C) = false := by
      simp only [Bool.and_eq_false_iff, Nat.blt_eq, decide_eq_false_iff_not]
      by_contra hh
      push_neg at hh
      exact hin ⟨by simpa using hh.1, by simpa using hh.2⟩
    rw [e, cond_false]
    by_cases ht : t < A
    · exact (KS.codeF_d (by have : ¬ d < C := fun hd => hin ⟨ht, hd⟩; omega)).symm
    · exact (KS.codeF_t (by omega)).symm

theorem maskR_bit (hA : A = s + 1) (hC : C = hi + 1) (hRb : ∀ x, x ≤ hi → P s x < R)
    (hp : ∀ t r d, t < A → r ≤ R → d < C → pR P s lo hi a b h rl A R C t r d = true) :
    ∀ t r d j, j < 6 → codeR rl A R C t r (d + (5 - j)) ≠ 0 → (maskR rl A R C t r d / 2 ^ j) % 2 = 1 := by
  intro t r d j hj hne
  unfold maskR
  by_cases hin : t < A ∧ r ≤ R ∧ d < C
  · have e : (Nat.blt t A && Nat.ble r R && Nat.blt d C) = true := by
      simp [Nat.blt_eq, Nat.ble_eq, hin.1, hin.2.1, hin.2.2]
    rw [e, cond_true]
    have hq := hp t r d hin.1 hin.2.1 hin.2.2
    unfold pR at hq
    simp only [Bool.and_eq_true] at hq
    have hall := List.all_eq_true.mp hq.1.2 j (List.mem_range.mpr hj)
    simp only [Bool.or_eq_true, Nat.beq_eq] at hall
    rcases hall with h0 | h1
    · exact absurd h0 hne
    · exact h1
  · have e : (Nat.blt t A && Nat.ble r R && Nat.blt d C) = false := by
      simp only [Bool.and_eq_false_iff, Nat.blt_eq, Nat.ble_eq, decide_eq_false_iff_not]
      by_contra hh
      push_neg at hh
      exact hin ⟨by simpa using hh.1.1, by simpa using hh.1.2, by simpa using hh.2⟩
    rw [e, cond_false]
    interval_cases j <;> norm_num

theorem cutR_of_cutF (hp : ∀ t r d, t < A → r ≤ R → d < C → pR P s lo hi a b h rl A R C t r d = true)
    (t r d : ℕ) (m M : ℤ) (hc : 2 ≤ codeF P s lo hi t r d)
    (hcut : cutF (a1F P s lo hi a b h) (a2F (uF P s a b h) (segF P s a b h) P s lo hi a b h) t r d m M = true) :
    cutR rl A R C t r d m M = true := by
  unfold cutR
  by_cases hin : t < A ∧ r ≤ R ∧ d < C
  · have hq := hp t r d hin.1 hin.2.1 hin.2.2
    unfold pR at hq
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, decide_eq_true_eq] at hq
    have hq3 := hq.2
    rcases hq3 with h1 | ⟨⟨hT1, hT2⟩, hT3⟩
    · omega
    unfold cutF at hcut
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hcut
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases hcut with (h0 | h1) | h2
    · exact Or.inl (Or.inl (Or.inl h0))
    · exact Or.inl (Or.inr (le_trans hT1 h1))
    · exact Or.inr (le_trans (a2F_ge P s lo hi a b h t r d hT2 hT1 hT3) h2)
  · have e : (Nat.blt t A && Nat.ble r R && Nat.blt d C) = false := by
      simp only [Bool.and_eq_false_iff, Nat.blt_eq, Nat.ble_eq, decide_eq_false_iff_not]
      by_contra hh
      push_neg at hh
      exact hin ⟨by simpa using hh.1.1, by simpa using hh.1.2, by simpa using hh.2⟩
    rw [e]
    simp

/-- **F(s; lo - 1, hi) from the kernel search with Rule JS.** -/
theorem seqCap_of_searchC (F : WFacts) {fuel : ℕ} (hA : A = s + 1) (hC : C = hi + 1)
    (hRb : ∀ x, x ≤ hi → P s x < R)
    (hp : ∀ t r d, t < A → r ≤ R → d < C → pR P s lo hi a b h rl A R C t r d = true)
    (hlow : ∀ j, j < s → SeqCapLt 7 j (P j) (hi + 1)) (hprev : SeqCapLt 7 s (P s) lo)
    (hs : searchC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrecT true
      wsT fuel [] ≠ none) :
    SeqCapLt 7 s (P s) (hi + 1) := by
  have hst := kstmt16_of_searchC (cenc F) (maskR_bit hA hC hRb hp) hs
  refine K16.seqCap_levelK16 (a := a) (b := b) (h := h) (js := true) (by norm_num) hlow hprev ?_
  intro x rest hL hjs hrule
  exact hst x rest hL hjs (ruleK_mono' (fun t r d => (codeR_eq hA hC hRb hp t r d).symm)
    (fun t r d m M hc hcut => cutR_of_cutF hp t r d m M hc hcut) rest _ _ _ _ _ hrule)

end Stmt

end Cert
end SuperpermLowerBounds

namespace SuperpermLowerBounds
namespace Cert

theorem grid_spec {p : Nat → Nat → Bool} {C R : Nat}
    (h : allIdx (fun r => allIdx (fun d => p r d) 0 C) 0 (R + 1) = true) :
    ∀ r, r ≤ R → ∀ d, d < C → p r d = true := by
  intro r hr d hd
  have h1 := allIdx_spec (R + 1) h r (Nat.zero_le r) (by omega)
  exact allIdx_spec C h1 d (Nat.zero_le d) (by omega)

end Cert
end SuperpermLowerBounds

namespace SuperpermLowerBounds
namespace Cert

/-- No sequence has fewer than `0` holes (as `PS.seqCapLt_zero` of `PFinal.lean`). -/
theorem seqCapLt_zero' (k s : ℕ) (P : ℕ → ℕ) : PS.SeqCapLt k s P 0 :=
  fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)

end Cert
end SuperpermLowerBounds

namespace SuperpermLowerBounds
namespace Cert

theorem grid_spec' {p : Nat → Nat → Bool} {C r0 n : Nat}
    (h : allIdx (fun r => allIdx (fun d => p r d) 0 C) r0 n = true) :
    ∀ r, r0 ≤ r → r < r0 + n → ∀ d, d < C → p r d = true := by
  intro r h1 h2 d hd
  have h3 := allIdx_spec n h r h1 h2
  exact allIdx_spec C h3 d (Nat.zero_le d) (by omega)

end Cert
end SuperpermLowerBounds
