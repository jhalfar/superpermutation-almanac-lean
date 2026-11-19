import Cert.KEngineN
import Cert.KComplete
import Cert.RDefs

/-!
# The engine with natural potentials is the engine of `KEngine.lean`

`goNat_eq`: for the rule records of a statement (`codeR`, `maskR`, `cutR`) and the potentials `KS.potN`,
`KS.potS`, `goNat` with shifted potentials `m`, `M` is `goC` with the potentials `m - off`, `M - off`, as long
as the shift is larger than `b d + 2 h t + h` for every `t < A`, `d < C` (`hoff`).  `goN_eq`, `searchN_eq`: the
forms that the evaluated lemmas use.
-/

namespace SuperpermLowerBounds
namespace Cert

open KS (potN potS)

theorem nmin_cast (x y : ℕ) : ((nmin x y : ℕ) : ℤ) - offN = min ((x : ℤ) - offN) ((y : ℤ) - offN) := by
  unfold nmin
  cases h : Nat.ble x y
  · have : ¬ x ≤ y := fun hxy => by rw [Nat.ble_eq_true_of_le hxy] at h; cases h
    simp only [Bool.cond_false]
    rw [min_eq_right (by omega)]
  · have := Nat.le_of_ble_eq_true h
    simp only [Bool.cond_true]
    rw [min_eq_left (by omega)]

theorem nmax_cast (x y : ℕ) : ((nmax x y : ℕ) : ℤ) - offN = max ((x : ℤ) - offN) ((y : ℤ) - offN) := by
  unfold nmax
  cases h : Nat.ble x y
  · have : ¬ x ≤ y := fun hxy => by rw [Nat.ble_eq_true_of_le hxy] at h; cases h
    simp only [Bool.cond_false]
    rw [max_eq_left (by omega)]
  · have := Nat.le_of_ble_eq_true h
    simp only [Bool.cond_true]
    rw [max_eq_right (by omega)]

theorem ble_dec (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; cases h
    exact (decide_eq_false this).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

theorem cutNat_eq (rl : ℕ → ℕ → ℕ → ℕ) (A R C t r d m M : ℕ) :
    cutNat rl A R C t r d m M = cutR rl A R C t r d ((m : ℤ) - offN) ((M : ℤ) - offN) := by
  unfold cutNat cutR t1R t2R
  rw [ble_dec offN m, ble_dec (rl t r d / 512 % 1048576) (M + m), ble_dec (rl t r d / 536870912 % 1048576) m]
  have e1 : decide (offN ≤ m) = decide ((0 : ℤ) ≤ (m : ℤ) - offN) :=
    decide_eq_decide.mpr (by simp only [offN]; omega)
  have e2 : decide (rl t r d / 512 % 1048576 ≤ M + m) =
      decide (((rl t r d / 512 % 1048576 : ℕ) : ℤ) - 524288 ≤ ((M : ℤ) - offN) + ((m : ℤ) - offN)) :=
    decide_eq_decide.mpr (by simp only [offN]; omega)
  have e3 : decide (rl t r d / 536870912 % 1048576 ≤ m) =
      decide (((rl t r d / 536870912 % 1048576 : ℕ) : ℤ) - 262144 ≤ (m : ℤ) - offN) :=
    decide_eq_decide.mpr (by simp only [offN]; omega)
  rw [e1, e2, e3]

theorem potN_cast {a b h t r d : ℕ} (hb : b * d + 2 * h * t ≤ offN) :
    ((offN + a * r - (b * d + 2 * h * t) : ℕ) : ℤ) - offN = potN a b h t r d := by
  unfold potN
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem potS_cast {a b h t r d : ℕ} (hb : b * d + 2 * h * t + h ≤ offN) :
    ((offN + a * r - (b * d + 2 * h * t + h) : ℕ) : ℤ) - offN = potS a b h t r d := by
  unfold potS potN
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem codeR_in {rl : ℕ → ℕ → ℕ → ℕ} {A R C t r d : ℕ} (h : codeR rl A R C t r d ≠ 0) : t < A ∧ d < C := by
  unfold codeR at h
  by_contra hn
  have e : (Nat.blt t A && Nat.blt d C) = false := by
    cases h1 : Nat.blt t A <;> cases h2 : Nat.blt d C
    all_goals first | rfl | exact absurd ⟨by simpa [Nat.blt_eq] using h1, by simpa [Nat.blt_eq] using h2⟩ hn
  rw [e] at h
  exact h rfl

section

variable (rl : ℕ → ℕ → ℕ → ℕ) (A R C a b h : ℕ) (wrec : ℕ → ℕ) (js : Bool)

set_option maxHeartbeats 4000000 in
/-- **The engine with natural potentials is the engine.** -/
theorem goNat_eq (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) :
    ∀ (f t r d m M q B : ℕ) (L : List CS),
      goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f t r d m M q B L =
        goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js f t r d
          ((m : ℤ) - offN) ((M : ℤ) - offN) q B L := by
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro t r d m M q B L
    rw [goC_succ]
    have hbody : ∀ L', bodyNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js
        (goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f) t r d m M q B L' =
        bodyC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js
          (goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js f)
          t r d ((m : ℤ) - offN) ((M : ℤ) - offN) q B L' := by
      intro L'
      unfold bodyNat bodyC
      by_cases hc : codeR rl A R C t r d = 0
      · rw [hc]
        simp only [Nat.beq_refl, Bool.cond_true]
      · obtain ⟨ht, hd⟩ := codeR_in hc
        have h1 := hoff t d ht hd
        have eN := potN_cast (a := a) (r := r) (show b * d + 2 * h * t ≤ offN by omega)
        have eS := potS_cast (a := a) (r := r) h1
        have hN : ∀ n e B' L'', goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f t (r + 1) (d + n)
            (nmin m (offN + a * r - (b * d + 2 * h * t))) (nmax M (offN + a * r - (b * d + 2 * h * t))) e B' L'' =
            goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js f t (r + 1)
              (d + n) (min ((m : ℤ) - offN) (potN a b h t r d)) (max ((M : ℤ) - offN) (potN a b h t r d)) e B' L'' := by
          intro n e B' L''
          rw [ih, nmin_cast, nmax_cast, eN]
        have hS : ∀ n e B' L'', goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f (t + 1) (r + 1)
            (d + n) (nmin m (offN + a * r - (b * d + 2 * h * t + h)))
            (nmax M (offN + a * r - (b * d + 2 * h * t + h))) e B' L'' =
            goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js f (t + 1)
              (r + 1) (d + n) (min ((m : ℤ) - offN) (potS a b h t r d)) (max ((M : ℤ) - offN) (potS a b h t r d))
              e B' L'' := by
          intro n e B' L''
          rw [ih, nmin_cast, nmax_cast, eS]
        have cN : cutNat rl A R C t r d (nmin m (offN + a * r - (b * d + 2 * h * t)))
            (nmax M (offN + a * r - (b * d + 2 * h * t))) =
            cutR rl A R C t r d (min ((m : ℤ) - offN) (potN a b h t r d)) (max ((M : ℤ) - offN) (potN a b h t r d)) := by
          rw [cutNat_eq, nmin_cast, nmax_cast, eN]
        have cS : cutNat rl A R C t r d (nmin m (offN + a * r - (b * d + 2 * h * t + h)))
            (nmax M (offN + a * r - (b * d + 2 * h * t + h))) =
            cutR rl A R C t r d (min ((m : ℤ) - offN) (potS a b h t r d)) (max ((M : ℤ) - offN) (potS a b h t r d)) := by
          rw [cutNat_eq, nmin_cast, nmax_cast, eS]
        rw [cN, cS, funext fun n => funext fun e => funext fun B' => funext fun L'' => hN n e B' L'',
          funext fun n => funext fun e => funext fun B' => funext fun L'' => hS n e B' L'']
    show nodeNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js
        (goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f) (f + 1) t r d m M q B L = _
    cases L with
    | nil => exact hbody []
    | cons s L' =>
      show (bif csEq s (f + 1) t r d ((m : ℤ) - offN) ((M : ℤ) - offN) q B then some L'
        else bodyNat _ _ _ _ _ _ _ _ _ _ _ _ t r d m M q B (s :: L')) = _
      rw [hbody]
      rfl

theorem goN_eq (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) (f t r d : ℕ) (m M : ℤ) (q B : ℕ)
    (L : List CS) (hm : -(offN : ℤ) ≤ m) (hM : -(offN : ℤ) ≤ M) :
    goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f t r d m M q B L =
      goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js f t r d m M q B L := by
  unfold goN
  rw [goNat_eq rl A R C a b h wrec js hoff]
  congr 1
  · rw [Int.toNat_of_nonneg (by omega)]; ring
  · rw [Int.toNat_of_nonneg (by omega)]; ring

theorem searchN_eq (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) (ws fuel : ℕ) (L : List CS) :
    searchN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js ws fuel L =
      searchC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js ws fuel L := by
  unfold searchN searchC
  have e : (fun n e B L' => goNat (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js fuel 0 1 n offN offN e B L')
      = (fun n e B L' => goC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js fuel
          0 1 n 0 0 e B L') := by
    funext n e B L'
    rw [goNat_eq rl A R C a b h wrec js hoff]
    simp
  rw [e]

end

end Cert
end SuperpermLowerBounds
