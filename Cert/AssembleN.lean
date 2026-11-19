import Cert.Assemble
import Cert.KEquiv
import Cert.OkN

/-!
# Putting together lemmas evaluated by the engine with natural potentials

As `Assemble.lean`, for lemmas `(goN … L).isSome = true` and `(searchN … L).isSome = true`: `goN_eq` and
`searchN_eq` turn them into the lemmas of `goC`, `searchC`.  `hoff` is the bound of the shift for the
statement, `hm`, `hM` that the potentials of the prefix are above `-off` (both by `decide`).
-/

namespace SuperpermLowerBounds
namespace Cert

open KS (potN potS)

section

variable {rl : ℕ → ℕ → ℕ → ℕ} {A R C a b h : ℕ} {wrec : ℕ → ℕ} {js : Bool}

theorem fullN_of_isSome (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {f t r d : ℕ} {m M : ℤ}
    {q B : ℕ} (hm : -(offN : ℤ) ≤ m) (hM : -(offN : ℤ) ≤ M)
    (hs : (goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f t r d m M q B []).isSome = true) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js
      ⟨f, t, r, d, m, M, q, B⟩ := by
  rw [goN_eq rl A R C a b h wrec js hoff f t r d m M q B [] hm hM] at hs
  exact full_of_isSome hs

theorem fullN_of_cut (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {f t r d : ℕ} {m M : ℤ}
    {q B : ℕ} {L : List CS} (hm : -(offN : ℤ) ≤ m) (hM : -(offN : ℤ) ≤ M)
    (hs : (goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js f t r d m M q B L).isSome = true)
    (hL : ∀ s ∈ L, FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js
      ⟨f, t, r, d, m, M, q, B⟩ := by
  rw [goN_eq rl A R C a b h wrec js hoff f t r d m M q B L hm hM] at hs
  exact full_of_cut hs hL

theorem fullS_of_isSome (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {s : CS}
    (hm : -(offN : ℤ) ≤ s.m) (hM : -(offN : ℤ) ≤ s.M)
    (hs : (goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js s.f s.t s.r s.d s.m s.M s.q s.B []).isSome
      = true) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s :=
  fullN_of_isSome hoff hm hM hs

theorem fullS_of_cut (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {s : CS} {L : List CS}
    (hm : -(offN : ℤ) ≤ s.m) (hM : -(offN : ℤ) ≤ s.M)
    (hs : (goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js s.f s.t s.r s.d s.m s.M s.q s.B L).isSome
      = true)
    (hL : ∀ x ∈ L, FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js x) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s :=
  fullN_of_cut hoff hm hM hs hL

theorem searchN_ok (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {ws fuel : ℕ} {L : List CS}
    (hs : (searchN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js ws fuel L).isSome = true)
    (hL : ∀ s ∈ L, FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s) :
    searchC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js ws fuel [] ≠ none := by
  rw [searchN_eq rl A R C a b h wrec js hoff] at hs
  exact searchC_ok hs hL

end

/-! The lemmas for the statements `okN` of `OkN.lean`. -/

section

variable {rl : ℕ → ℕ → ℕ → ℕ} {A R C a b h : ℕ} {wrec : ℕ → ℕ} {js : Bool}

theorem fullS_of_ok (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {s : CS}
    (hk : okN rl A R C a b h wrec js s [] = true) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s := by
  unfold okN at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact fullS_of_isSome hoff hk.1.1 hk.1.2 hk.2

theorem fullS_of_cut_ok (hoff : ∀ t d, t < A → d < C → b * d + 2 * h * t + h ≤ offN) {s : CS} {L : List CS}
    (hk : okN rl A R C a b h wrec js s L = true)
    (hL : ∀ x ∈ L, FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js x) :
    FullC (codeR rl A R C) (maskR rl A R C) (potN a b h) (potS a b h) (cutR rl A R C) wrec js s := by
  unfold okN at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact fullS_of_cut hoff hk.1.1 hk.1.2 hk.2 hL

end

end Cert
end SuperpermLowerBounds
