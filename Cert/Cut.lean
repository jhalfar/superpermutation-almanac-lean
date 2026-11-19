import Cert.KComplete

/-!
# Skipped prefixes

A search with a list `L` of prefixes skips every prefix that is the head of the list when it is reached.
`goC_cut`: if the search with `L` does not find, and the whole search below every prefix of `L` does not find,
then the whole search does not find.  So a search can be cut into lemmas: one for the tree above a list of
prefixes, one for each prefix of the list (each of which may again be cut).
-/

namespace SuperpermLowerBounds
namespace Cert

/-- A call `c` that does not find with a list whose prefixes all satisfy `P` does not find with the empty
list. -/
def CutOK (P : CS → Prop) (c : List CS → Res) : Prop :=
  ∀ L L', c L = some L' → (∀ s ∈ L, P s) → c [] ≠ none

theorem cutOK_some (P : CS → Prop) : CutOK P (fun L => some L) := fun _ _ _ _ h => by cases h

theorem cutOK_cond (P : CS → Prop) (b : Bool) {c1 c2 : List CS → Res} (h1 : CutOK P c1)
    (h2 : CutOK P c2) : CutOK P (fun L => bif b then c1 L else c2 L) := by
  cases b
  · exact h2
  · exact h1

theorem cutOK_none (P : CS → Prop) : CutOK P (fun _ => none) := fun _ _ h => by cases h

theorem cutOK_bnd (P : CS → Prop) {c1 : List CS → Res} {c2 : List CS → Res} (h1 : CutOK P c1)
    (hs : ∀ L, SufR L (c1 L)) (h2 : CutOK P c2) : CutOK P (fun L => bnd (c1 L) c2) := by
  intro L L' h hP
  change bnd (c1 L) c2 = some L' at h
  show bnd (c1 []) c2 ≠ none
  cases e1 : c1 L with
  | none =>
    rw [e1] at h
    cases h
  | some L1 =>
    rw [e1, bnd_some] at h
    have hsuf := hs L L1 e1
    have hP1 : ∀ s ∈ L1, P s := fun s hs' => hP s (hsuf.subset hs')
    have hn1 := h1 L L1 e1 hP
    cases e0 : c1 [] with
    | none => exact absurd e0 hn1
    | some L0 =>
      have hnil : L0 = [] := nil_of_sufR (hs []) e0
      subst hnil
      rw [bnd_some]
      exact h2 L1 L' h hP1

theorem walkC_cut (P : CS → Prop) (G : Nat → Nat → Nat → List CS → Res)
    (hGs : ∀ n e B L, SufR L (G n e B L)) (hG : ∀ n e B, CutOK P (G n e B)) :
    ∀ (n mk x B : Nat), CutOK P (walkC G n mk x B) := by
  intro n
  induction n with
  | zero => intro mk x B; exact cutOK_some P
  | succ n ih =>
    intro mk x B
    have e : walkC G (n + 1) mk x B = fun L =>
        (bif Nat.beq mk 0 then some L
        else bif Nat.testBit B (x % 1024) then some L
        else bnd (bif Nat.beq (mk % 2) 1 then G n (x / 1024 % 8192) (B ||| 2 ^ (x % 1024)) L else some L)
          (fun L1 => walkC G n (mk / 2) (x / 8388608) (B ||| 2 ^ (x % 1024)) L1)) := rfl
    rw [e]
    refine cutOK_cond P _ (cutOK_some P) (cutOK_cond P _ (cutOK_some P) ?_)
    refine cutOK_bnd P (c1 := fun L => bif Nat.beq (mk % 2) 1 then
        G n (x / 1024 % 8192) (B ||| 2 ^ (x % 1024)) L else some L)
      (cutOK_cond P _ (hG _ _ _) (cutOK_some P)) (fun L => sufR_cond _ (hGs _ _ _ _) (sufR_some L))
      (ih _ _ _)

theorem succC_cut (P : CS → Prop) (G : Nat → Nat → Nat → List CS → Res)
    (hGs : ∀ n e B L, SufR L (G n e B L)) (hG : ∀ n e B, CutOK P (G n e B)) (js : Bool) (cq mk : Nat) :
    ∀ (n x B : Nat), CutOK P (succC G js cq mk n x B) := by
  intro n
  induction n with
  | zero => intro x B; exact cutOK_some P
  | succ n ih =>
    intro x B
    have e : succC G js cq mk (n + 1) x B = fun L =>
        bnd (walkC G 6 (jsC js cq (x % 1024) mk) (x % P138) B L)
          (fun L1 => succC G js cq mk n (x / P138) B L1) := rfl
    rw [e]
    exact cutOK_bnd P (walkC_cut P G hGs hG _ _ _ _) (fun L => walkC_suffix G hGs _ _ _ _ L) (ih _ _)

section Rule

variable (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
  (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool)

theorem bodyC_cut (P : CS → Prop) (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hGs : ∀ t r d m M q B L, SufR L (G t r d m M q B L))
    (hG : ∀ t r d m M q B, CutOK P (G t r d m M q B)) (t r d : Nat) (m M : Int) (q B : Nat) :
    CutOK P (bodyC code mask fN fS cut wrec js G t r d m M q B) := by
  have e : bodyC code mask fN fS cut wrec js G t r d m M q B = fun L =>
      bif Nat.beq (code t r d) 0 then some L
      else bif Nat.beq (code t r d) 1 then none
      else
        bnd
          (bif !Nat.beq (code t r d) 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)) then
            succC (fun n e B' L' => G t (r + 1) (d + n) (min m (fN t r d)) (max M (fN t r d)) e B' L') js
              (wrec q % 1024) (mask t (r + 1) d) 6 (wrec q / 1024) B L
          else some L)
          (fun L1 =>
            bif !Nat.beq (code t r d) 2 && cut t r d (min m (fS t r d)) (max M (fS t r d)) then
              succC (fun n e B' L' => G (t + 1) (r + 1) (d + n) (min m (fS t r d)) (max M (fS t r d)) e B' L')
                js (wrec q % 1024) (mask (t + 1) (r + 1) d) 24
                (wrec q / 1024 / 2 ^ 828) B L1
            else some L1) := rfl
  rw [e]
  refine cutOK_cond P _ (cutOK_some P) (cutOK_cond P _ (cutOK_none P) ?_)
  have hN := succC_cut P (fun n e B' L' => G t (r + 1) (d + n) (min m (fN t r d)) (max M (fN t r d)) e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) (fun n e B' => hG _ _ _ _ _ _ _) js (wrec q % 1024)
    (mask t (r + 1) d) 6 (wrec q / 1024) B
  have hNs := succC_suffix (fun n e B' L' => G t (r + 1) (d + n) (min m (fN t r d)) (max M (fN t r d)) e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) js (wrec q % 1024) (mask t (r + 1) d) 6 (wrec q / 1024) B
  have hS := succC_cut P
    (fun n e B' L' => G (t + 1) (r + 1) (d + n) (min m (fS t r d)) (max M (fS t r d)) e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) (fun n e B' => hG _ _ _ _ _ _ _) js (wrec q % 1024)
    (mask (t + 1) (r + 1) d) 24 (wrec q / 1024 / 2 ^ 828) B
  exact cutOK_bnd P (cutOK_cond P _ hN (cutOK_some P)) (fun L => sufR_cond _ (hNs L) (sufR_some L))
    (cutOK_cond P _ hS (cutOK_some P))

theorem csEq_true {s : CS} {f t r d : Nat} {m M : Int} {q B : Nat} (h : csEq s f t r d m M q B = true) :
    s = ⟨f, t, r, d, m, M, q, B⟩ := by
  unfold csEq at h
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases s
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-- The whole search below a prefix does not find. -/
def FullC (s : CS) : Prop := goC code mask fN fS cut wrec js s.f s.t s.r s.d s.m s.M s.q s.B [] ≠ none

/-- **Cutting the search at the prefixes of a list.** -/
theorem goC_cut : ∀ (f t r d : Nat) (m M : Int) (q B : Nat),
    CutOK (FullC code mask fN fS cut wrec js) (goC code mask fN fS cut wrec js f t r d m M q B) := by
  intro f
  induction f with
  | zero => intro t r d m M q B L L' h; cases h
  | succ f ih =>
    intro t r d m M q B L L' h hP
    cases L with
    | nil => rw [h]; exact Option.some_ne_none _
    | cons s L1 =>
      rw [goC_succ] at h
      change (bif csEq s (f + 1) t r d m M q B then some L1
        else bodyC code mask fN fS cut wrec js (goC code mask fN fS cut wrec js f) t r d m M q B (s :: L1))
        = some L' at h
      cases hc : csEq s (f + 1) t r d m M q B with
      | true =>
        have hs := hP s List.mem_cons_self
        rw [csEq_true hc] at hs
        exact hs
      | false =>
        rw [hc, cond_false] at h
        have hb := bodyC_cut code mask fN fS cut wrec js (FullC code mask fN fS cut wrec js)
          (goC code mask fN fS cut wrec js f) (fun _ _ _ _ _ _ _ _ => goC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          ih t r d m M q B (s :: L1) L' h hP
        rw [goC_succ]
        exact hb

/-- **The whole search from a list.** -/
theorem searchC_cut {ws fuel : Nat} {L L' : List CS}
    (h : searchC code mask fN fS cut wrec js ws fuel L = some L')
    (hP : ∀ s ∈ L, FullC code mask fN fS cut wrec js s) :
    searchC code mask fN fS cut wrec js ws fuel [] ≠ none :=
  walkC_cut (FullC code mask fN fS cut wrec js)
    (fun n e B L => goC code mask fN fS cut wrec js fuel 0 1 n 0 0 e B L)
    (fun n e B L => goC_suffix code mask fN fS cut wrec js fuel 0 1 n 0 0 e B L)
    (fun n e B => goC_cut code mask fN fS cut wrec js fuel 0 1 n 0 0 e B) 6 63 ws 0 L L' h hP

end Rule

end Cert
end SuperpermLowerBounds
