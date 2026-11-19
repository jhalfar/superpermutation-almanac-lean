import Cert.PComplete
import Cert.Cut

/-!
# Skipped prefixes for the engine of `PEngine.lean`

As `Cut.lean`: `pgoC_cut`, `psearchC_cut`, and the forms used by the generated lemmas.
-/

namespace SuperpermLowerBounds
namespace Cert

section Rule

variable (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat)

theorem jumpC_cut (P : CS → Prop) (G : Nat → Nat → Nat → List CS → Res)
    (hGs : ∀ n e B L, SufR L (G n e B L)) (hG : ∀ n e B, CutOK P (G n e B)) (orb : Nat → Nat) :
    ∀ (n i B : Nat), CutOK P (jumpC G orb n i B) := by
  intro n
  induction n with
  | zero => intro i B; exact cutOK_some P
  | succ n ih =>
    intro i B
    have e : jumpC G orb (n + 1) i B = fun L =>
        bnd (walkC G 6 63 (orb i) B L) (fun L1 => jumpC G orb n (i + 1) B L1) := rfl
    rw [e]
    exact cutOK_bnd P (walkC_cut P G hGs hG _ _ _ _) (fun L => walkC_suffix G hGs _ _ _ _ L) (ih _ _)

theorem pbodyC_cut (P : CS → Prop) (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hGs : ∀ t r d m M q B L, SufR L (G t r d m M q B L))
    (hG : ∀ t r d m M q B, CutOK P (G t r d m M q B)) (t r d q B : Nat) :
    CutOK P (pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B) := by
  have e : pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B = fun L =>
      bif bad t r d || (badR t r d && slotHas 0 6 (wrec q / 1024)) then none
      else
        bnd (bif keepN t r d then
              succC (fun n e B' L' => G t (r + 1) (d + n) 0 0 e B' L') false 0 63 6 (wrec q / 1024) B L
            else some L)
          (fun L1 => bnd (bif keepS t r d then
              succC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
                false 0 63 24 (wrec q / 1024 / 2 ^ 828) B L1
            else some L1)
            (fun L2 => bif keepJ t r d then
              jumpC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
                orb 5040 0 B L2
            else some L2)) := rfl
  rw [e]
  refine cutOK_cond P _ (cutOK_none P) ?_
  have hN := succC_cut P (fun n e B' L' => G t (r + 1) (d + n) 0 0 e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) (fun n e B' => hG _ _ _ _ _ _ _) false 0 63 6 (wrec q / 1024) B
  have hNs := succC_suffix (fun n e B' L' => G t (r + 1) (d + n) 0 0 e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) false 0 63 6 (wrec q / 1024) B
  have hS := succC_cut P
    (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) (fun n e B' => hG _ _ _ _ _ _ _) false 0 63 24 (wrec q / 1024 / 2 ^ 828) B
  have hSs := succC_suffix
    (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) false 0 63 24 (wrec q / 1024 / 2 ^ 828) B
  have hJ := jumpC_cut P
    (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
    (fun n e B' L' => hGs _ _ _ _ _ _ _ _) (fun n e B' => hG _ _ _ _ _ _ _) orb 5040 0 B
  exact cutOK_bnd P (cutOK_cond P _ hN (cutOK_some P)) (fun L => sufR_cond _ (hNs L) (sufR_some L))
    (cutOK_bnd P (cutOK_cond P _ hS (cutOK_some P)) (fun L => sufR_cond _ (hSs L) (sufR_some L))
      (cutOK_cond P _ hJ (cutOK_some P)))

/-- The whole search below a prefix does not find. -/
def PFullC (s : CS) : Prop :=
  pgoC bad badR keepN keepS keepJ rs wrec orb s.f s.t s.r s.d s.m s.M s.q s.B [] ≠ none

/-- The search does not look at the potentials. -/
theorem pgoC_mM (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) :
    pgoC bad badR keepN keepS keepJ rs wrec orb f t r d m M q B L =
      pgoC bad badR keepN keepS keepJ rs wrec orb f t r d 0 0 q B L := by
  cases f <;> rfl

/-- **Cutting the search at the prefixes of a list.** -/
theorem pgoC_cut : ∀ (f t r d : Nat) (q B : Nat),
    CutOK (PFullC bad badR keepN keepS keepJ rs wrec orb) (pgoC bad badR keepN keepS keepJ rs wrec orb f t r d 0 0 q B) := by
  intro f
  induction f with
  | zero => intro t r d q B L L' h; cases h
  | succ f ih =>
    intro t r d q B L L' h hP
    cases L with
    | nil => rw [h]; exact Option.some_ne_none _
    | cons s L1 =>
      rw [pgoC_succ] at h
      change (bif csEq s (f + 1) t r d 0 0 q B then some L1
        else pbodyC bad badR keepN keepS keepJ rs wrec orb (pgoC bad badR keepN keepS keepJ rs wrec orb f)
          t r d q B (s :: L1)) = some L' at h
      cases hc : csEq s (f + 1) t r d 0 0 q B with
      | true =>
        have hs := hP s List.mem_cons_self
        rw [csEq_true hc] at hs
        exact hs
      | false =>
        rw [hc, Bool.cond_false] at h
        have hb := pbodyC_cut bad badR keepN keepS keepJ rs wrec orb (PFullC bad badR keepN keepS keepJ rs wrec orb)
          (pgoC bad badR keepN keepS keepJ rs wrec orb f)
          (fun _ _ _ _ _ _ _ _ => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          (fun t' r' d' m' M' q' B' => by
            intro L0 L0' h0 hP0
            rw [pgoC_mM] at h0 ⊢
            exact ih t' r' d' q' B' L0 L0' h0 hP0)
          t r d q B (s :: L1) L' h hP
        rw [pgoC_succ]
        exact hb

/-- **The whole search from a list.** -/
theorem psearchC_cut {ws fuel : Nat} {L L' : List CS}
    (h : psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel L = some L')
    (hP : ∀ s ∈ L, PFullC bad badR keepN keepS keepJ rs wrec orb s) :
    psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel [] ≠ none :=
  walkC_cut (PFullC bad badR keepN keepS keepJ rs wrec orb)
    (fun n e B L => pgoC bad badR keepN keepS keepJ rs wrec orb fuel 0 1 n 0 0 e B L)
    (fun n e B L => pgoC_suffix bad badR keepN keepS keepJ rs wrec orb fuel 0 1 n 0 0 e B L)
    (fun n e B => pgoC_cut bad badR keepN keepS keepJ rs wrec orb fuel 0 1 n e B) 6 63 ws 0 L L' h hP

theorem pfull_of_isSome {f t r d q B : Nat}
    (h : (pgoC bad badR keepN keepS keepJ rs wrec orb f t r d 0 0 q B []).isSome = true) :
    PFullC bad badR keepN keepS keepJ rs wrec orb ⟨f, t, r, d, 0, 0, q, B⟩ := by
  intro h0
  rw [show pgoC bad badR keepN keepS keepJ rs wrec orb f t r d 0 0 q B [] = none from h0] at h
  cases h

theorem pfull_of_cut {f t r d q B : Nat} {L : List CS}
    (h : (pgoC bad badR keepN keepS keepJ rs wrec orb f t r d 0 0 q B L).isSome = true)
    (hL : ∀ s ∈ L, PFullC bad badR keepN keepS keepJ rs wrec orb s) :
    PFullC bad badR keepN keepS keepJ rs wrec orb ⟨f, t, r, d, 0, 0, q, B⟩ := by
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp h
  exact pgoC_cut bad badR keepN keepS keepJ rs wrec orb f t r d q B L L' hL' hL

theorem psearchC_ok {ws fuel : Nat} {L : List CS}
    (h : (psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel L).isSome = true)
    (hL : ∀ s ∈ L, PFullC bad badR keepN keepS keepJ rs wrec orb s) :
    psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel [] ≠ none := by
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp h
  exact psearchC_cut bad badR keepN keepS keepJ rs wrec orb hL' hL

end Rule

end Cert
end SuperpermLowerBounds

namespace SuperpermLowerBounds
namespace Cert

section

variable {bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool} {rs : Bool} {wrec orb : Nat → Nat}

theorem pfullS_of_isSome {s : CS}
    (h : (pgoC bad badR keepN keepS keepJ rs wrec orb s.f s.t s.r s.d s.m s.M s.q s.B []).isSome = true) :
    PFullC bad badR keepN keepS keepJ rs wrec orb s := by
  intro h0
  rw [show pgoC bad badR keepN keepS keepJ rs wrec orb s.f s.t s.r s.d s.m s.M s.q s.B [] = none from h0] at h
  cases h

theorem pfullS_of_cut {s : CS} {L : List CS}
    (h : (pgoC bad badR keepN keepS keepJ rs wrec orb s.f s.t s.r s.d s.m s.M s.q s.B L).isSome = true)
    (hL : ∀ x ∈ L, PFullC bad badR keepN keepS keepJ rs wrec orb x) :
    PFullC bad badR keepN keepS keepJ rs wrec orb s := by
  rw [pgoC_mM] at h
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp h
  have := pgoC_cut bad badR keepN keepS keepJ rs wrec orb s.f s.t s.r s.d s.q s.B L L' hL' hL
  unfold PFullC
  rw [pgoC_mM]
  exact this

end

end Cert
end SuperpermLowerBounds
