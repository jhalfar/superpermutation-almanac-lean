import Asym25.Envelope
import Asym25.Params
import Quantitative.UniformPacking

/-!
# Exponent 25: a separated labelled family for the tied envelopes

Jay Pantone's `PackingSupply`, `LiteralPacking` and `UniformPacking` select
`⌊sourceEta M^d⌋` labelled frames whose envelopes are pairwise disjoint.
This module repeats the three for the tied envelopes (`MeetsT`,
`EnvelopeT`), whose degree is `Asym25.degree_240`: the family has
`⌊sourceEta25 M^d⌋` frames and needs `r ∣ M`. The proofs are his, with the
degree theorem, the envelope and the numbers changed; his three files are
unchanged.
-/

namespace CoefficientTwoPrecision.Asym25


open LabelledReconstruction SortedFrameSupply EnvelopeDegree

def desiredSize (M d : Nat) : Nat :=
  ((d + 3).factorial * M ^ d) / (2 * d.factorial * (240 * (d + 3) ^ 6 + 1))

theorem desiredSize_eq_floor (M d : Nat) :
    desiredSize M d = ⌊sourceEta25 (d + 3) * (M : ℚ) ^ d⌋₊ := by
  have hform : sourceEta25 (d + 3) * (M : ℚ) ^ d =
      (((d + 3).factorial * M ^ d : Nat) : ℚ) /
        ((2 * d.factorial * (240 * (d + 3) ^ 6 + 1) : Nat) : ℚ) := by
    simp only [sourceEta25, sourceDegree25, Nat.add_sub_cancel, Nat.cast_mul,
      Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [hform, ← Int.floor_toNat, Rat.floor_natCast_div_natCast]
  simp only [desiredSize, ← Int.natCast_ediv, Int.toNat_natCast]

theorem half_supply {M d : Nat} [NeZero M] (hd : 3 ≤ d)
    (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    M ^ d ≤ 2 * (physicalFrames M d).card * d.factorial := by
  have hpow : M * M ^ (d - 1) = M ^ d := by
    rw [← pow_succ']
    congr 1
    omega
  have hbase : 36 * (d + 2) ^ 4 ≤ M := by
    have hp := Nat.pow_le_pow_left (show d + 2 ≤ d + 3 by omega) 4
    nlinarith
  have hbad : 2 * (18 * (d + 2) ^ 4 * M ^ (d - 1)) ≤ M ^ d := by
    have h := Nat.mul_le_mul_right (M ^ (d - 1)) hbase
    rw [hpow] at h
    nlinarith
  have h := physicalFrames_card_lower (NeZero.pos M) hd
  nlinarith

theorem size_budget {M d : Nat} [NeZero M] (hd : 3 ≤ d)
    (hsize : 38 * (d + 3) ^ 4 ≤ M) :
    (240 * (d + 3) ^ 6 + 1) * desiredSize M d ≤ (labelledFrames M d).card := by
  have hhalf := half_supply hd hsize
  have hdivision := Nat.mul_div_le ((d + 3).factorial * M ^ d)
    (2 * d.factorial * (240 * (d + 3) ^ 6 + 1))
  have hscaled := Nat.mul_le_mul_left (d + 3).factorial hhalf
  have hcombined : (2 * d.factorial) * ((240 * (d + 3) ^ 6 + 1) * desiredSize M d) ≤
      (2 * d.factorial) * (labelledFrames M d).card := by
    rw [labelledFrames_card]
    dsimp only [desiredSize]
    nlinarith [hdivision, hscaled]
  exact Nat.le_of_mul_le_mul_left hcombined (by positivity)

theorem exists_separated {M d : Nat} [NeZero M] {α : Type} [DecidableEq α]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) (hdiv : d + 3 ∣ M)
    (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta25 (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
        ¬ MeetsT background embed (actionT d) (phaseT d) source target := by
  classical
  let R := MeetsT background embed (actionT d) (phaseT d)
  have hdegree : ∀ source ∈ labelledFrames M d,
      ((labelledFrames M d).filter (R source)).card ≤ 240 * (d + 3) ^ 6 + 1 := by
    intro source hs
    exact (degree_240 hM (by omega) hdiv (indexT_card d)
      backgroundTest background embed hbackground hembed htb htc
      (actionT d) (phaseT d) (phaseT_indep d) source hs).trans
      (Nat.le_succ _)
  obtain ⟨S, hS, hcard, hsep⟩ := FinitePacking.exists_separated_of_mul_le R
    (fun h => meetsT_symm _ _ _ _ h) (meetsT_refl _ _ _ _) (240 * (d + 3) ^ 6 + 1)
    (by omega) (labelledFrames M d) hdegree (desiredSize M d) (size_budget hd hsize)
  exact ⟨S, hS, hcard.trans (desiredSize_eq_floor M d), hsep⟩

open LabelledReconstruction SortedFrameSupply

def InEnvelope {M d : Nat} {α : Type} (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α) (frame : Labelled M d) (source : List α) : Prop :=
  EnvelopeT background
    (fun p => embed (FiniteRoles.lift ((PhysicalJointStates.reverseRoles (d + 2)).trans frame.2) p))
    (fun i => frame.1 i.rev) source

theorem exists_literal_separated {M d : Nat} [NeZero M] {α : Type} [DecidableEq α]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) (hdiv : d + 3 ∣ M)
    (backgroundTest : α → Bool) (background : Fin M → α)
    (embed : FiniteRoles.Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta25 (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
        ∀ first second : List α, InEnvelope background embed source first →
          InEnvelope background embed target second → ¬ first.IsRotated second := by
  classical
  obtain ⟨S, hS, hcard, hsep⟩ := exists_separated hd hM hsize hdiv
    backgroundTest background embed hbackground hembed htb htc
  refine ⟨S, hS, hcard, ?_⟩
  intro source hs target ht hne first second hfirst hsecond hcyclic
  obtain ⟨_, _, _, _, hr, _⟩ := physicalFrame_properties source.1
    (Finset.mem_product.mp (hS hs)).1
  obtain ⟨_, _, _, _, hr', _⟩ := physicalFrame_properties target.1
    (Finset.mem_product.mp (hS ht)).1
  obtain ⟨index, translation, gap, htied, hleft⟩ :=
    literal_memT hdiv background embed source.2 source.1 hr first hfirst
  obtain ⟨index', translation', gap', htied', hright⟩ :=
    literal_memT hdiv background embed target.2 target.1 hr' second hsecond
  apply hsep source hs target ht hne
  refine ⟨index, index', translation, translation', gap, gap', htied, htied', ?_⟩
  simpa only [hleft, hright] using hcyclic

open LabelledReconstruction SortedFrameSupply EnvelopeDegree FiniteRoles

theorem exists_uniform_separated {M d : Nat} [NeZero M]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) (hdiv : d + 3 ∣ M) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta25 (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ¬ MeetsT background embed (actionT d) (phaseT d)
            source target := by
  classical
  let Alphabet := Sum (Fin M) (Role (d + 2))
  let test : Alphabet → Bool := Sum.elim (fun _ => true) (fun _ => false)
  obtain ⟨S, hS, hcard, hsep⟩ := exists_separated hd hM hsize hdiv test
    (Sum.inl : Fin M → Alphabet) (Sum.inr : Role (d + 2) → Alphabet)
    Sum.inl_injective Sum.inr_injective (fun _ => rfl) (fun _ => rfl)
  refine ⟨S, hS, hcard, ?_⟩
  intro α background embed hb he hcross source hs target ht hne hmeet
  apply hsep source hs target ht hne
  obtain ⟨first, second, t, t', gap, gap', h1, h2, h⟩ := hmeet
  refine ⟨first, second, t, t', gap, gap', h1, h2, ?_⟩
  apply UniformPacking.isRotated_of_map (Sum.elim background embed) (UniformPacking.joint_injective background embed hb he hcross)
  simpa only [UniformPacking.row_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using h

theorem exists_uniform_literal_separated {M d : Nat} [NeZero M]
    (hd : 3 ≤ d) (hM : 2 ≤ M) (hsize : 38 * (d + 3) ^ 4 ≤ M) (hdiv : d + 3 ∣ M) :
    ∃ S : Finset (Labelled M d), S ⊆ labelledFrames M d ∧
      S.card = ⌊sourceEta25 (d + 3) * (M : ℚ) ^ d⌋₊ ∧
      ∀ {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α),
        Function.Injective background → Function.Injective embed →
        (∀ i c, background i ≠ embed c) →
        ∀ source ∈ S, ∀ target ∈ S, source ≠ target →
          ∀ first second : List α, InEnvelope background embed source first →
            InEnvelope background embed target second → ¬ first.IsRotated second := by
  classical
  obtain ⟨S, hS, hcard, hsep⟩ := exists_uniform_separated hd hM hsize hdiv
  refine ⟨S, hS, hcard, ?_⟩
  intro α background embed hb he hcross source hs target ht hne first second hf hg hc
  obtain ⟨_, _, _, _, hr, _⟩ := physicalFrame_properties source.1
    (Finset.mem_product.mp (hS hs)).1
  obtain ⟨_, _, _, _, hr', _⟩ := physicalFrame_properties target.1
    (Finset.mem_product.mp (hS ht)).1
  obtain ⟨index, translation, gap, htied, hfirst⟩ :=
    literal_memT hdiv background embed source.2 source.1 hr first hf
  obtain ⟨index', translation', gap', htied', hsecond⟩ :=
    literal_memT hdiv background embed target.2 target.1 hr' second hg
  apply hsep background embed hb he hcross source hs target ht hne
  refine ⟨index, index', translation, translation', gap, gap', htied, htied', ?_⟩
  simpa only [hfirst, hsecond] using hc

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.exists_separated
#print axioms CoefficientTwoPrecision.Asym25.exists_uniform_literal_separated
