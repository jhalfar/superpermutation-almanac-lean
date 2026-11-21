import Asym29.Sorted

/-!
# Exponent 29: the envelope degree is at most `192 r^7`

Jay Pantone's `EnvelopeDegree.degree_64` bounds the number of labelled sorted
frames whose envelopes meet a given one by `64 r^8`: `(4r^2)^2` pairs of joint
states times `(d+2)(d+1)^2(2d) * 2` reconstruction witnesses. With the lemmas
of `Asym29.Sorted` the targets for one pair of joint states number at most
`(d+2) ((d+1)(4d+6) * 2 + (d+1) * 2 * (d-1) * 2) ≤ 12 r^3`, so the degree is at
most `192 r^7` (`degree_192`). The witnesses themselves are his
(`PositionalExtraction.actual_reconstruction`); only the count is new.
-/

namespace CoefficientTwoPrecision.Asym29

open FiniteRoles BatchSafety ActualCyclicMatching AffineReconstruction LabelledReconstruction
open RobustMatching

variable {M d : Nat} [NeZero M]

/-- Targets with the anchor retained, listed with their omitted slot. -/
noncomputable def pairs1 (S E : Fin (d + 2) → ZMod M) (L T : Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) (c : Fin (d + 1)) : Finset (Fin (d + 2) × Labelled M d) := by
  classical
  exact Finset.univ.filter (fun jt => jt.1 ≠ 0 ∧ Framed jt.2.1 ∧
    (∃ δ, Matched S E i jt.1 c jt.2.1 δ) ∧
    jt.2.2 ∈ CyclicLabelCount.candidates L T i jt.1 c)

theorem pairs1_card {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    (L T : Equiv.Perm (Role (d + 2))) (i : Fin (d + 2)) (c : Fin (d + 1)) :
    (pairs1 S E L T i c).card ≤ (4 * d + 6) * 2 := by
  classical
  refine (FiniteFibers.card_le_of_fiber_bound (pairs1 S E L T i c) (valueSet S E i c)
    (fun jt => cutValue (jt.2.1 jt.1)) 2 ?_ ?_).trans
    (Nat.mul_le_mul_right 2 (valueSet_card S E i c))
  · intro jt hjt
    obtain ⟨hj, hq, ⟨δ, hm⟩, _⟩ := (Finset.mem_filter.mp hjt).2
    exact omitted_value_mem hE hq hm hj
  · intro b _
    rcases ((pairs1 S E L T i c).filter
      (fun jt => cutValue (jt.2.1 jt.1) = b)).eq_empty_or_nonempty with hnil | ⟨jt0, h0⟩
    · rw [hnil]
      simp
    · obtain ⟨h0mem, h0b⟩ := Finset.mem_filter.mp h0
      obtain ⟨hj0, hq0, ⟨δ0, hm0⟩, hl0⟩ := (Finset.mem_filter.mp h0mem).2
      refine (Finset.card_le_card (t := (CyclicLabelCount.candidates L T i jt0.1 c).image
        (fun σ => (jt0.1, (jt0.2.1, σ)))) ?_).trans
        (Finset.card_image_le.trans (CyclicLabelCount.candidates_card L T i jt0.1 c))
      intro jt hjt
      obtain ⟨hmem, hb⟩ := Finset.mem_filter.mp hjt
      obtain ⟨hj, hq, ⟨δ, hm⟩, hl⟩ := (Finset.mem_filter.mp hmem).2
      have hval : jt.2.1 jt.1 = jt0.2.1 jt0.1 := cutValue_injective (hb.trans h0b.symm)
      have hjeq : jt.1 = jt0.1 := by
        rcases lt_trichotomy jt.1 jt0.1 with hlt | heq | hgt
        · exact absurd hval (ne_of_lt (omitted_value_lt hE hq hq0 hm hm0 hj hlt))
        · exact heq
        · exact absurd hval.symm (ne_of_lt (omitted_value_lt hE hq0 hq hm0 hm hj0 hgt))
      obtain ⟨j, q, σ⟩ := jt
      obtain ⟨j0, q0, σ0⟩ := jt0
      dsimp only at hjeq hval hm hl hq hj hm0 hq0 ⊢
      subst hjeq
      have hqeq : q = q0 := frame_eq_of_omitted hq.2.1 hq0.2.1 hm hm0 hj hval
      subst hqeq
      exact Finset.mem_image.mpr ⟨σ, hl, rfl⟩

/-- Targets with the anchor omitted, listed with their cyclic offset. -/
noncomputable def pairs0 (S E : Fin (d + 2) → ZMod M) (L T : Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) : Finset (Fin (d + 1) × Labelled M d) := by
  classical
  exact Finset.univ.filter (fun ct => Framed ct.2.1 ∧
    (∃ δ, Matched S E i 0 ct.1 ct.2.1 δ) ∧
    ct.2.2 ∈ CyclicLabelCount.candidates L T i 0 ct.1)

theorem matched0_translation {S E : Fin (d + 2) → ZMod M} {i : Fin (d + 2)}
    {c : Fin (d + 1)} {q : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hm : Matched S E i 0 c q δ) :
    δ = S (i.succAbove (0 + c)) - E (Fin.succ 0) - cutValue (q (Fin.succ 0)) := by
  have h := hm 0
  rw [show (0 : Fin (d + 2)).succAbove (0 : Fin (d + 1)) = Fin.succ 0 from
    congrFun Fin.succAbove_zero 0] at h
  linear_combination h

theorem pairs0_card (hd : 2 ≤ d) {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    (L T : Equiv.Perm (Role (d + 2))) (i : Fin (d + 2)) :
    (pairs0 S E L T i).card ≤ (d + 1) * 2 * (d - 1) * 2 := by
  classical
  refine (FiniteFibers.card_le_of_fiber_bound (pairs0 S E L T i) (translationSet S E i)
    (fun ct => S (i.succAbove (0 + ct.1)) - E (Fin.succ 0) - cutValue (ct.2.1 (Fin.succ 0))) 2
    ?_ ?_).trans (Nat.mul_le_mul_right 2 (translationSet_card hd S E i))
  · intro ct hct
    obtain ⟨hq, ⟨δ, hm⟩, _⟩ := (Finset.mem_filter.mp hct).2
    have hδ := matched0_translation hm
    have := translation_mem hd hE hq hm
    rw [hδ] at this
    exact this
  · intro b _
    rcases ((pairs0 S E L T i).filter (fun ct =>
      S (i.succAbove (0 + ct.1)) - E (Fin.succ 0) - cutValue (ct.2.1 (Fin.succ 0)) = b)
      ).eq_empty_or_nonempty with hnil | ⟨ct0, h0⟩
    · rw [hnil]
      simp
    · obtain ⟨h0mem, h0b⟩ := Finset.mem_filter.mp h0
      obtain ⟨hq0, ⟨δ0, hm0⟩, hl0⟩ := (Finset.mem_filter.mp h0mem).2
      refine (Finset.card_le_card (t := (CyclicLabelCount.candidates L T i 0 ct0.1).image
        (fun σ => (ct0.1, (ct0.2.1, σ)))) ?_).trans
        (Finset.card_image_le.trans (CyclicLabelCount.candidates_card L T i 0 ct0.1))
      intro ct hct
      obtain ⟨hmem, hb⟩ := Finset.mem_filter.mp hct
      obtain ⟨hq, ⟨δ, hm⟩, hl⟩ := (Finset.mem_filter.mp hmem).2
      have hδ : δ = b := (matched0_translation hm).trans hb
      have hδ0 : δ0 = b := (matched0_translation hm0).trans h0b
      subst hδ
      subst hδ0
      have hc : ct.1 = ct0.1 := offset_eq_of_translation hd hE hq hq0 hm hm0
      obtain ⟨c, q, σ⟩ := ct
      obtain ⟨c0, q0, σ0⟩ := ct0
      dsimp only at hc hm hl hq hm0 hq0 ⊢
      subst hc
      have hqeq : q = q0 := frame_eq_of_translation hq.2.1 hq0.2.1 hm hm0
      subst hqeq
      exact Finset.mem_image.mpr ⟨σ, hl, rfl⟩

/-- A sorted physical frame is `Framed`: with the anchor at zero, his affine
relation says that the cuts add up to twice the sum point. -/
theorem framed_of_physical {q : Fin (d + 2) → Fin M}
    (hq : q ∈ SortedFrameSupply.physicalFrames M d) : Framed q := by
  classical
  obtain ⟨s, hs, hm, hz, _, hrel⟩ := SortedFrameSupply.physicalFrame_properties q hq
  refine ⟨hm, hz, s, hs, ?_⟩
  have hterm : ∀ p : Fin (d + 2),
      ((frameWeight d s p : ℤ) : ZMod M) * (((q p).val : ℕ) : ZMod M) =
        -(((q p).val : ℕ) : ZMod M) +
          (if p = 0 then (d : ZMod M) * (((q p).val : ℕ) : ZMod M) else 0) +
          (if p = s then 2 * (((q p).val : ℕ) : ZMod M) else 0) := by
    intro p
    by_cases h0 : p = 0
    · have hne : ¬ p = s := fun h => hs (h ▸ h0)
      rw [if_pos h0, if_neg hne]
      simp only [frameWeight, if_pos h0]
      push_cast
      ring
    · by_cases hps : p = s
      · rw [if_neg h0, if_pos hps]
        simp only [frameWeight, if_neg h0, if_pos hps]
        push_cast
        ring
      · rw [if_neg h0, if_neg hps]
        simp only [frameWeight, if_neg h0, if_neg hps]
        push_cast
        ring
  simp_rw [hterm] at hrel
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (d + 2)), Finset.sum_ite_eq' Finset.univ s] at hrel
  simp only [Finset.mem_univ, if_true] at hrel
  have hzero := cutValue_zero_of (M := M) hz
  simp only [cutValue] at hzero ⊢
  linear_combination -hrel + (d : ZMod M) * hzero

def srcCuts (q : Fin (d + 2) → Fin M) (ph : Fin (d + 2) → Bool) : Fin (d + 2) → ZMod M :=
  fun p => cutValue (q p) + (bit (ph p) : ZMod M)

def tgtBits (M : Nat) (ph : Fin (d + 2) → Bool) : Fin (d + 2) → ZMod M :=
  fun p => (bit (ph p) : ZMod M)

omit [NeZero M] in
theorem tgtBits_isBit (ph : Fin (d + 2) → Bool) : IsBit (tgtBits M ph) := by
  intro p
  unfold tgtBits
  cases ph p
  · left; simp [bit]
  · right; simp [bit]

theorem count_bound (d : Nat) (hd : 2 ≤ d) :
    (d + 2) * ((d + 1) * ((4 * d + 6) * 2) + (d + 1) * 2 * (d - 1) * 2) ≤ 12 * (d + 3) ^ 3 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have h1 : e + 2 - 1 = e + 1 := by omega
  rw [h1]
  calc
    (e + 2 + 2) * ((e + 2 + 1) * ((4 * (e + 2) + 6) * 2) + (e + 2 + 1) * 2 * (e + 1) * 2) =
        (e + 4) * (e + 3) * (12 * e + 32) := by ring
    _ ≤ (e + 5) * (e + 5) * (12 * (e + 5)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    _ = 12 * (e + 2 + 3) ^ 3 := by ring

/-- All targets for one pair of joint states. -/
noncomputable def pairCatalogue {I : Type} (action : I → Equiv.Perm (Role (d + 2)))
    (phase : I → Fin (d + 2) → Bool) (source : Labelled M d) (pair : I × I) :
    Finset (Labelled M d) := by
  classical
  exact Finset.univ.biUnion (fun i : Fin (d + 2) =>
    (Finset.univ.biUnion (fun c : Fin (d + 1) =>
      (pairs1 (srcCuts source.1 (phase pair.1)) (tgtBits M (phase pair.2))
        ((action pair.1).trans source.2) (action pair.2) i c).image Prod.snd)) ∪
    (pairs0 (srcCuts source.1 (phase pair.1)) (tgtBits M (phase pair.2))
        ((action pair.1).trans source.2) (action pair.2) i).image Prod.snd)

theorem pairCatalogue_card {I : Type} (hd : 2 ≤ d) (action : I → Equiv.Perm (Role (d + 2)))
    (phase : I → Fin (d + 2) → Bool) (source : Labelled M d) (pair : I × I) :
    (pairCatalogue action phase source pair).card ≤ 12 * (d + 3) ^ 3 := by
  classical
  refine le_trans ?_ (count_bound d hd)
  have h := FiniteFibers.bad_union_count (Finset.univ : Finset (Fin (d + 2)))
    (fun i : Fin (d + 2) =>
      (Finset.univ.biUnion (fun c : Fin (d + 1) =>
        (pairs1 (srcCuts source.1 (phase pair.1)) (tgtBits M (phase pair.2))
          ((action pair.1).trans source.2) (action pair.2) i c).image Prod.snd)) ∪
      (pairs0 (srcCuts source.1 (phase pair.1)) (tgtBits M (phase pair.2))
          ((action pair.1).trans source.2) (action pair.2) i).image Prod.snd)
    ((d + 1) * ((4 * d + 6) * 2) + (d + 1) * 2 * (d - 1) * 2) ?_
  · simpa only [pairCatalogue, Finset.card_univ, Fintype.card_fin] using h
  · intro i _
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · have h1 := FiniteFibers.bad_union_count (Finset.univ : Finset (Fin (d + 1)))
        (fun c : Fin (d + 1) =>
          (pairs1 (srcCuts source.1 (phase pair.1)) (tgtBits M (phase pair.2))
            ((action pair.1).trans source.2) (action pair.2) i c).image Prod.snd)
        ((4 * d + 6) * 2)
        (fun c _ => Finset.card_image_le.trans
          (pairs1_card (tgtBits_isBit (phase pair.2)) _ _ i c))
      simpa only [Finset.card_univ, Fintype.card_fin] using h1
    · exact Finset.card_image_le.trans (pairs0_card hd (tgtBits_isBit (phase pair.2)) _ _ i)

theorem intersection_mem {I α : Type} [Fintype I] [DecidableEq α] (hM : 2 ≤ M)
    (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source target : Labelled M d)
    (hsource : source ∈ SortedFrameSupply.labelledFrames M d)
    (htarget : target ∈ SortedFrameSupply.labelledFrames M d)
    (hmeet : EnvelopeDegree.Meets background embed action phase source target) :
    target ∈ (Finset.univ : Finset (I × I)).biUnion (pairCatalogue action phase source) := by
  classical
  have htphys := (Finset.mem_product.mp htarget).1
  have hframed := framed_of_physical htphys
  obtain ⟨_, _, hm, hz, hr, _⟩ := SortedFrameSupply.physicalFrame_properties source.1
    (Finset.mem_product.mp hsource).1
  obtain ⟨sumSlot, hs, hm', hz', hr', hrel⟩ :=
    SortedFrameSupply.physicalFrame_properties target.1 htphys
  obtain ⟨sumIndex, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs
  obtain ⟨first, second, t, t', gap, gap', hcyclic⟩ := hmeet
  obtain ⟨omitted, other, offset, hpos, hlabels⟩ :=
    PositionalExtraction.actual_reconstruction hM backgroundTest background embed
      hbackground hembed htb htc ((action first).trans source.2) ((action second).trans target.2)
      source.1 target.1 hm hm' hr hr' hz hz' sumIndex hrel t t'
      (phase first) (phase second) _ _ gap gap'
      (EnvelopeDegree.phaseCuts_represents source.1 t (phase first))
      (EnvelopeDegree.phaseCuts_represents target.1 t' (phase second)) hcyclic
  have hmatched : Matched (srcCuts source.1 (phase first)) (tgtBits M (phase second))
      omitted other offset target.1 (t' - t) := by
    intro x
    obtain ⟨_, _, _, hmatches⟩ := Finset.mem_filter.mp hpos
    have h := hmatches (other.succAbove x) (Fin.succAbove_ne other x)
    simpa only [srcCuts, tgtBits, PositionalCatalogue.observation,
      Fin.insertNth_apply_succAbove] using h
  have hlab : target.2 ∈ CyclicLabelCount.candidates ((action first).trans source.2)
      (action second) omitted other offset :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabels⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(first, second), Finset.mem_univ _, ?_⟩
  unfold pairCatalogue
  apply Finset.mem_biUnion.mpr
  refine ⟨omitted, Finset.mem_univ _, ?_⟩
  by_cases ho : other = 0
  · subst ho
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(offset, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hframed, ⟨t' - t, hmatched⟩, hlab⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨offset, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(other, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ho, hframed, ⟨t' - t, hmatched⟩, hlab⟩, rfl⟩

/-- The envelope degree, counted with the source itself, is at most `192 r^7`. -/
theorem degree_192 {I α : Type} [Fintype I] [DecidableEq α] (hM : 2 ≤ M) (hd : 2 ≤ d)
    (hI : Fintype.card I ≤ 4 * (d + 3) ^ 2) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source : Labelled M d) (hsource : source ∈ SortedFrameSupply.labelledFrames M d) :
    (EnvelopeDegree.neighbours background embed action phase source).card ≤
      192 * (d + 3) ^ 7 := by
  classical
  have hsub : EnvelopeDegree.neighbours background embed action phase source ⊆
      (Finset.univ : Finset (I × I)).biUnion (pairCatalogue action phase source) := by
    intro target ht
    obtain ⟨htarget, hmeet⟩ := Finset.mem_filter.mp ht
    exact intersection_mem hM backgroundTest background embed hbackground hembed htb htc
      action phase source target hsource htarget hmeet
  have hunion := FiniteFibers.bad_union_count (Finset.univ : Finset (I × I))
    (pairCatalogue action phase source) (12 * (d + 3) ^ 3)
    (fun pair _ => pairCatalogue_card hd action phase source pair)
  calc
    (EnvelopeDegree.neighbours background embed action phase source).card ≤
        ((Finset.univ : Finset (I × I)).biUnion (pairCatalogue action phase source)).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (I × I)).card * (12 * (d + 3) ^ 3) := hunion
    _ = Fintype.card I ^ 2 * (12 * (d + 3) ^ 3) := by
      simp only [Finset.card_univ, Fintype.card_prod, pow_two]
    _ ≤ (4 * (d + 3) ^ 2) ^ 2 * (12 * (d + 3) ^ 3) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hI 2)
    _ = 192 * (d + 3) ^ 7 := by ring

end CoefficientTwoPrecision.Asym29

#print axioms CoefficientTwoPrecision.Asym29.degree_192
