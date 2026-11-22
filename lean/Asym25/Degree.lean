import Asym29.Degree

/-!
# Exponent 25: the degree of the tied envelopes is at most `240 r^6`

In Jay Pantone's envelope a joint state (role phase `s`, prefix) may occur at
every translation. In an actual normal batch the role phase is the
translation modulo `r`, and with the repairs of `Asym25.Parking` a parking
interval starts at role phase 0 or 2. So a state `(s, j)` is used at the
translation `t` only if `s = 0`, `s = 2` or `s = t mod r` (`Tied`).

For a pair of joint states the targets number at most `12 r^3`
(`Asym29.pairCatalogue_card`). If both states are tied to their translations,
the role phase of the target is the role phase of the source plus the
translation difference, and the reconstruction of the target cuts fixes that
difference (`Asym29.translation_of_anchor`, `matched0_translation`). So the
same `12 r^3` bounds the targets of all `r` role phases of the target together
(`tiedCatalogue_card`). With `r |J|` states, of which `2 |J|` are free:
`12 r^3 (2 + 2 + 1) r |J|^2 <= 240 r^6` for `|J| <= 2r` (`degree_240`).
-/

namespace CoefficientTwoPrecision.Asym25

open FiniteRoles BatchSafety ActualCyclicMatching AffineReconstruction LabelledReconstruction
open RobustMatching Asym29

variable {M d : Nat} [NeZero M]

/-- Targets with the anchor retained; the target role action may depend on
the translation difference. -/
noncomputable def pairs1T (S E : Fin (d + 2) → ZMod M) (L : Equiv.Perm (Role (d + 2)))
    (T : ZMod M → Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) (c : Fin (d + 1)) : Finset (Fin (d + 2) × Labelled M d) := by
  classical
  exact Finset.univ.filter (fun jt => jt.1 ≠ 0 ∧ Framed jt.2.1 ∧
    ∃ δ, Matched S E i jt.1 c jt.2.1 δ ∧
      jt.2.2 ∈ CyclicLabelCount.candidates L (T δ) i jt.1 c)

theorem pairs1T_card {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    (L : Equiv.Perm (Role (d + 2))) (T : ZMod M → Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) (c : Fin (d + 1)) :
    (pairs1T S E L T i c).card ≤ (4 * d + 6) * 2 := by
  classical
  refine (FiniteFibers.card_le_of_fiber_bound (pairs1T S E L T i c) (valueSet S E i c)
    (fun jt => cutValue (jt.2.1 jt.1)) 2 ?_ ?_).trans
    (Nat.mul_le_mul_right 2 (valueSet_card S E i c))
  · intro jt hjt
    obtain ⟨hj, hq, δ, hm, _⟩ := (Finset.mem_filter.mp hjt).2
    exact omitted_value_mem hE hq hm hj
  · intro b _
    rcases ((pairs1T S E L T i c).filter
      (fun jt => cutValue (jt.2.1 jt.1) = b)).eq_empty_or_nonempty with hnil | ⟨jt0, h0⟩
    · rw [hnil]
      simp
    · obtain ⟨h0mem, h0b⟩ := Finset.mem_filter.mp h0
      obtain ⟨hj0, hq0, δ0, hm0, hl0⟩ := (Finset.mem_filter.mp h0mem).2
      refine (Finset.card_le_card (t := (CyclicLabelCount.candidates L (T δ0) i jt0.1 c).image
        (fun σ => (jt0.1, (jt0.2.1, σ)))) ?_).trans
        (Finset.card_image_le.trans (CyclicLabelCount.candidates_card L (T δ0) i jt0.1 c))
      intro jt hjt
      obtain ⟨hmem, hb⟩ := Finset.mem_filter.mp hjt
      obtain ⟨hj, hq, δ, hm, hl⟩ := (Finset.mem_filter.mp hmem).2
      have hval : jt.2.1 jt.1 = jt0.2.1 jt0.1 := cutValue_injective (hb.trans h0b.symm)
      have hjeq : jt.1 = jt0.1 := by
        rcases lt_trichotomy jt.1 jt0.1 with hlt | heq | hgt
        · exact absurd hval (ne_of_lt (omitted_value_lt hE hq hq0 hm hm0 hj hlt))
        · exact heq
        · exact absurd hval.symm (ne_of_lt (omitted_value_lt hE hq0 hq hm0 hm hj0 hgt))
      obtain ⟨j, q, σ⟩ := jt
      obtain ⟨j0, q0, σ0⟩ := jt0
      dsimp only at hjeq hval hm hl hq hj hm0 hq0 hj0 hl0 ⊢
      subst hjeq
      have hqeq : q = q0 := frame_eq_of_omitted hq.2.1 hq0.2.1 hm hm0 hj hval
      subst hqeq
      have hδ : δ = δ0 :=
        (translation_of_anchor hm hq.2.1 hj).trans (translation_of_anchor hm0 hq.2.1 hj).symm
      subst hδ
      exact Finset.mem_image.mpr ⟨σ, hl, rfl⟩

/-- Targets with the anchor omitted. -/
noncomputable def pairs0T (S E : Fin (d + 2) → ZMod M) (L : Equiv.Perm (Role (d + 2)))
    (T : ZMod M → Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) : Finset (Fin (d + 1) × Labelled M d) := by
  classical
  exact Finset.univ.filter (fun ct => Framed ct.2.1 ∧
    ∃ δ, Matched S E i 0 ct.1 ct.2.1 δ ∧
      ct.2.2 ∈ CyclicLabelCount.candidates L (T δ) i 0 ct.1)

theorem pairs0T_card (hd : 2 ≤ d) {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    (L : Equiv.Perm (Role (d + 2))) (T : ZMod M → Equiv.Perm (Role (d + 2)))
    (i : Fin (d + 2)) :
    (pairs0T S E L T i).card ≤ (d + 1) * 2 * (d - 1) * 2 := by
  classical
  refine (FiniteFibers.card_le_of_fiber_bound (pairs0T S E L T i) (translationSet S E i)
    (fun ct => S (i.succAbove (0 + ct.1)) - E (Fin.succ 0) - cutValue (ct.2.1 (Fin.succ 0))) 2
    ?_ ?_).trans (Nat.mul_le_mul_right 2 (translationSet_card hd S E i))
  · intro ct hct
    obtain ⟨hq, δ, hm, _⟩ := (Finset.mem_filter.mp hct).2
    have hδ := matched0_translation hm
    have := translation_mem hd hE hq hm
    rw [hδ] at this
    exact this
  · intro b _
    rcases ((pairs0T S E L T i).filter (fun ct =>
      S (i.succAbove (0 + ct.1)) - E (Fin.succ 0) - cutValue (ct.2.1 (Fin.succ 0)) = b)
      ).eq_empty_or_nonempty with hnil | ⟨ct0, h0⟩
    · rw [hnil]
      simp
    · obtain ⟨h0mem, h0b⟩ := Finset.mem_filter.mp h0
      obtain ⟨hq0, δ0, hm0, hl0⟩ := (Finset.mem_filter.mp h0mem).2
      have hδ0 : δ0 = b := (matched0_translation hm0).trans h0b
      subst hδ0
      refine (Finset.card_le_card (t := (CyclicLabelCount.candidates L (T δ0) i 0 ct0.1).image
        (fun σ => (ct0.1, (ct0.2.1, σ)))) ?_).trans
        (Finset.card_image_le.trans (CyclicLabelCount.candidates_card L (T δ0) i 0 ct0.1))
      intro ct hct
      obtain ⟨hmem, hb⟩ := Finset.mem_filter.mp hct
      obtain ⟨hq, δ, hm, hl⟩ := (Finset.mem_filter.mp hmem).2
      have hδ : δ = δ0 := (matched0_translation hm).trans hb
      subst hδ
      have hc : ct.1 = ct0.1 := offset_eq_of_translation hd hE hq hq0 hm hm0
      obtain ⟨c, q, σ⟩ := ct
      obtain ⟨c0, q0, σ0⟩ := ct0
      dsimp only at hc hm hl hq hm0 hq0 ⊢
      subst hc
      have hqeq : q = q0 := frame_eq_of_translation hq.2.1 hq0.2.1 hm hm0
      subst hqeq
      exact Finset.mem_image.mpr ⟨σ, hl, rfl⟩

variable {J : Type}

/-- A joint state `(s, j)` may be used at the translation `t`: the role phase
is 0 or 2 (parking) or the translation modulo `r` (normal batches). -/
def Tied (index : Fin (d + 3) × J) (t : ZMod M) : Prop :=
  index.1.val = 0 ∨ index.1.val = 2 ∨ index.1.val = t.val % (d + 3)

/-- The role phase moved by a translation difference. -/
def shift (s : Fin (d + 3)) (δ : ZMod M) : Fin (d + 3) :=
  ⟨(s.val + δ.val) % (d + 3), Nat.mod_lt _ (by omega)⟩

theorem shift_eq (hdiv : d + 3 ∣ M) {s s' : Fin (d + 3)} {t t' : ZMod M}
    (hs : s.val = t.val % (d + 3)) (hs' : s'.val = t'.val % (d + 3)) :
    s' = shift s (t' - t) := by
  apply Fin.ext
  change s'.val = (s.val + (t' - t).val) % (d + 3)
  have hval : (t.val + (t' - t).val) % M = t'.val := by
    rw [← ZMod.val_add]
    congr 1
    ring
  rw [hs, hs', Nat.mod_add_mod, ← Nat.mod_mod_of_dvd (t.val + (t' - t).val) hdiv, hval]

def zeroTwo (d : Nat) (b : Bool) : Fin (d + 3) :=
  if b then ⟨2, by omega⟩ else ⟨0, by omega⟩

/-- Two envelopes meet through states tied to their translations. -/
def MeetsT {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (source target : Labelled M d) : Prop :=
  ∃ first second : Fin (d + 3) × J, ∃ t t' : ZMod M, ∃ gap gap' : Nat,
    Tied first t ∧ Tied second t' ∧
    (EnvelopeDegree.row background embed action phase source first t gap).IsRotated
      (EnvelopeDegree.row background embed action phase target second t' gap')

theorem meetsT_symm {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    {source target : Labelled M d} (h : MeetsT background embed action phase source target) :
    MeetsT background embed action phase target source := by
  obtain ⟨first, second, t, t', gap, gap', h1, h2, h⟩ := h
  exact ⟨second, first, t', t, gap', gap, h2, h1, h.symm⟩

theorem meetsT_refl [Nonempty J] {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (source : Labelled M d) : MeetsT background embed action phase source source := by
  classical
  let j : J := Classical.choice inferInstance
  exact ⟨(⟨0, by omega⟩, j), (⟨0, by omega⟩, j), 0, 0, 0, 0, Or.inl rfl, Or.inl rfl,
    List.IsRotated.refl _⟩

/-- The reconstruction witness of one actual intersection (the first half of
`Asym29.intersection_mem`, for the given pair of states). -/
theorem meet_witness {I α : Type} [DecidableEq α] (hM : 2 ≤ M)
    (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : I → Equiv.Perm (Role (d + 2))) (phase : I → Fin (d + 2) → Bool)
    (source target : Labelled M d)
    (hsource : source ∈ SortedFrameSupply.labelledFrames M d)
    (htarget : target ∈ SortedFrameSupply.labelledFrames M d)
    (first second : I) (t t' : ZMod M) (gap gap' : Nat)
    (hcyclic : (EnvelopeDegree.row background embed action phase source first t gap).IsRotated
      (EnvelopeDegree.row background embed action phase target second t' gap')) :
    Framed target.1 ∧ ∃ omitted other : Fin (d + 2), ∃ offset : Fin (d + 1),
      Matched (srcCuts source.1 (phase first)) (tgtBits M (phase second))
        omitted other offset target.1 (t' - t) ∧
      target.2 ∈ CyclicLabelCount.candidates ((action first).trans source.2)
        (action second) omitted other offset := by
  classical
  have htphys := (Finset.mem_product.mp htarget).1
  have hframed := framed_of_physical htphys
  obtain ⟨_, _, hm, hz, hr, _⟩ := SortedFrameSupply.physicalFrame_properties source.1
    (Finset.mem_product.mp hsource).1
  obtain ⟨sumSlot, hs, hm', hz', hr', hrel⟩ :=
    SortedFrameSupply.physicalFrame_properties target.1 htphys
  obtain ⟨sumIndex, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs
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
  exact ⟨hframed, omitted, other, offset, hmatched,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabels⟩⟩

theorem mem_pairCatalogue {I : Type} (action : I → Equiv.Perm (Role (d + 2)))
    (phase : I → Fin (d + 2) → Bool) (source target : Labelled M d) (first second : I)
    (δ : ZMod M) (hframed : Framed target.1) (omitted other : Fin (d + 2)) (offset : Fin (d + 1))
    (hmatched : Matched (srcCuts source.1 (phase first)) (tgtBits M (phase second))
      omitted other offset target.1 δ)
    (hlab : target.2 ∈ CyclicLabelCount.candidates ((action first).trans source.2)
      (action second) omitted other offset) :
    target ∈ pairCatalogue action phase source (first, second) := by
  classical
  unfold pairCatalogue
  apply Finset.mem_biUnion.mpr
  refine ⟨omitted, Finset.mem_univ _, ?_⟩
  by_cases ho : other = 0
  · subst ho
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(offset, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hframed, ⟨δ, hmatched⟩, hlab⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨offset, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(other, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ho, hframed, ⟨δ, hmatched⟩, hlab⟩, rfl⟩

/-- All targets for a tied source state and the second coordinate of a tied
target state; the role phase of the target follows the translation. -/
noncomputable def tiedCatalogue (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool) (source : Labelled M d)
    (pair : (Fin (d + 3) × J) × J) : Finset (Labelled M d) := by
  classical
  exact Finset.univ.biUnion (fun i : Fin (d + 2) =>
    (Finset.univ.biUnion (fun c : Fin (d + 1) =>
      (pairs1T (srcCuts source.1 (phase pair.1)) (tgtBits M (phase (pair.1.1, pair.2)))
        ((action pair.1).trans source.2) (fun δ => action (shift pair.1.1 δ, pair.2)) i c).image
          Prod.snd)) ∪
    (pairs0T (srcCuts source.1 (phase pair.1)) (tgtBits M (phase (pair.1.1, pair.2)))
        ((action pair.1).trans source.2) (fun δ => action (shift pair.1.1 δ, pair.2)) i).image
          Prod.snd)

theorem tiedCatalogue_card (hd : 2 ≤ d) (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool) (source : Labelled M d)
    (pair : (Fin (d + 3) × J) × J) :
    (tiedCatalogue action phase source pair).card ≤ 12 * (d + 3) ^ 3 := by
  classical
  refine le_trans ?_ (count_bound d hd)
  have h := FiniteFibers.bad_union_count (Finset.univ : Finset (Fin (d + 2)))
    (fun i : Fin (d + 2) =>
      (Finset.univ.biUnion (fun c : Fin (d + 1) =>
        (pairs1T (srcCuts source.1 (phase pair.1)) (tgtBits M (phase (pair.1.1, pair.2)))
          ((action pair.1).trans source.2) (fun δ => action (shift pair.1.1 δ, pair.2)) i c).image
            Prod.snd)) ∪
      (pairs0T (srcCuts source.1 (phase pair.1)) (tgtBits M (phase (pair.1.1, pair.2)))
          ((action pair.1).trans source.2) (fun δ => action (shift pair.1.1 δ, pair.2)) i).image
            Prod.snd)
    ((d + 1) * ((4 * d + 6) * 2) + (d + 1) * 2 * (d - 1) * 2) ?_
  · simpa only [tiedCatalogue, Finset.card_univ, Fintype.card_fin] using h
  · intro i _
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · have h1 := FiniteFibers.bad_union_count (Finset.univ : Finset (Fin (d + 1)))
        (fun c : Fin (d + 1) =>
          (pairs1T (srcCuts source.1 (phase pair.1)) (tgtBits M (phase (pair.1.1, pair.2)))
            ((action pair.1).trans source.2) (fun δ => action (shift pair.1.1 δ, pair.2)) i c).image
              Prod.snd)
        ((4 * d + 6) * 2)
        (fun c _ => Finset.card_image_le.trans
          (pairs1T_card (tgtBits_isBit (phase (pair.1.1, pair.2))) _ _ i c))
      simpa only [Finset.card_univ, Fintype.card_fin] using h1
    · exact Finset.card_image_le.trans
        (pairs0T_card hd (tgtBits_isBit (phase (pair.1.1, pair.2))) _ _ i)

theorem mem_tiedCatalogue (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (hphase : ∀ s s' j, phase (s, j) = phase (s', j))
    (source target : Labelled M d) (first second : Fin (d + 3) × J)
    (δ : ZMod M) (hshift : second.1 = shift first.1 δ)
    (hframed : Framed target.1) (omitted other : Fin (d + 2)) (offset : Fin (d + 1))
    (hmatched : Matched (srcCuts source.1 (phase first)) (tgtBits M (phase second))
      omitted other offset target.1 δ)
    (hlab : target.2 ∈ CyclicLabelCount.candidates ((action first).trans source.2)
      (action second) omitted other offset) :
    target ∈ tiedCatalogue action phase source (first, second.2) := by
  classical
  obtain ⟨s', j'⟩ := second
  dsimp only at hshift hmatched hlab ⊢
  subst hshift
  rw [hphase (shift first.1 δ) first.1 j'] at hmatched
  unfold tiedCatalogue
  apply Finset.mem_biUnion.mpr
  refine ⟨omitted, Finset.mem_univ _, ?_⟩
  by_cases ho : other = 0
  · subst ho
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(offset, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hframed, δ, hmatched, hlab⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨offset, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(other, target), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ho, hframed, δ, hmatched, hlab⟩, rfl⟩

noncomputable def neighboursT {α : Type} (background : Fin M → α) (embed : Role (d + 2) → α)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (source : Labelled M d) : Finset (Labelled M d) := by
  classical
  exact (SortedFrameSupply.labelledFrames M d).filter
    (MeetsT background embed action phase source)

variable [Fintype J]

/-- The three families of targets: free target state, free source state,
both tied. -/
noncomputable def cover (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool) (source : Labelled M d) :
    Finset (Labelled M d) := by
  classical
  exact ((Finset.univ : Finset ((Fin (d + 3) × J) × (Bool × J))).biUnion
      (fun p => pairCatalogue action phase source (p.1, (zeroTwo d p.2.1, p.2.2)))) ∪
    ((Finset.univ : Finset ((Bool × J) × (Fin (d + 3) × J))).biUnion
      (fun p => pairCatalogue action phase source ((zeroTwo d p.1.1, p.1.2), p.2))) ∪
    ((Finset.univ : Finset ((Fin (d + 3) × J) × J)).biUnion
      (fun p => tiedCatalogue action phase source p))

theorem free_eq {index : Fin (d + 3) × J} (h : index.1.val = 0 ∨ index.1.val = 2) :
    ∃ b : Bool, index = (zeroTwo d b, index.2) := by
  rcases h with h | h
  · exact ⟨false, Prod.ext (Fin.ext h) rfl⟩
  · exact ⟨true, Prod.ext (Fin.ext h) rfl⟩

theorem intersection_mem {α : Type} [DecidableEq α] (hM : 2 ≤ M) (hdiv : d + 3 ∣ M)
    (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (hphase : ∀ s s' j, phase (s, j) = phase (s', j))
    (source target : Labelled M d)
    (hsource : source ∈ SortedFrameSupply.labelledFrames M d)
    (htarget : target ∈ SortedFrameSupply.labelledFrames M d)
    (hmeet : MeetsT background embed action phase source target) :
    target ∈ cover action phase source := by
  classical
  obtain ⟨first, second, t, t', gap, gap', h1, h2, hcyclic⟩ := hmeet
  obtain ⟨hframed, omitted, other, offset, hmatched, hlab⟩ :=
    meet_witness hM backgroundTest background embed hbackground hembed htb htc action phase
      source target hsource htarget first second t t' gap gap' hcyclic
  unfold cover
  by_cases hf2 : second.1.val = 0 ∨ second.1.val = 2
  · obtain ⟨b, hb⟩ := free_eq hf2
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨(first, (b, second.2)), Finset.mem_univ _, ?_⟩
    dsimp only
    rw [← hb]
    exact mem_pairCatalogue action phase source target first second (t' - t) hframed
      omitted other offset hmatched hlab
  · by_cases hf1 : first.1.val = 0 ∨ first.1.val = 2
    · obtain ⟨b, hb⟩ := free_eq hf1
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨((b, first.2), second), Finset.mem_univ _, ?_⟩
      dsimp only
      rw [← hb]
      exact mem_pairCatalogue action phase source target first second (t' - t) hframed
        omitted other offset hmatched hlab
    · have ht1 : first.1.val = t.val % (d + 3) := by
        rcases h1 with h | h | h
        · exact absurd (Or.inl h) hf1
        · exact absurd (Or.inr h) hf1
        · exact h
      have ht2 : second.1.val = t'.val % (d + 3) := by
        rcases h2 with h | h | h
        · exact absurd (Or.inl h) hf2
        · exact absurd (Or.inr h) hf2
        · exact h
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨(first, second.2), Finset.mem_univ _, ?_⟩
      exact mem_tiedCatalogue action phase hphase source target first second (t' - t)
        (shift_eq hdiv ht1 ht2) hframed omitted other offset hmatched hlab

/-- The degree of the tied envelopes, counted with the source itself. -/
theorem degree_240 {α : Type} [DecidableEq α] (hM : 2 ≤ M) (hd : 2 ≤ d) (hdiv : d + 3 ∣ M)
    (hJ : Fintype.card J ≤ 2 * (d + 3)) (backgroundTest : α → Bool)
    (background : Fin M → α) (embed : Role (d + 2) → α)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (htb : ∀ i, backgroundTest (background i) = true)
    (htc : ∀ c, backgroundTest (embed c) = false)
    (action : Fin (d + 3) × J → Equiv.Perm (Role (d + 2)))
    (phase : Fin (d + 3) × J → Fin (d + 2) → Bool)
    (hphase : ∀ s s' j, phase (s, j) = phase (s', j))
    (source : Labelled M d) (hsource : source ∈ SortedFrameSupply.labelledFrames M d) :
    (neighboursT background embed action phase source).card ≤ 240 * (d + 3) ^ 6 := by
  classical
  have hsub : neighboursT background embed action phase source ⊆ cover action phase source := by
    intro target ht
    obtain ⟨htarget, hmeet⟩ := Finset.mem_filter.mp ht
    exact intersection_mem hM hdiv backgroundTest background embed hbackground hembed htb htc
      action phase hphase source target hsource htarget hmeet
  have h1 := FiniteFibers.bad_union_count
    (Finset.univ : Finset ((Fin (d + 3) × J) × (Bool × J)))
    (fun p => pairCatalogue action phase source (p.1, (zeroTwo d p.2.1, p.2.2)))
    (12 * (d + 3) ^ 3) (fun p _ => pairCatalogue_card hd action phase source _)
  have h2 := FiniteFibers.bad_union_count
    (Finset.univ : Finset ((Bool × J) × (Fin (d + 3) × J)))
    (fun p => pairCatalogue action phase source ((zeroTwo d p.1.1, p.1.2), p.2))
    (12 * (d + 3) ^ 3) (fun p _ => pairCatalogue_card hd action phase source _)
  have h3 := FiniteFibers.bad_union_count
    (Finset.univ : Finset ((Fin (d + 3) × J) × J))
    (fun p => tiedCatalogue action phase source p)
    (12 * (d + 3) ^ 3) (fun p _ => tiedCatalogue_card hd action phase source p)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1 h2 h3
  have hcover : (cover action phase source).card ≤
      (d + 3) * Fintype.card J * (2 * Fintype.card J) * (12 * (d + 3) ^ 3) +
        2 * Fintype.card J * ((d + 3) * Fintype.card J) * (12 * (d + 3) ^ 3) +
        (d + 3) * Fintype.card J * Fintype.card J * (12 * (d + 3) ^ 3) := by
    unfold cover
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)) h3)
  have hsq : Fintype.card J * Fintype.card J ≤ (2 * (d + 3)) * (2 * (d + 3)) :=
    Nat.mul_le_mul hJ hJ
  calc
    (neighboursT background embed action phase source).card ≤
        (cover action phase source).card := Finset.card_le_card hsub
    _ ≤ (d + 3) * Fintype.card J * (2 * Fintype.card J) * (12 * (d + 3) ^ 3) +
        2 * Fintype.card J * ((d + 3) * Fintype.card J) * (12 * (d + 3) ^ 3) +
        (d + 3) * Fintype.card J * Fintype.card J * (12 * (d + 3) ^ 3) := hcover
    _ = 60 * (d + 3) ^ 4 * (Fintype.card J * Fintype.card J) := by ring
    _ ≤ 60 * (d + 3) ^ 4 * ((2 * (d + 3)) * (2 * (d + 3))) := Nat.mul_le_mul_left _ hsq
    _ = 240 * (d + 3) ^ 6 := by ring

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.degree_240
