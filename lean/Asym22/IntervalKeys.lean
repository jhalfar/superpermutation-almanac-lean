import Asym33.IntervalCount
import Asym22.ProximityKeys

/-!
# The proximity deletion counted once per pair of event types

Addition to Jay Pantone's quantitative development (release 9ccbe66), on top of
`ProximityKeys`. For a fixed pair of event types the linear form of the proximity equation
is the same for all constants `c`, `|c| ≤ B`; only the constant changes. So the union over
the constants is the set where the form lands in the interval `[-B, B]`, and
`IntervalCount.linear_interval_count` bounds it by `4B + |γ| + 1` values of one variable
(`γ` its coefficient).

New in the exponent-22 batch: the form is in the local positions of the guards modulo
`m + G` (`Asym22.LocalPos`), where `B ≤ 9 r^3` instead of `14 r^2 W`; `B` is taken for each
pair of types from the two coefficients of the shared controls, and the counts are summed over
the pairs, which gives `45 r^2` per pair on average (`ProximityKeys.pairBound_sum`). A guard background is
sent to its position tuple, which is injective, and the position tuples that satisfy the
condition are counted among all `(m + G)^G` tuples. The guard-free part counts frames, as in
the earlier batches, with the congruence modulo `m + G`.
-/

namespace CoefficientTwoPrecision.Asym22

open CoefficientTwoPrecision.Asym33

open TD.GuardCatalogue TD.CandidateSpace LabelledReconstruction TD.PrimaryCatalogue TD.PrimaryRank
open TD.ProximityCatalogue TD.ProximitySurvivors TD.ProximityPairCount TD.ProximityDeletion
open TD.NeighbourGeometry StationaryRelations ActiveSlotEvents TD.CatalogueBounds SortedFrameSupply

variable {m d A : Nat}

/-- The frame part of the linear form of a pair of event types. -/
noncomputable def typeFrameTerm (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active × EventType d A hA active)
    (q : Fin (d + 2) → Fin (m + guardNumber d A)) : Int :=
  typeCoefficient hA active t.1 * typeCoefficient hA active t.2 *
    ((q (typeSlot t.1)).val - ((q (typeSlot t.2)).val : Int))

/-- All candidates (in one fibre) whose form for the type pair `t` lands in `[-B, B]`. -/
noncomputable def typeSolutions (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (t : EventType d A hA active × EventType d A hA active) : Finset (Fiber m d A) := by
  classical
  exact (Finset.univ ×ˢ S).filter (fun p =>
    typeForbidden hA active t.1 ≠ typeForbidden hA active t.2 ∧
      ∃ c : Int, -((pairConstant hA active t : Nat) : Int) ≤ c ∧
        c < -((pairConstant hA active t : Nat) : Int) +
          ((2 * pairConstant hA active t + 1 : Nat) : Int) ∧
        Int.ModEq ((m + guardNumber d A : Nat) : Int)
          (typeFrameTerm hA active t p.2.1 +
            ∑ u, typeCross hA active t.1 t.2 u * (TD.LocalPos.localPos (p.1 : Fin (guardNumber d A) → Fin m) u).val) c)

/-- The mean number of values of one position variable per pair of event types
(`ProximityKeys.pairBound_sum`). -/
def typeBound (d _A : Nat) : Nat := 45 * (d + 3) ^ 2

theorem interval_factor_le (k B D : Nat) (hk : 1 ≤ k) (hkD : k ≤ D) :
    (k + 1) * ((2 * B + 1 - 1) / k + 1) ≤ 4 * B + D + 1 := by
  have hq := Nat.mul_div_le (2 * B) k
  have hsub : 2 * B + 1 - 1 = 2 * B := by omega
  rw [hsub]
  set q := 2 * B / k
  have h1 : (k + 1) * q ≤ 2 * (k * q) := by nlinarith
  have h2 : (k + 1) * (q + 1) = (k + 1) * q + (k + 1) := by ring
  rw [h2]
  have : k * q ≤ 2 * B := by simpa [mul_comm] using hq
  omega

theorem typeSolutions_card (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (e : PairEvent d A hA active)
    (u : Fin (guardNumber d A)) (hu : guardCross hA active e.1 e.2.1 u ≠ 0) :
    (typeSolutions hA active S (eventType e.1, eventType e.2.1)).card ≤
      S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) *
        pairBound hA active (eventType e.1, eventType e.2.1)) := by
  classical
  set t : EventType d A hA active × EventType d A hA active := (eventType e.1, eventType e.2.1)
  set B := pairConstant hA active t with hB
  have hu' : typeCross hA active t.1 t.2 u ≠ 0 := by
    rw [← guardCross_eq_type]; exact hu
  have habs : (typeCross hA active t.1 t.2 u).natAbs ≤
      (d - 1) * (typeAbs hA active t.1 + typeAbs hA active t.2) := by
    rw [← guardCross_eq_type]
    have h1 := coefficient_abs hd hA active e.1 u
    have h2 := coefficient_abs hd hA active e.2.1 u
    have h3 := Int.natAbs_sub_le
      (coefficient hA active e.2.1 * guardCoefficient hA active e.1 u)
      (coefficient hA active e.1 * guardCoefficient hA active e.2.1 u)
    simp only [Int.natAbs_mul] at h3
    have ha : typeAbs hA active t.1 = (coefficient hA active e.1).natAbs := rfl
    have hb : typeAbs hA active t.2 = (coefficient hA active e.2.1).natAbs := rfl
    have h4 := Nat.mul_le_mul_left (coefficient hA active e.2.1).natAbs h1
    have h5 := Nat.mul_le_mul_left (coefficient hA active e.1).natAbs h2
    rw [ha, hb]
    unfold guardCross
    nlinarith
  have hk1 : 1 ≤ (typeCross hA active t.1 t.2 u).natAbs := Int.natAbs_pos.mpr hu'
  apply FiniteFibers.card_le_of_fiber_bound (typeSolutions hA active S t) S Prod.snd
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro node _
    let lo : Int := -(B : Int) - typeFrameTerm hA active t node.1
    let T := Finset.univ.filter (fun x : Fin (guardNumber d A) → Fin (m + guardNumber d A) =>
      ∃ c : Int, lo ≤ c ∧ c < lo + ((2 * B + 1 : Nat) : Int) ∧
        Int.ModEq ((m + guardNumber d A : Nat) : Int)
          (∑ v, typeCross hA active t.1 t.2 v * (x v).val) c)
    let F := (typeSolutions hA active S t).filter (fun p => p.2 = node)
    have hmap : Set.MapsTo (fun p : Fiber m d A =>
        TD.LocalPos.localPos (p.1 : Fin (guardNumber d A) → Fin m)) F T := by
      intro p hp
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, _, c, hc1, hc2, hc⟩ := Finset.mem_filter.mp hp
      rw [he] at hc
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c - typeFrameTerm hA active t node.1,
        by simp only [lo]; linarith, by simp only [lo]; linarith, ?_⟩
      have := hc.sub_right (typeFrameTerm hA active t node.1)
      simpa using this
    have hinj : (F : Set (Fiber m d A)).InjOn
        (fun p => TD.LocalPos.localPos (p.1 : Fin (guardNumber d A) → Fin m)) := by
      intro p hp q hq he
      apply Prod.ext
      · exact DFunLike.coe_injective (TD.LocalPos.localPos_injective he)
      · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hcount := linear_interval_count (m + guardNumber d A) (guardNumber d A) (by omega)
      (typeCross hA active t.1 t.2) lo (2 * B + 1) u hu'
    have hfac := interval_factor_le (typeCross hA active t.1 t.2 u).natAbs B
      ((d - 1) * (typeAbs hA active t.1 + typeAbs hA active t.2)) hk1 habs
    calc
      F.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap hinj
      _ ≤ (m + guardNumber d A) ^ (guardNumber d A - 1) *
          ((typeCross hA active t.1 t.2 u).natAbs + 1) *
          ((2 * B + 1 - 1) / (typeCross hA active t.1 t.2 u).natAbs + 1) := by
        convert hcount using 2
      _ = (m + guardNumber d A) ^ (guardNumber d A - 1) *
          (((typeCross hA active t.1 t.2 u).natAbs + 1) *
          ((2 * B + 1 - 1) / (typeCross hA active t.1 t.2 u).natAbs + 1)) := by ring
      _ ≤ (m + guardNumber d A) ^ (guardNumber d A - 1) * pairBound hA active t := by
        apply Nat.mul_le_mul_left
        exact hfac

/-- The bad fibre of one active block, the guard part counted by type pairs. -/
theorem badFiber_card_types [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial * (badFiber hA active S).card ≤
      (d - 1).factorial * (typeTotal d A ^ 2 *
          (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A))) +
        freeKeyCount d A * frameBound m d A := by
  classical
  set B := constantBound d A with hB
  let Eg := (Finset.univ : Finset (PairEvent d A hA active)).filter (fun e =>
    forbiddenPair hA active e.1 ≠ forbiddenPair hA active e.2.1 ∧
      ∃ u, guardCross hA active e.1 e.2.1 u ≠ 0)
  let Ef := (Finset.univ : Finset (PairEvent d A hA active)).filter (fun e =>
    forbiddenPair hA active e.1 ≠ forbiddenPair hA active e.2.1 ∧
      ∀ u, guardCross hA active e.1 e.2.1 u = 0)
  have hrs (e : PairEvent d A hA active) : rightSide hA active e ∈ Finset.Icc (-(B : Int)) B := by
    have h := rightSide_natAbs_le hd hA active e
    rw [Finset.mem_Icc]
    rw [hB, constantBound]
    omega
  have hsplit : badFiber hA active S ⊆ Eg.biUnion (pairSolutions hA active S) ∪ Ef.biUnion (pairSolutions hA active S) := by
    intro p hp
    unfold badFiber at hp
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    have hdist := (Finset.mem_filter.mp hpe).2.1
    by_cases hz : ∃ u, guardCross hA active e.1 e.2.1 u ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist, hz⟩, hpe⟩)
    · push Not at hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist, hz⟩, hpe⟩)
  -- guard part: one interval count per pair of event types, summed over the pairs
  let typePair : PairEvent d A hA active → EventType d A hA active × EventType d A hA active :=
    fun e => (eventType e.1, eventType e.2.1)
  have hguard : (Eg.biUnion (pairSolutions hA active S)).card ≤
      typeTotal d A ^ 2 * (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A)) := by
    have hsub : Eg.biUnion (pairSolutions hA active S) ⊆
        (Eg.image typePair).biUnion (typeSolutions hA active S) := by
      intro p hp
      obtain ⟨e, he, hpe⟩ := Finset.mem_biUnion.mp hp
      refine Finset.mem_biUnion.mpr ⟨typePair e, Finset.mem_image_of_mem _ he, ?_⟩
      rw [pairSolutions_eq_key] at hpe
      obtain ⟨hbase, hdist, heq⟩ := Finset.mem_filter.mp hpe
      have hc : (rightSide hA active e).natAbs ≤ pairConstant hA active (typePair e) :=
        rightSide_natAbs_le_pair hA active e
      refine Finset.mem_filter.mpr ⟨hbase, hdist, rightSide hA active e, ?_, ?_, heq⟩
      · omega
      · push_cast
        omega
    have hsum : ((Eg.image typePair).biUnion (typeSolutions hA active S)).card ≤
        ∑ t ∈ Eg.image typePair,
          S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * pairBound hA active t) := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
      intro t ht
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp he).2.2
      exact typeSolutions_card hm (by omega) hA active S e u hu
    have hall : (∑ t ∈ Eg.image typePair,
          S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * pairBound hA active t)) ≤
        ∑ t : EventType d A hA active × EventType d A hA active,
          S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * pairBound hA active t) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have htot := pairBound_sum hd hA active
    calc
      (Eg.biUnion (pairSolutions hA active S)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := hsum
      _ ≤ _ := hall
      _ = S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) *
          ∑ t : EventType d A hA active × EventType d A hA active, pairBound hA active t) := by
        simp only [← Finset.mul_sum]
      _ ≤ S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) *
          (45 * (d + 3) ^ 2 * typeTotal d A ^ 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ htot)
      _ = typeTotal d A ^ 2 *
          (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A)) := by
        unfold typeBound
        ring
  -- guard-free part: as in ProximityKeys.badFiber_card_keys
  let frameSet : Int × Fin (d + 2) × Fin (d + 2) × Int →
      Finset (Labelled (m + guardNumber d A) d) := fun k =>
    (labelledFrames (m + guardNumber d A) d).filter (fun node =>
      Int.ModEq ((m + guardNumber d A : Nat) : Int) (k.1 * ((node.1 k.2.1).val - ((node.1 k.2.2.1).val : Int))) k.2.2.2)
  let freeKey : PairEvent d A hA active → Int × Fin (d + 2) × Fin (d + 2) × Int := fun e =>
    (coefficient hA active e.1 * coefficient hA active e.2.1, slot hA active e.1,
      slot hA active e.2.1, rightSide hA active e)
  have hfreeSub : Ef.biUnion (pairSolutions hA active S) ⊆ (Ef.image freeKey).biUnion
      (fun k => (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ frameSet k) := by
    intro p hp
    obtain ⟨e, he, hpe⟩ := Finset.mem_biUnion.mp hp
    have hzero := (Finset.mem_filter.mp he).2.2
    obtain ⟨hbase, _, heq⟩ := Finset.mem_filter.mp hpe
    refine Finset.mem_biUnion.mpr ⟨freeKey e, Finset.mem_image_of_mem _ he, ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact hS (Finset.mem_product.mp hbase).2
    · exact (equation_guard_free hA active p.1 p.2.1 e hzero).mp heq
  have hfree : (d - 1).factorial * (Ef.biUnion (pairSolutions hA active S)).card ≤ freeKeyCount d A * frameBound m d A := by
    have hc1 := Nat.mul_le_mul_left (d - 1).factorial (Finset.card_le_card hfreeSub)
    have hc2 : (d - 1).factorial * ((Ef.image freeKey).biUnion
        (fun k => (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ frameSet k)).card ≤
        (Ef.image freeKey).card * frameBound m d A := by
      have hb := card_biUnion_le_mul (Ef.image freeKey)
        (fun k => (Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ frameSet k)
        (frameBound m d A / (d - 1).factorial) ?_
      · have hdvd : (d - 1).factorial ∣ frameBound m d A := by
          unfold frameBound
          apply Dvd.dvd.mul_right
          exact Dvd.dvd.mul_left (Nat.factorial_dvd_factorial (by omega)) _
        calc
          (d - 1).factorial * ((Ef.image freeKey).biUnion _).card ≤
              (d - 1).factorial * ((Ef.image freeKey).card *
                (frameBound m d A / (d - 1).factorial)) := Nat.mul_le_mul_left _ hb
          _ = (Ef.image freeKey).card * ((d - 1).factorial *
                (frameBound m d A / (d - 1).factorial)) := by ring
          _ = (Ef.image freeKey).card * frameBound m d A := by
            rw [Nat.mul_div_cancel' hdvd]
      · intro k hk
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨hdist, hzero⟩ := (Finset.mem_filter.mp he).2
        have ha : coefficient hA active e.1 * coefficient hA active e.2.1 ≠ 0 := mul_ne_zero
          (TD.PrimaryCatalogue.coefficient_nonzero (by omega) hA active e.1)
          (TD.PrimaryCatalogue.coefficient_nonzero (by omega) hA active e.2.1)
        have hne := distinct_slots_of_guard_free hd hA active e.1 e.2.1 hdist hzero
        have hbound := labelled_frame_count (d := d) (m + guardNumber d A) (m + guardNumber d A)
          (by omega) (by omega) (by omega) hd
          (coefficient hA active e.1 * coefficient hA active e.2.1) ha
          (slot hA active e.1) (slot hA active e.2.1) hne (rightSide hA active e)
        have habs : (coefficient hA active e.1 * coefficient hA active e.2.1).natAbs ≤
            (d - 1) ^ 2 := by
          rw [Int.natAbs_mul, pow_two]
          exact Nat.mul_le_mul (coefficient_natAbs_le (by omega) hA active e.1)
            (coefficient_natAbs_le (by omega) hA active e.2.1)
        have hsmall : (d - 1).factorial * (frameSet (freeKey e)).card ≤ (d + 3).factorial *
            ((d + 1) * d * ((m + guardNumber d A) ^ (d - 1) * (2 * (d - 1) ^ 2))) :=
          hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 habs))))
        have hcard : ((Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ
            frameSet (freeKey e)).card =
            m.descFactorial (guardNumber d A) * (frameSet (freeKey e)).card := by
          simp only [Finset.card_product, Finset.card_univ, Fintype.card_embedding_eq,
            Fintype.card_fin]
        rw [hcard]
        apply (Nat.le_div_iff_mul_le (Nat.factorial_pos _)).2
        have h := Nat.mul_le_mul_left (m.descFactorial (guardNumber d A)) hsmall
        unfold frameBound
        calc
          m.descFactorial (guardNumber d A) * (frameSet (freeKey e)).card * (d - 1).factorial =
              m.descFactorial (guardNumber d A) *
                ((d - 1).factorial * (frameSet (freeKey e)).card) := by ring
          _ ≤ _ := h
          _ = _ := by ring
    have hc3 : (Ef.image freeKey).card ≤ freeKeyCount d A := by
      have hsub : Ef.image freeKey ⊆
          Finset.Icc (-(((d - 1) ^ 2 : Nat) : Int)) (((d - 1) ^ 2 : Nat) : Int) ×ˢ
            ((Finset.univ : Finset (Fin (d + 2))) ×ˢ ((Finset.univ : Finset (Fin (d + 2))) ×ˢ
              Finset.Icc (-(B : Int)) B)) := by
        intro k hk
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hk
        have habs : (coefficient hA active e.1 * coefficient hA active e.2.1).natAbs ≤
            (d - 1) ^ 2 := by
          rw [Int.natAbs_mul, pow_two]
          exact Nat.mul_le_mul (coefficient_natAbs_le (by omega) hA active e.1)
            (coefficient_natAbs_le (by omega) hA active e.2.1)
        refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_product.mpr ⟨Finset.mem_univ _, hrs e⟩⟩⟩
        change coefficient hA active e.1 * coefficient hA active e.2.1 ∈ Finset.Icc _ _
        rw [Finset.mem_Icc]
        omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
        Fintype.card_fin, card_Icc_sym, card_Icc_sym] at hc
      unfold freeKeyCount
      rw [← hB]
      calc
        (Ef.image freeKey).card ≤ (2 * (d - 1) ^ 2 + 1) * ((d + 2) * ((d + 2) * (2 * B + 1))) := hc
        _ = (2 * (d - 1) ^ 2 + 1) * (d + 2) ^ 2 * (2 * B + 1) := by ring
    calc
      (d - 1).factorial * (Ef.biUnion (pairSolutions hA active S)).card ≤ _ := hc1
      _ ≤ (Ef.image freeKey).card * frameBound m d A := hc2
      _ ≤ freeKeyCount d A * frameBound m d A := Nat.mul_le_mul_right _ hc3
  have htotal := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have h1 := Nat.mul_le_mul_left (d - 1).factorial htotal
  have h2 := Nat.mul_le_mul_left (d - 1).factorial hguard
  rw [Nat.mul_add] at h1
  omega

/-- The second deletion, the guard part counted by type pairs. -/
theorem deleted_types [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial *
        ((TD.GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card) ≤
      (A * TD.tdQ (d + 3) A) *
        ((d - 1).factorial * (typeTotal d A ^ 2 *
            (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A))) +
          freeKeyCount d A * frameBound m d A) := by
  classical
  have hbad : (d - 1).factorial * (allBad hA S).card ≤
      (A * TD.tdQ (d + 3) A) *
        ((d - 1).factorial * (typeTotal d A ^ 2 *
            (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A))) +
          freeKeyCount d A * frameBound m d A) := by
    rw [allBad_card, Finset.mul_sum]
    calc
      (∑ active : Active d A, (d - 1).factorial * (badFiber hA active S).card) ≤
          ∑ _active : Active d A, ((d - 1).factorial * (typeTotal d A ^ 2 *
              (S.card * ((m + guardNumber d A) ^ (guardNumber d A - 1) * typeBound d A))) +
            freeKeyCount d A * frameBound m d A) := by
        apply Finset.sum_le_sum
        intro active _
        exact badFiber_card_types hm hM hd hA active S hS
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, TD.ActiveGrid.blocks_card, Nat.nsmul_eq_mul]
  exact (Nat.mul_le_mul_left _ (deleted_le_allBad hA S)).trans hbad

end CoefficientTwoPrecision.Asym22

#print axioms CoefficientTwoPrecision.Asym22.typeSolutions_card
#print axioms CoefficientTwoPrecision.Asym22.badFiber_card_types
#print axioms CoefficientTwoPrecision.Asym22.deleted_types
