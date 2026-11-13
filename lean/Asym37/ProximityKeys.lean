import Quantitative.ProximityDeletion

/-!
# Exponent 37: counting proximity equations by their key

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The proximity equation of a pair event depends on the pair only through
the two event types (an event without its right side) and the constant
`rightSide`. `ProximityDeletion.badFiber_scaled_count` charges every pair
event separately with the maximum of the two rank cases. Here the bad
fibre is a union over the distinct keys instead:

* keys with a nonzero guard coefficient: at most `T^2 (2B+1)` keys, each
  bounded by `ProximityPairCount.guard_variable_count`;
* guard-free keys: the equation is `a (q_j - q_l) ≡ b`, so the solution set
  depends only on `(a, j, l, b)`, at most `(2(d-1)^2+1) (d+2)^2 (2B+1)`
  values, each bounded by `ProximityPairCount.labelled_frame_count`.

Here `T = (d+3)(A-1)(d+2)^3(d+1)` is the number of event types and
`B = 14 (d+3)^2 W` bounds `|rightSide|`.
-/

namespace CoefficientTwoPrecision.Asym37

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue ProximitySurvivors ProximityPairCount ProximityDeletion
open NeighbourGeometry StationaryRelations ActiveSlotEvents CatalogueBounds SortedFrameSupply

variable {m d A : Nat}

/-- An event without its bounded right side. -/
abbrev EventType (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  Σ foreign : Neighbour d A hA active, Mobile hA active foreign × (Assignment d × Fin (d + 2))

def eventType {hA : 0 < A} {active : Active d A} (e : Event d A hA active) :
    EventType d A hA active :=
  ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1⟩

noncomputable def typeCoefficient (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active) : Int :=
  weight t.2.2.1 (sharedIndex hA active t.1 t.2.1)

def typeSlot {hA : 0 < A} {active : Active d A} (t : EventType d A hA active) : Fin (d + 2) :=
  t.2.2.2

noncomputable def typeForbidden (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active) : Fin (d + 3) × Fin (d + 2) :=
  ((shared hA active t.1).1, t.2.2.2)

noncomputable def typeGuardCoefficient (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active) (u : Fin (guardNumber d A)) : Int :=
  ∑ i : {i : Fin (d + 2) // i ≠ sharedIndex hA active t.1 t.2.1},
    if guardIndex hA active t.1 t.2.1 i = u then weight t.2.2.1 i.val else 0

noncomputable def typeCross (hA : 0 < A) (active : Active d A)
    (first second : EventType d A hA active) (u : Fin (guardNumber d A)) : Int :=
  typeCoefficient hA active second * typeGuardCoefficient hA active first u -
    typeCoefficient hA active first * typeGuardCoefficient hA active second u

theorem guardCross_eq_type (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (u : Fin (guardNumber d A)) :
    guardCross hA active first second u =
      typeCross hA active (eventType first) (eventType second) u := rfl

/-- The key of a pair event: both event types and the constant. -/
abbrev PairKey (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  EventType d A hA active × EventType d A hA active × Int

noncomputable def pairKey {hA : 0 < A} {active : Active d A}
    (event : PairEvent d A hA active) : PairKey d A hA active :=
  (eventType event.1, eventType event.2.1, rightSide hA active event)

noncomputable def keySolutions (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (key : PairKey d A hA active) :
    Finset (Fiber m d A) := by
  classical
  exact (Finset.univ ×ˢ S).filter (fun p =>
    typeForbidden hA active key.1 ≠ typeForbidden hA active key.2.1 ∧
      Int.ModEq (m : Int)
        (typeCoefficient hA active key.1 * typeCoefficient hA active key.2.1 *
            ((p.2.1 (typeSlot key.1)).val - ((p.2.1 (typeSlot key.2.1)).val : Int)) +
          ∑ u, typeCross hA active key.1 key.2.1 u * (p.1 u).val)
        key.2.2)

/-- `pairSolutions` factors through the key. -/
theorem pairSolutions_eq_key (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (event : PairEvent d A hA active) :
    pairSolutions hA active S event = keySolutions hA active S (pairKey event) := by
  classical
  ext p
  simp only [pairSolutions, keySolutions, Finset.mem_filter]
  exact Iff.rfl

/-- Pair events with the same key have the same solution set. -/
theorem pairSolutions_congr (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (event other : PairEvent d A hA active)
    (h : pairKey event = pairKey other) :
    pairSolutions hA active S event = pairSolutions hA active S other := by
  rw [pairSolutions_eq_key, pairSolutions_eq_key, h]

/-- The number of event types. -/
def typeTotal (d A : Nat) : Nat := (d + 3) * (A - 1) * (d + 2) ^ 3 * (d + 1)

theorem eventType_card (hA : 0 < A) (active : Active d A) :
    Fintype.card (EventType d A hA active) = typeTotal d A := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, mobile_card, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, neighbour_card, Nat.nsmul_eq_mul, typeTotal]
  ring

theorem typeTotal_le (d A : Nat) : typeTotal d A ≤ (d + 3) ^ 3 * width d A := by
  have hI : (d + 3) * (A - 1) ≤ (d + 3) * A := Nat.mul_le_mul_left _ (Nat.sub_le A 1)
  have hp : (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 4 := by
    calc
      (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 3 * (d + 3) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3) (by omega)
      _ = (d + 3) ^ 4 := by ring
  unfold typeTotal width
  calc
    (d + 3) * (A - 1) * (d + 2) ^ 3 * (d + 1) = ((d + 3) * (A - 1)) * ((d + 2) ^ 3 * (d + 1)) := by
      ring
    _ ≤ ((d + 3) * A) * (d + 3) ^ 4 := Nat.mul_le_mul hI hp
    _ = (d + 3) ^ 3 * ((d + 3) ^ 2 * A) := by ring

theorem coefficient_natAbs_le (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (e : Event d A hA active) : (coefficient hA active e).natAbs ≤ d - 1 := by
  unfold coefficient
  rw [weight_abs_formula hd]
  split_ifs <;> omega

/-- The constant of a proximity equation: `|rightSide| ≤ 14 r^2 W`. -/
theorem rightSide_natAbs_le (hd : 3 ≤ d) (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) :
    (rightSide hA active event).natAbs ≤ 14 * (d + 3) ^ 2 * width d A := by
  have hc1 := coefficient_natAbs_le (by omega) hA active event.1
  have hc2 := coefficient_natAbs_le (by omega) hA active event.2.1
  have hP := primary_bound d A hA
  have hG := guard_le d A
  have hW := width_ge d A hA
  set P := primaryOffsetBound d (guardNumber d A) with hPdef
  have hrhs1 : (rhs hA active event.1).natAbs ≤ P := by
    have h := event.1.2.2.2.2.isLt
    unfold rhs
    omega
  have hrhs2 : (rhs hA active event.2.1).natAbs ≤ P := by
    have h := event.2.1.2.2.2.2.isLt
    unfold rhs
    omega
  have hdisp : (displacement hA active event).natAbs ≤ radius d := by
    have h := event.2.2.1.isLt
    unfold displacement
    omega
  have hwind : (winding hA active event).natAbs ≤ 1 := by
    have h := event.2.2.2.isLt
    unfold winding
    omega
  have hshift : (displacement hA active event +
      winding hA active event * (guardNumber d A : Int)).natAbs ≤ radius d + guardNumber d A := by
    have h1 := Int.natAbs_add_le (displacement hA active event)
      (winding hA active event * (guardNumber d A : Int))
    have h2 : (winding hA active event * (guardNumber d A : Int)).natAbs ≤ guardNumber d A := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      simpa using Nat.mul_le_mul_right (guardNumber d A) hwind
    omega
  have hterm1 : (coefficient hA active event.2.1 * rhs hA active event.1).natAbs ≤ (d - 1) * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hc2 hrhs1
  have hterm2 : (coefficient hA active event.1 * rhs hA active event.2.1).natAbs ≤ (d - 1) * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hc1 hrhs2
  have hterm3 : (coefficient hA active event.1 * coefficient hA active event.2.1 *
      (displacement hA active event + winding hA active event * guardNumber d A)).natAbs ≤
      (d - 1) * (d - 1) * (radius d + guardNumber d A) := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul hc1 hc2) hshift
  have hsum : (rightSide hA active event).natAbs ≤
      (d - 1) * P + (d - 1) * P + (d - 1) * (d - 1) * (radius d + guardNumber d A) := by
    unfold rightSide
    have h1 := Int.natAbs_add_le
      (coefficient hA active event.2.1 * rhs hA active event.1 -
        coefficient hA active event.1 * rhs hA active event.2.1)
      (coefficient hA active event.1 * coefficient hA active event.2.1 *
        (displacement hA active event + winding hA active event * guardNumber d A))
    have h2 := Int.natAbs_sub_le
      (coefficient hA active event.2.1 * rhs hA active event.1)
      (coefficient hA active event.1 * rhs hA active event.2.1)
    omega
  have hd1 : d - 1 ≤ d + 3 := by omega
  have hR : radius d ≤ width d A := by
    have hsq : (d + 3) ^ 2 ≤ width d A := by
      have h := Nat.mul_le_mul_left ((d + 3) ^ 2) (show 1 ≤ A from hA)
      simpa [width] using h
    unfold radius
    nlinarith
  have hA1 : (d - 1) * P ≤ (d + 3) * (6 * (d + 3) * width d A) := Nat.mul_le_mul hd1 hP
  have hA2 : (d - 1) * (d - 1) * (radius d + guardNumber d A) ≤
      (d + 3) * (d + 3) * (width d A + width d A) :=
    Nat.mul_le_mul (Nat.mul_le_mul hd1 hd1) (Nat.add_le_add hR hG)
  have he1 : (d + 3) * (6 * (d + 3) * width d A) = 6 * ((d + 3) ^ 2 * width d A) := by ring
  have he2 : (d + 3) * (d + 3) * (width d A + width d A) = 2 * ((d + 3) ^ 2 * width d A) := by ring
  have he3 : 14 * (d + 3) ^ 2 * width d A = 14 * ((d + 3) ^ 2 * width d A) := by ring
  omega

/-- The bound `B` on the constants. -/
def constantBound (d A : Nat) : Nat := 14 * (d + 3) ^ 2 * width d A

/-- The number of keys with a guard coefficient (an upper bound). -/
def guardKeyCount (d A : Nat) : Nat := typeTotal d A ^ 2 * (2 * constantBound d A + 1)

/-- The number of guard-free keys `(a, j, l, b)` (an upper bound). -/
def freeKeyCount (d A : Nat) : Nat :=
  (2 * (d - 1) ^ 2 + 1) * (d + 2) ^ 2 * (2 * constantBound d A + 1)

theorem card_Icc_sym (B : Nat) : (Finset.Icc (-(B : Int)) B).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  omega

theorem card_biUnion_le_mul {α β : Type} [DecidableEq β] (s : Finset α) (t : α → Finset β)
    (b : Nat) (h : ∀ a ∈ s, (t a).card ≤ b) : (s.biUnion t).card ≤ s.card * b := by
  calc
    (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card := Finset.card_biUnion_le
    _ ≤ s.card • b := Finset.sum_le_card_nsmul s _ b h
    _ = s.card * b := by rw [smul_eq_mul]

/-- The bad fibre of one active block, counted by keys. -/
theorem badFiber_card_keys [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (active : Active d A) (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial * (badFiber hA active S).card ≤
      (d - 1).factorial * (guardKeyCount d A *
          (S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2)))) +
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
  -- the bad fibre lies in the two unions
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
  -- guard keys
  have hguard : (Eg.biUnion (pairSolutions hA active S)).card ≤
      guardKeyCount d A * (S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2))) := by
    have heq : Eg.biUnion (pairSolutions hA active S) = (Eg.image pairKey).biUnion (keySolutions hA active S) := by
      ext p
      constructor
      · intro hp
        obtain ⟨e, he, hpe⟩ := Finset.mem_biUnion.mp hp
        refine Finset.mem_biUnion.mpr ⟨pairKey e, Finset.mem_image_of_mem _ he, ?_⟩
        rw [← pairSolutions_eq_key]
        exact hpe
      · intro hp
        obtain ⟨key, hkey, hpk⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hkey
        refine Finset.mem_biUnion.mpr ⟨e, he, ?_⟩
        rw [pairSolutions_eq_key]
        exact hpk
    rw [heq]
    refine (card_biUnion_le_mul _ _ _ ?_).trans (Nat.mul_le_mul_right _ ?_)
    · intro key hkey
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hkey
      rw [← pairSolutions_eq_key]
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp he).2.2
      exact guard_variable_count hm (by omega) hA active S e u hu
    · have hsub : Eg.image pairKey ⊆
          (Finset.univ : Finset (EventType d A hA active)) ×ˢ
            ((Finset.univ : Finset (EventType d A hA active)) ×ˢ Finset.Icc (-(B : Int)) B) := by
        intro key hkey
        obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hkey
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_product.mpr ⟨Finset.mem_univ _, hrs e⟩⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_product, Finset.card_univ, eventType_card,
        card_Icc_sym] at hc
      unfold guardKeyCount
      rw [← hB]
      calc
        (Eg.image pairKey).card ≤ typeTotal d A * (typeTotal d A * (2 * B + 1)) := hc
        _ = typeTotal d A ^ 2 * (2 * B + 1) := by ring
  -- guard-free keys
  let frameSet : Int × Fin (d + 2) × Fin (d + 2) × Int →
      Finset (Labelled (m + guardNumber d A) d) := fun k =>
    (labelledFrames (m + guardNumber d A) d).filter (fun node =>
      Int.ModEq (m : Int) (k.1 * ((node.1 k.2.1).val - ((node.1 k.2.2.1).val : Int))) k.2.2.2)
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
          (PrimaryCatalogue.coefficient_nonzero (by omega) hA active e.1)
          (PrimaryCatalogue.coefficient_nonzero (by omega) hA active e.2.1)
        have hne := distinct_slots_of_guard_free hd hA active e.1 e.2.1 hdist hzero
        have hbound := labelled_frame_count (d := d) m (m + guardNumber d A) hm (by omega) hM hd
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

/-- The second deletion, counted by keys. -/
theorem deleted_keys [NeZero (m + guardNumber d A)]
    (hm : 0 < m) (hM : m + guardNumber d A ≤ 2 * m) (hd : 3 ≤ d) (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d))
    (hS : S ⊆ labelledFrames (m + guardNumber d A) d) :
    (d - 1).factorial *
        ((GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card) ≤
      (A * ((d + 3) * A)) *
        ((d - 1).factorial * (guardKeyCount d A *
            (S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2)))) +
          freeKeyCount d A * frameBound m d A) := by
  classical
  have hbad : (d - 1).factorial * (allBad hA S).card ≤
      (A * ((d + 3) * A)) *
        ((d - 1).factorial * (guardKeyCount d A *
            (S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2)))) +
          freeKeyCount d A * frameBound m d A) := by
    rw [allBad_card, Finset.mul_sum]
    calc
      (∑ active : Active d A, (d - 1).factorial * (badFiber hA active S).card) ≤
          ∑ _active : Active d A, ((d - 1).factorial * (guardKeyCount d A *
              (S.card * (m ^ (guardNumber d A - 1) * (2 * (d - 1) ^ 2)))) +
            freeKeyCount d A * frameBound m d A) := by
        apply Finset.sum_le_sum
        intro active _
        exact badFiber_card_keys hm hM hd hA active S hS
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, ActiveGrid.blocks_card, Nat.nsmul_eq_mul]
  exact (Nat.mul_le_mul_left _ (deleted_le_allBad hA S)).trans hbad

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.pairSolutions_congr
#print axioms CoefficientTwoPrecision.Asym37.rightSide_natAbs_le
#print axioms CoefficientTwoPrecision.Asym37.badFiber_card_keys
#print axioms CoefficientTwoPrecision.Asym37.deleted_keys
