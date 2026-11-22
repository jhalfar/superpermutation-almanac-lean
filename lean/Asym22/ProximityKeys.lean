import Asym22.TD.ProximityDeletion

/-!
# The keys of the proximity equations

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The proximity equation of a pair event depends on the pair only through the two event
types (an event without its right side) and the constant `rightSide`. This file has the
event types, their number `T = (d+3)(A-1)(d+2)^3(d+1) ≤ r^4 W`, and the bound on the
constants. In the exponent-28 batch the constant was bounded by `14 r^2 W`, because the
equations were written in the original cuts of the guards. Here they are written in local
positions modulo `m + G` (`Asym22.LocalPos`), and `|rightSide| ≤ 9 r^3`. More precisely the
constant of a pair of types is at most `(|a| + |a'|) · 2 r^2 + |a| |a'| (4r + 2)`, with `a`, `a'`
the coefficients of the shared controls; `|a|` is `d - 1` for one coefficient assignment in
`d + 2` and `1` otherwise, so the sum of these constants over all pairs of types is of order
`r^2 T^2`, not `r^3 T^2` (`pairBound_sum`). The count itself is in `Asym22.IntervalKeys`.
-/

namespace CoefficientTwoPrecision.Asym22

open TD.GuardCatalogue TD.CandidateSpace LabelledReconstruction TD.PrimaryCatalogue TD.PrimaryRank
open TD.ProximityCatalogue TD.ProximitySurvivors TD.ProximityPairCount TD.ProximityDeletion
open TD.NeighbourGeometry StationaryRelations ActiveSlotEvents TD.CatalogueBounds SortedFrameSupply

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
      Int.ModEq ((m + guardNumber d A : Nat) : Int)
        (typeCoefficient hA active key.1 * typeCoefficient hA active key.2.1 *
            ((p.2.1 (typeSlot key.1)).val - ((p.2.1 (typeSlot key.2.1)).val : Int)) +
          ∑ u, typeCross hA active key.1 key.2.1 u * (TD.LocalPos.localPos (p.1 : Fin (guardNumber d A) → Fin m) u).val)
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

theorem typeTotal_le (d A : Nat) : typeTotal d A ≤ (d + 3) ^ 4 * width d A := by
  have hI : (d + 3) * (A - 1) ≤ (d + 3) * A := Nat.mul_le_mul_left _ (Nat.sub_le A 1)
  have hp : (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 4 := by
    calc
      (d + 2) ^ 3 * (d + 1) ≤ (d + 3) ^ 3 * (d + 3) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3) (by omega)
      _ = (d + 3) ^ 4 := by ring
  unfold typeTotal
  calc
    (d + 3) * (A - 1) * (d + 2) ^ 3 * (d + 1) = ((d + 3) * (A - 1)) * ((d + 2) ^ 3 * (d + 1)) := by
      ring
    _ ≤ ((d + 3) * A) * (d + 3) ^ 4 := Nat.mul_le_mul hI hp
    _ ≤ width d A * (d + 3) ^ 4 := Nat.mul_le_mul_right _ (rowsA_le d A)
    _ = (d + 3) ^ 4 * width d A := by ring

theorem coefficient_natAbs_le (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A)
    (e : Event d A hA active) : (coefficient hA active e).natAbs ≤ d - 1 := by
  unfold coefficient
  rw [weight_abs_formula hd]
  split_ifs <;> omega

/-- The constant of a proximity equation in local positions: `|rightSide| ≤ 9 r^3`. -/
theorem rightSide_natAbs_le (hd : 3 ≤ d) (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) :
    (rightSide hA active event).natAbs ≤ 9 * (d + 3) ^ 3 := by
  have hc1 := coefficient_natAbs_le (by omega) hA active event.1
  have hc2 := coefficient_natAbs_le (by omega) hA active event.2.1
  set P := TD.LocalPos.localOffsetBound d with hPdef
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
  have hterm1 : (coefficient hA active event.2.1 * rhs hA active event.1).natAbs ≤ (d - 1) * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hc2 hrhs1
  have hterm2 : (coefficient hA active event.1 * rhs hA active event.2.1).natAbs ≤ (d - 1) * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hc1 hrhs2
  have hterm3 : (coefficient hA active event.1 * coefficient hA active event.2.1 *
      displacement hA active event).natAbs ≤ (d - 1) * (d - 1) * radius d := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul (Nat.mul_le_mul hc1 hc2) hdisp
  have hsum : (rightSide hA active event).natAbs ≤
      (d - 1) * P + (d - 1) * P + (d - 1) * (d - 1) * radius d := by
    unfold rightSide
    have h1 := Int.natAbs_add_le
      (coefficient hA active event.2.1 * rhs hA active event.1 -
        coefficient hA active event.1 * rhs hA active event.2.1)
      (coefficient hA active event.1 * coefficient hA active event.2.1 *
        displacement hA active event)
    have h2 := Int.natAbs_sub_le
      (coefficient hA active event.2.1 * rhs hA active event.1)
      (coefficient hA active event.1 * rhs hA active event.2.1)
    omega
  have hd1 : d - 1 ≤ d + 3 := by omega
  have hR : radius d ≤ 5 * (d + 3) := by unfold radius; omega
  have hA1 : (d - 1) * P ≤ (d + 3) * (2 * (d + 3) ^ 2) := Nat.mul_le_mul hd1 (le_of_eq hPdef)
  have hA2 : (d - 1) * (d - 1) * radius d ≤ (d + 3) * (d + 3) * (5 * (d + 3)) :=
    Nat.mul_le_mul (Nat.mul_le_mul hd1 hd1) hR
  have he1 : (d + 3) * (2 * (d + 3) ^ 2) = 2 * (d + 3) ^ 3 := by ring
  have he2 : (d + 3) * (d + 3) * (5 * (d + 3)) = 5 * (d + 3) ^ 3 := by ring
  omega

/-- The bound `B` on the constants (it does not depend on the width). -/
def constantBound (d _A : Nat) : Nat := 9 * (d + 3) ^ 3

/-- The coefficient magnitude of an event type (`d - 1` for one assignment in `d + 2`, else `1`). -/
noncomputable def typeAbs (hA : 0 < A) (active : Active d A) (t : EventType d A hA active) : Nat :=
  (typeCoefficient hA active t).natAbs

/-- The constant of a pair of event types: `(|a| + |a'|) · 2 r^2 + |a| |a'| · (4r + 2)`. -/
noncomputable def pairConstant (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active × EventType d A hA active) : Nat :=
  (typeAbs hA active t.1 + typeAbs hA active t.2) * TD.LocalPos.localOffsetBound d +
    typeAbs hA active t.1 * typeAbs hA active t.2 * radius d

/-- The constant of a proximity equation, bounded through the coefficients of its two types. -/
theorem rightSide_natAbs_le_pair (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) :
    (rightSide hA active event).natAbs ≤
      pairConstant hA active (eventType event.1, eventType event.2.1) := by
  set P := TD.LocalPos.localOffsetBound d with hPdef
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
  have hterm1 : (coefficient hA active event.2.1 * rhs hA active event.1).natAbs ≤
      (coefficient hA active event.2.1).natAbs * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ hrhs1
  have hterm2 : (coefficient hA active event.1 * rhs hA active event.2.1).natAbs ≤
      (coefficient hA active event.1).natAbs * P := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ hrhs2
  have hterm3 : (coefficient hA active event.1 * coefficient hA active event.2.1 *
      displacement hA active event).natAbs ≤
      (coefficient hA active event.1).natAbs * (coefficient hA active event.2.1).natAbs *
        radius d := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul_left _ hdisp
  have hsum : (rightSide hA active event).natAbs ≤
      (coefficient hA active event.2.1).natAbs * P + (coefficient hA active event.1).natAbs * P +
        (coefficient hA active event.1).natAbs * (coefficient hA active event.2.1).natAbs *
          radius d := by
    unfold rightSide
    have h1 := Int.natAbs_add_le
      (coefficient hA active event.2.1 * rhs hA active event.1 -
        coefficient hA active event.1 * rhs hA active event.2.1)
      (coefficient hA active event.1 * coefficient hA active event.2.1 *
        displacement hA active event)
    have h2 := Int.natAbs_sub_le
      (coefficient hA active event.2.1 * rhs hA active event.1)
      (coefficient hA active event.1 * rhs hA active event.2.1)
    omega
  have he : pairConstant hA active (eventType event.1, eventType event.2.1) =
      ((coefficient hA active event.1).natAbs + (coefficient hA active event.2.1).natAbs) * P +
        (coefficient hA active event.1).natAbs * (coefficient hA active event.2.1).natAbs *
          radius d := rfl
  rw [he, Nat.add_mul]
  omega

/-- The coefficient magnitudes of all event types add up to `2d/(d+2)` times their number:
for a fixed shared label the assignments contribute `2 d (d + 1)` (Jay's
`fixed_label_abs_sum`). -/
theorem typeAbs_sum (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A) :
    ∑ t : EventType d A hA active, typeAbs hA active t =
      (d + 3) * (A - 1) * ((d + 2) * ((d + 2) * (2 * d * (d + 1)))) := by
  classical
  have hmobile (foreign : Neighbour d A hA active) (mobile : Mobile hA active foreign) :
      (∑ tail : Assignment d × Fin (d + 2), typeAbs hA active ⟨foreign, mobile, tail⟩) =
        (d + 2) * (2 * d * (d + 1)) := by
    rw [Fintype.sum_prod_type]
    change (∑ a : Assignment d, ∑ _s : Fin (d + 2),
      (weight a (sharedIndex hA active foreign mobile)).natAbs) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← Finset.mul_sum, fixed_label_abs_sum hd]
  have hforeign (foreign : Neighbour d A hA active) :
      (∑ pair : Mobile hA active foreign × (Assignment d × Fin (d + 2)),
        typeAbs hA active ⟨foreign, pair⟩) = (d + 2) * ((d + 2) * (2 * d * (d + 1))) := by
    rw [Fintype.sum_prod_type]
    simp_rw [hmobile foreign]
    simp only [Finset.sum_const, Finset.card_univ, mobile_card, smul_eq_mul]
  rw [Fintype.sum_sigma]
  simp_rw [hforeign]
  simp only [Finset.sum_const, Finset.card_univ, neighbour_card, smul_eq_mul]

theorem typeAbs_sum_le (hd : 2 ≤ d) (hA : 0 < A) (active : Active d A) :
    ∑ t : EventType d A hA active, typeAbs hA active t ≤ 2 * typeTotal d A := by
  rw [typeAbs_sum hd hA active]
  unfold typeTotal
  have h : (d + 2) * ((d + 2) * (2 * d * (d + 1))) ≤ 2 * ((d + 2) ^ 3 * (d + 1)) := by
    calc
      (d + 2) * ((d + 2) * (2 * d * (d + 1))) = 2 * ((d + 2) ^ 2 * d * (d + 1)) := by ring
      _ ≤ 2 * ((d + 2) ^ 2 * (d + 2) * (d + 1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
      _ = 2 * ((d + 2) ^ 3 * (d + 1)) := by ring
  calc
    (d + 3) * (A - 1) * ((d + 2) * ((d + 2) * (2 * d * (d + 1)))) ≤
        (d + 3) * (A - 1) * (2 * ((d + 2) ^ 3 * (d + 1))) := Nat.mul_le_mul_left _ h
    _ = 2 * ((d + 3) * (A - 1) * (d + 2) ^ 3 * (d + 1)) := by ring

/-- The interval count of one pair of event types: `4 B + (d - 1)(|a| + |a'|) + 1` values of
one position variable, `B` the constant of the pair. -/
noncomputable def pairBound (hA : 0 < A) (active : Active d A)
    (t : EventType d A hA active × EventType d A hA active) : Nat :=
  4 * pairConstant hA active t +
    (d - 1) * (typeAbs hA active t.1 + typeAbs hA active t.2) + 1

theorem double_sum_formula {ι : Type} [Fintype ι] (a : ι → Nat) (c1 c2 : Nat) :
    ∑ x : ι, ∑ y : ι, (c1 * (a x + a y) + c2 * (a x * a y) + 1) =
      2 * c1 * (Fintype.card ι * ∑ x, a x) + c2 * (∑ x, a x) ^ 2 + Fintype.card ι ^ 2 := by
  have hinner (x : ι) : ∑ y : ι, (c1 * (a x + a y) + c2 * (a x * a y) + 1) =
      c1 * (Fintype.card ι * a x) + c1 * (∑ y, a y) + c2 * (a x * ∑ y, a y) + Fintype.card ι := by
    simp only [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Finset.mul_sum, mul_one]
    ring
  simp_rw [hinner]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The mean interval count of a pair of event types is at most `45 r^2`: the sum over all
pairs is at most `45 r^2 T^2`. (With the largest coefficient for every type it is of order
`r^3 T^2`.) -/
theorem pairBound_sum (hd : 3 ≤ d) (hA : 0 < A) (active : Active d A) :
    ∑ t : EventType d A hA active × EventType d A hA active, pairBound hA active t ≤
      45 * (d + 3) ^ 2 * typeTotal d A ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  have hterm (x y : EventType d A hA active) : pairBound hA active (x, y) =
      (4 * TD.LocalPos.localOffsetBound d + (d - 1)) * (typeAbs hA active x + typeAbs hA active y) +
        4 * radius d * (typeAbs hA active x * typeAbs hA active y) + 1 := by
    unfold pairBound pairConstant
    ring
  simp_rw [hterm]
  rw [double_sum_formula, eventType_card]
  have hs := typeAbs_sum_le (by omega) hA active
  set s := ∑ x : EventType d A hA active, typeAbs hA active x with hsdef
  set T := typeTotal d A with hTdef
  set c1 := 4 * TD.LocalPos.localOffsetBound d + (d - 1) with hc1
  have h1 : T * s ≤ T * (2 * T) := Nat.mul_le_mul_left _ hs
  have h2 : s ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left hs 2
  have hX : 6 * (d + 3) ≤ (d + 3) ^ 2 := by nlinarith
  have hc : 4 * c1 + 16 * radius d + 1 ≤ 45 * (d + 3) ^ 2 := by
    rw [hc1]
    unfold TD.LocalPos.localOffsetBound radius
    omega
  calc
    2 * c1 * (T * s) + 4 * radius d * s ^ 2 + T ^ 2 ≤
        2 * c1 * (T * (2 * T)) + 4 * radius d * (2 * T) ^ 2 + T ^ 2 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ h1)
        (Nat.mul_le_mul_left _ h2)) _
    _ = (4 * c1 + 16 * radius d + 1) * T ^ 2 := by ring
    _ ≤ 45 * (d + 3) ^ 2 * T ^ 2 := Nat.mul_le_mul_right _ hc

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

end CoefficientTwoPrecision.Asym22

#print axioms CoefficientTwoPrecision.Asym22.pairSolutions_congr
#print axioms CoefficientTwoPrecision.Asym22.rightSide_natAbs_le
#print axioms CoefficientTwoPrecision.Asym22.rightSide_natAbs_le_pair
#print axioms CoefficientTwoPrecision.Asym22.pairBound_sum
