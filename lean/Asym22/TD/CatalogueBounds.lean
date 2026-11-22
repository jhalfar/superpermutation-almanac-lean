import Asym22.TD.PrimaryCatalogue
import Quantitative.ConstructionParameters

/-!
Copy of Jay Pantone's `Quantitative/CatalogueBounds.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.CatalogueBounds`, imports of the copied modules
redirected to `Asym22.TD`. Changed: `width d A = (d+3) tdQ (d+3) A` (the
number of controls) in place of `(d+3)^2 A`. Since only `(d+3) A ≤ W` and
`A ≤ tdQ` hold now, the guard-event, primary-type and occurrence bounds carry
one more factor `d+3` and the proximity-type bound two; Jay's `source_width`
(his `sourceA`) is dropped. The proofs are his with these steps added.

Changed for the exponent-22 batch (November 2026): the right sides of the relations
range over `2 * localOffsetBound d + 1 ≤ 5 r^2` values (local positions) instead of about
`13 r W`; the guard-event bound is `5 r^3 W^2` and the occurrence bound `20 r^6 W`.

# Polynomial bounds for the actual finite collision catalogues

The catalogues retain all coefficient assignments and all bounded right
sides. These bounds specialize their exact finite cardinalities to the
width W = r q of the transversal design. The constants match the global deletion estimates.
-/

namespace CoefficientTwoPrecision.TD.CatalogueBounds

open GuardCatalogue GuardEvents ActiveSlotEvents

def width (d A : Nat) : Nat := (d + 3) * tdQ (d + 3) A

theorem width_ge (d A : Nat) (_hA : 0 < A) : d + 3 ≤ width d A := by
  unfold width
  exact Nat.le_mul_of_pos_right _ (tdQ_pos _ _)

/-- A block's neighbour count `(d+3)(A-1)` is below `(d+3) A ≤ W`. -/
theorem rowsA_le (d A : Nat) : (d + 3) * A ≤ width d A := by
  unfold width
  exact Nat.mul_le_mul_left _ (le_tdQ_right _ _)

theorem rows_le (d A : Nat) : (d + 3) ^ 2 ≤ width d A := by
  unfold width
  rw [pow_two]
  exact Nat.mul_le_mul_left _ (le_tdQ_left _ _)

theorem guard_le (d A : Nat) : guardNumber d A ≤ width d A := by
  unfold guardNumber width
  exact Nat.sub_le _ _

/-- The constants of one relation: `2 · 2 r^2 + 1 ≤ 5 r^2`. -/
theorem local_cells (d : Nat) : 2 * LocalPos.localOffsetBound d + 1 ≤ 5 * (d + 3) ^ 2 := by
  unfold LocalPos.localOffsetBound
  have h : 1 ≤ (d + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

theorem guard_event_bound (d A : Nat) (_hA : 0 < A) :
    GuardCatalogue.eventCount d A ≤ 5 * (d + 3) ^ 3 * width d A ^ 2 := by
  have hp : (d + 2) * (d + 1) ≤ (d + 3) ^ 2 := by nlinarith
  have hAq : A * tdQ (d + 3) A ≤ tdQ (d + 3) A * tdQ (d + 3) A :=
    Nat.mul_le_mul_right _ (le_tdQ_right _ _)
  unfold GuardCatalogue.eventCount
  calc
    A * tdQ (d + 3) A * (d + 3) * ((d + 2) * (d + 1)) *
        (2 * LocalPos.localOffsetBound d + 1) ≤
      (A * tdQ (d + 3) A * (d + 3) * (d + 3) ^ 2) * (5 * (d + 3) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (local_cells d)
    _ ≤ (tdQ (d + 3) A * tdQ (d + 3) A * (d + 3) * (d + 3) ^ 2) * (5 * (d + 3) ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hAq))
    _ = 5 * (d + 3) ^ 3 * width d A ^ 2 := by unfold width; ring

theorem occurrence_bound_local (d A : Nat) (_hA : 0 < A) :
    PrimaryCatalogue.occurrenceBound d A ≤ 20 * (d + 3) ^ 6 * width d A := by
  have hI : (d + 3) * (A - 1) ≤ width d A :=
    (Nat.mul_le_mul_left _ (Nat.sub_le A 1)).trans (rowsA_le d A)
  have hpair : d * (d + 1) ≤ (d + 3) ^ 2 := by nlinarith
  have hp : (d + 2) ^ 2 * (d * (d + 1)) ≤ (d + 3) ^ 4 := by
    calc
      (d + 2) ^ 2 * (d * (d + 1)) ≤ (d + 3) ^ 2 * (d + 3) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) hpair
      _ = (d + 3) ^ 4 := by ring
  unfold PrimaryCatalogue.occurrenceBound
  calc
    4 * ((d + 3) * (A - 1)) * (d + 2) ^ 2 * d * (d + 1) *
        (2 * LocalPos.localOffsetBound d + 1) =
      4 * (((d + 3) * (A - 1)) * ((d + 2) ^ 2 * (d * (d + 1)))) *
        (2 * LocalPos.localOffsetBound d + 1) := by ring
    _ ≤ (4 * (width d A * (d + 3) ^ 4)) * (5 * (d + 3) ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.mul_le_mul hI hp)) (local_cells d)
    _ = 20 * (d + 3) ^ 6 * width d A := by ring

/-- The occurrence bound in the form used by the row count (`52 r^5 W^2`, as in the
exponent-28 batch; it is weaker than `occurrence_bound_local` because `r ≤ W`). -/
theorem occurrence_bound (d A : Nat) (hA : 0 < A) :
    PrimaryCatalogue.occurrenceBound d A ≤ 52 * (d + 3) ^ 5 * width d A ^ 2 := by
  have h := occurrence_bound_local d A hA
  have hW := width_ge d A hA
  calc
    PrimaryCatalogue.occurrenceBound d A ≤ 20 * (d + 3) ^ 6 * width d A := h
    _ = 20 * (d + 3) ^ 5 * width d A * (d + 3) := by ring
    _ ≤ 20 * (d + 3) ^ 5 * width d A * width d A := Nat.mul_le_mul_left _ hW
    _ = 20 * (d + 3) ^ 5 * width d A ^ 2 := by ring
    _ ≤ 52 * (d + 3) ^ 5 * width d A ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))

end CoefficientTwoPrecision.TD.CatalogueBounds

#print axioms CoefficientTwoPrecision.TD.CatalogueBounds.guard_event_bound
#print axioms CoefficientTwoPrecision.TD.CatalogueBounds.occurrence_bound
