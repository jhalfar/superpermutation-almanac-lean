import Asym22.TD.PrimaryRank

/-!
Copy of Jay Pantone's `Quantitative/ProximityCatalogue.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.ProximityCatalogue`, imports of the copied modules
redirected to `Asym22.TD`. Changed for the exponent-22 batch (November 2026): the events
are congruences modulo `m + G` in the local positions of the guards, so the proximity
equation has no wrap term; `rightSide` is `a' b - a b' + a a' delta`. The wrap index of a
pair event is kept in the type and no longer enters the equation.

# Eliminating time from two nearby actual events

The circle has length m+G, whereas guard variables are counted modulo m.
Consequently a wrap of the time interval contributes G to the equation.
The finite catalogue records both the signed short displacement and this
wrap. Its entries with distinct forbidden pairs have either a nonzero
guard coefficient or two distinct current stationary slots.
-/

namespace CoefficientTwoPrecision.TD.ProximityCatalogue

open GuardCatalogue NeighbourGeometry PrimaryCatalogue PrimaryRank

variable {d A : Nat}

def radius (d : Nat) : Nat := 4 * (d + 3) + 2

noncomputable def forbiddenPair (hA : 0 < A) (active : Active d A)
    (event : Event d A hA active) : Fin (d + 3) × Fin (d + 2) :=
  ((shared hA active event.1).1, slot hA active event)

abbrev PairEvent (d A : Nat) (hA : 0 < A) (active : Active d A) :=
  Event d A hA active × Event d A hA active × Fin (2 * radius d + 1) × Fin 3

def displacement (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) : Int := event.2.2.1.val - (radius d : Int)

def winding (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) : Int := (event.2.2.2.val : Int) - 1

noncomputable def rightSide (hA : 0 < A) (active : Active d A)
    (event : PairEvent d A hA active) : Int :=
  coefficient hA active event.2.1 * rhs hA active event.1 -
    coefficient hA active event.1 * rhs hA active event.2.1 +
    coefficient hA active event.1 * coefficient hA active event.2.1 *
      displacement hA active event

def Close {M : Nat} (S : Nat) (first second : Fin M) : Prop :=
  ∃ delta : Int, delta.natAbs ≤ S ∧
    Int.ModEq (M : Int) ((second.val : Int) - first.val) delta

theorem close_winding {M S : Nat} (hS : S < M) (first second : Fin M)
    (hclose : Close S first second) :
    ∃ delta sigma : Int, delta.natAbs ≤ S ∧ sigma.natAbs ≤ 1 ∧
      (second.val : Int) - first.val = delta + sigma * M := by
  obtain ⟨delta, hd, hmod⟩ := hclose
  obtain ⟨sigma, hs⟩ := hmod.symm.dvd
  have he : (second.val : Int) - first.val = delta + sigma * M := by
    nlinarith only [hs]
  have hfirst := first.isLt
  have hsecond := second.isLt
  have hM : (0 : Int) < M := by omega
  have hdlo : -(M : Int) < delta := by omega
  have hdhi : delta < (M : Int) := by omega
  have hlo : -2 < sigma := by
    by_contra hn
    have hsle : sigma ≤ -2 := by omega
    nlinarith
  have hhi : sigma < 2 := by
    by_contra hn
    have hsge : 2 ≤ sigma := by omega
    nlinarith
  exact ⟨delta, sigma, hd, by omega, he⟩

theorem pairEvent_card (hA : 0 < A) (active : Active d A) :
    Fintype.card (PairEvent d A hA active) =
      3 * (2 * radius d + 1) * (typeCount d A) ^ 2 := by
  simp only [PairEvent, Fintype.card_prod, PrimaryCatalogue.event_card, Fintype.card_fin]
  ring

theorem cross_sum {m : Nat} (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (x : Fin (guardNumber d A) → Fin m) :
    (∑ u, guardCross hA active first second u * (x u).val) =
      coefficient hA active second * guardSum hA active first x -
        coefficient hA active first * guardSum hA active second x := by
  rw [guardSum_eq, guardSum_eq]
  simp only [guardCross, sub_mul, mul_assoc, Finset.sum_sub_distrib, Finset.mul_sum]

/-- The equation of two nearby events. Everything is modulo the length `m + G` of the
circle, so a wrap of the time interval contributes nothing. -/
theorem nearby_equation {m : Nat} (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active) (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (timeFirst timeSecond : Fin (m + guardNumber d A))
    (hfirst : timeFirst ∈ times m hA active x q first)
    (hsecond : timeSecond ∈ times m hA active x q second)
    (delta sigma : Int)
    (htime : (timeSecond.val : Int) - timeFirst.val = delta + sigma * (m + guardNumber d A)) :
    Int.ModEq ((m + guardNumber d A : Nat) : Int)
      (coefficient hA active first * coefficient hA active second *
          ((q (slot hA active first)).val - ((q (slot hA active second)).val : Int)) +
        ∑ u, guardCross hA active first second u * (LocalPos.localPos x u).val)
      (coefficient hA active second * rhs hA active first -
        coefficient hA active first * rhs hA active second +
        coefficient hA active first * coefficient hA active second * delta) := by
  have htimeMod : Int.ModEq ((m + guardNumber d A : Nat) : Int)
      ((timeSecond.val : Int) - timeFirst.val) delta := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-sigma, ?_⟩
    push_cast at htime ⊢
    nlinarith only [htime]
  have h1 := (Finset.mem_filter.mp hfirst).2
  have h2 := (Finset.mem_filter.mp hsecond).2
  have h := ((h1.mul_left (coefficient hA active second)).sub
    (h2.mul_left (coefficient hA active first))).add
      (htimeMod.mul_left (coefficient hA active first * coefficient hA active second))
  rw [cross_sum]
  convert h using 1 <;> ring

theorem nearby_entry {m : Nat} (hsize : radius d < m + guardNumber d A)
    (hA : 0 < A) (active : Active d A) (first second : Event d A hA active)
    (x : Fin (guardNumber d A) → Fin m)
    (q : Fin (d + 2) → Fin (m + guardNumber d A))
    (timeFirst timeSecond : Fin (m + guardNumber d A))
    (hfirst : timeFirst ∈ times m hA active x q first)
    (hsecond : timeSecond ∈ times m hA active x q second)
    (hclose : Close (radius d) timeFirst timeSecond) :
    ∃ event : PairEvent d A hA active, event.1 = first ∧ event.2.1 = second ∧
      Int.ModEq ((m + guardNumber d A : Nat) : Int)
        (coefficient hA active first * coefficient hA active second *
            ((q (slot hA active first)).val - ((q (slot hA active second)).val : Int)) +
          ∑ u, guardCross hA active first second u * (LocalPos.localPos x u).val)
        (rightSide hA active event) := by
  obtain ⟨delta, sigma, hd, hs, htime⟩ := close_winding hsize timeFirst timeSecond hclose
  let signed : Fin (2 * radius d + 1) := ⟨(delta + radius d).toNat, by omega⟩
  let wrap : Fin 3 := ⟨(sigma + 1).toNat, by omega⟩
  let event : PairEvent d A hA active := (first, second, signed, wrap)
  have hdelta : displacement hA active event = delta := by
    change ((delta + radius d).toNat : Int) - radius d = delta
    omega
  refine ⟨event, rfl, rfl, ?_⟩
  unfold rightSide
  rw [hdelta]
  exact nearby_equation hA active first second x q timeFirst timeSecond hfirst hsecond
    delta sigma htime

theorem distinct_slots_of_guard_free (hd : 3 ≤ d) (hA : 0 < A) (active : Active d A)
    (first second : Event d A hA active)
    (hdistinct : forbiddenPair hA active first ≠ forbiddenPair hA active second)
    (hzero : ∀ u, guardCross hA active first second u = 0) :
    slot hA active first ≠ slot hA active second := by
  obtain ⟨hforeign, hmobile, hassignment⟩ := pattern_eq_of_guardCross_zero hd hA active
    first second hzero
  intro hslot
  apply hdistinct
  unfold forbiddenPair
  rw [hforeign, hslot]

end CoefficientTwoPrecision.TD.ProximityCatalogue

#print axioms CoefficientTwoPrecision.TD.ProximityCatalogue.nearby_entry
#print axioms CoefficientTwoPrecision.TD.ProximityCatalogue.distinct_slots_of_guard_free
