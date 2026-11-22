import Asym22.TD.CollisionGeometry
import Asym22.TD.PrimaryCatalogue
import Quantitative.StationaryWeightTransport

/-!
Copy of Jay Pantone's `Quantitative/CollisionToPrimary.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.CollisionToPrimary`, imports of the copied modules
redirected to `Asym22.TD`. Changed for the exponent-22 batch (November 2026): the foreign
relation is transported to the local positions of the current guards and to the current
local cut of the shared control (`PhysicalOldCuts.resident_guard_local`,
`common_resident_local`: offsets at most `d + 4`), so the event holds modulo `m + G` with a
right side bounded by `2 r^2`.

# Literal cross-block collisions belong to the primary catalogue

Filtering the two full cyclic rows identifies the original cut of their
shared stationary control. Every other foreign stationary control is a
named guard of the current block. These identifications transport the
foreign affine relation to the current guard variables and the actual
current slot and time. The resulting congruence is a catalogue entry.
-/

namespace CoefficientTwoPrecision.TD.CollisionToPrimary

open GuardCatalogue GridBackground NeighbourGeometry PhysicalOldCuts
open CollisionGeometry StationaryRelations GuardEvents ActiveSlotEvents PrimaryCatalogue

private theorem stationary_slot {d : Nat}
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) (row : Fin (d + 3))
    (hne : role none ≠ row) : ∃ j, role (some j) = row := by
  cases h : role.symm row with
  | none =>
      have he := role.apply_symm_apply row
      rw [h] at he
      exact False.elim (hne he)
  | some j =>
      exact ⟨j, by simpa only [h] using role.apply_symm_apply row⟩

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
variable (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

include hm hd

/-- A collision of the two actual cyclic rows gives an event at the
current time. Its current slot carries the actual shared control. -/
theorem collision_event (active : Active d A) (foreign : Neighbour d A hA active)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgoodL : guardCutsL ∈ goodEmbeddings m d A hA active)
    (hgoodR : guardCutsR ∈ goodEmbeddings m d A hA foreign.val)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hframeL : HasFrame localL) (hframeR : HasFrame localR)
    (qL : Fin (d + 2) → Fin (m + guardNumber d A))
    (time : Fin (m + guardNumber d A)) (phaseL : Fin (d + 2) → Fin 2)
    (hlocalL : ∀ j, (localL j).val =
      ((qL j).val + time.val + (phaseL j).val) % (m + guardNumber d A))
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign.val guardCutsR roleR localR gapR)) :
    ∃ event : Event d A hA active, event.1 = foreign ∧
      residentControl hA active roleL (slot hA active event) = shared hA active foreign ∧
      time ∈ times m hA active guardCutsL qL event := by
  classical
  have hmobileR := foreign_mobile_not_shared hm hd hA old ho label hl hcross
    active foreign guardCutsL guardCutsR hgoodL roleL roleR localL localR gapL gapR hframeR hcyclic
  have hmobileL := current_mobile_not_shared hm hd hA old ho label hl hcross
    active foreign guardCutsL guardCutsR hgoodR roleL roleR localL localR gapL gapR hframeL hcyclic
  let mobile : Mobile hA active foreign := ⟨roleR none, hmobileR⟩
  let sharedSlot := sharedIndex hA active foreign mobile
  obtain ⟨slotsR, hslotsR⟩ := slotEquiv_exists roleR
  obtain ⟨targetL, htargetL⟩ := stationary_slot roleL (shared hA active foreign).1 hmobileL
  have hcontrolL : residentControl hA active roleL targetL = shared hA active foreign := by
    change activeControl d A hA active (roleL (some targetL)) = _
    rw [htargetL, shared_in_current_row]
  have hcontrolR : residentControl hA foreign.val roleR (slotsR sharedSlot) =
      shared hA active foreign := by
    change activeControl d A hA foreign.val (roleR (some (slotsR sharedSlot))) = _
    rw [hslotsR]
    exact sharedIndex_control hA active foreign mobile
  have hsharedOff := common_resident_local hA old ho label hl hcross active foreign.val
    guardCutsL guardCutsR guardCutsL.injective guardCutsR.injective roleL roleR localL localR
    gapL gapR targetL (slotsR sharedSlot) (hcontrolL.trans hcontrolR.symm) hcyclic
  let Y : Fin (d + 2) → Int := fun i =>
    if hi : i = sharedSlot then ((localL targetL).val : Int)
    else ((LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m)
      (guardIndex hA active foreign mobile ⟨i, hi⟩)).val : Int)
  have hYShared : Y sharedSlot = ((localL targetL).val : Int) := by simp only [Y, dif_pos rfl]
  have hoffset : ∀ i, (((localR (slotsR i)).val : Int) - Y i).natAbs ≤ d + 4 := by
    intro i
    by_cases hi : i = sharedSlot
    · subst i
      rw [hYShared]
      exact hsharedOff
    · have htracked : guardLabel d A hA active (guardIndex hA active foreign mobile ⟨i, hi⟩) =
          residentControl hA foreign.val roleR (slotsR i) := by
        rw [guardIndex_label]
        change activeControl d A hA foreign.val (mobile.val.succAbove i) =
          activeControl d A hA foreign.val (roleR (some (slotsR i)))
        rw [hslotsR]
      have h := PhysicalOldCuts.resident_guard_local hA old ho label hl hcross
        active foreign.val guardCutsL guardCutsR guardCutsL.injective roleL roleR localL localR
        gapL gapR (guardIndex hA active foreign mobile ⟨i, hi⟩) (slotsR i) htracked hcyclic
      simpa only [Y, dif_neg hi] using h
  obtain ⟨sumSlot, qR, phaseR, tR, hsumR, hqR, hlocalR⟩ := hframeR
  obtain ⟨assignment, hweights, hphysical⟩ := StationaryWeightTransport.physical_relation
    ((m + guardNumber d A : Nat) : Int) sumSlot hsumR slotsR qR hqR
  obtain ⟨b, hb, hforeign⟩ := LocalPos.local_relation ((m + guardNumber d A : Nat) : Int) hd
    assignment Y (fun i => ((localR (slotsR i)).val : Int)) (d + 4) hoffset
    (fun i => qR (slotsR i)) (fun i => phaseR (slotsR i)) tR hphysical
    (fun i => hlocalR (slotsR i))
  have hshared' : Int.ModEq ((m + guardNumber d A : Nat) : Int) (Y sharedSlot)
      (((qL targetL).val : Int) + (time.val : Int) + ((phaseL targetL).val : Int)) := by
    rw [hYShared, hlocalL targetL]
    have h := Int.mod_modEq (((qL targetL).val : Int) + (time.val : Int) +
      ((phaseL targetL).val : Int)) ((m + guardNumber d A : Nat) : Int)
    have hc : (((((qL targetL).val + time.val + (phaseL targetL).val) %
        (m + guardNumber d A) : Nat)) : Int) =
        (((qL targetL).val : Int) + (time.val : Int) + ((phaseL targetL).val : Int)) %
          ((m + guardNumber d A : Nat) : Int) := by
      push_cast
      rfl
    rw [hc]
    exact h
  obtain ⟨b1, hb1, hprimary⟩ := LocalPos.primary_relation_local
    ((m + guardNumber d A : Nat) : Int) hd assignment sharedSlot Y (qL targetL).val time.val
    (phaseL targetL) b (2 * d * (d + 4 + 1)) hforeign hb hshared'
  have hb1' : b1.natAbs ≤ LocalPos.localOffsetBound d := hb1.trans (LocalPos.local_bound_event d)
  let offset : Fin (2 * LocalPos.localOffsetBound d + 1) :=
    ⟨(b1 + LocalPos.localOffsetBound d).toNat, by omega⟩
  let event : Event d A hA active := ⟨foreign, mobile, assignment, targetL, offset⟩
  have hrhs : rhs hA active event = b1 := by
    change ((b1 + LocalPos.localOffsetBound d).toNat : Int) - LocalPos.localOffsetBound d = b1
    omega
  have hremaining : remainingSum assignment sharedSlot Y =
      guardSum hA active event
        (LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m)) := by
    have he := Fintype.sum_eq_add_sum_subtype_ne
      (fun i => weight assignment i * Y i) sharedSlot
    rw [split_shared] at he
    have he' := add_left_cancel he
    calc
      remainingSum assignment sharedSlot Y =
          ∑ i : {i : Fin (d + 2) // i ≠ sharedSlot},
            weight assignment i.val * Y i.val := he'
      _ = guardSum hA active event
          (LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Y, dif_neg i.property]
        rfl
  refine ⟨event, rfl, hcontrolL, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change Int.ModEq ((m + guardNumber d A : Nat) : Int)
    (weight assignment sharedSlot * ((qL targetL).val + (time.val : Int)) +
      guardSum hA active event
        (LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m))) (rhs hA active event)
  rw [hrhs, ← hremaining]
  exact hprimary

end CoefficientTwoPrecision.TD.CollisionToPrimary

#print axioms CoefficientTwoPrecision.TD.CollisionToPrimary.collision_event
