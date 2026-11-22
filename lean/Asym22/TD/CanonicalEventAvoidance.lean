import Asym22.TD.EventLabelTransport
import Asym25.Parking
import Quantitative.FiniteProgram

/-!
Copy of Jay Pantone's `Quantitative/CanonicalEventAvoidance.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.CanonicalEventAvoidance`, imports of the copied modules
redirected to `Asym22.TD`. For the exponent-25 batch the compiled program is that of
`Asym25.Parking` (phases 0 and 2, normal parking order) and the avoidance is
`Asym25.event_prefix_avoids`; this needs `3 ≤ k`.

# Actual repaired prefixes avoid canonical physical events

The safe cut changes the local batch coordinate by a fixed origin. A
canonical event at cut+t therefore appears at t in the grouped list.
Its converted engine label determines an actual parking interval. The
literal prefix avoidance theorem and finite-role encoding give the
required assertion for the executed finite assignment.
-/

namespace CoefficientTwoPrecision.TD.CanonicalEventAvoidance

open PositiveParking MacroCatalogue RepairAvoidance RepairGroups RepairProgram
open CyclicRepairSchedule EventLabelTransport CompiledEventAvoidance

variable {M k : Nat} {Control : Type} [NeZero M] [DecidableEq Control]

theorem canonical_prefix_avoids (hk : 3 ≤ k)
    (initial : FiniteRoles.Role k ≃ Control)
    (events : Finset (ZMod M × (Control × Fin k))) (cut : ZMod M)
    (groups : List (EventGroup (2 * (k + 1) + 1) ForbiddenPair))
    (hgroups : (groups.flatMap EventGroup.events).Perm
      (liftedEvents (mapEvents (encodePair initial) events) cut))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before)
    (n : Nat) (hbatch : n / k < M) (pair : Control × Fin k)
    (hevent : (cut + (n / k : Nat), pair) ∈ events) :
    FiniteRoles.execute
      ((FiniteProgram.word k (compile (k + 1) (Asym25.groupPhase k) (Asym25.groupChoice k) M 0 groups)).take n)
      initial (some pair.2.rev) ≠ pair.1 := by
  classical
  have hencoded : (cut + (n / k : Nat), encodePair initial pair) ∈
      mapEvents (encodePair initial) events :=
    Finset.mem_image.mpr ⟨(cut + (n / k : Nat), pair), hevent, rfl⟩
  have hlift : liftEvent cut (cut + (n / k : Nat), encodePair initial pair) =
      (n / k, encodePair initial pair) := by
    simp only [liftEvent, add_sub_cancel_left, ZMod.val_natCast_of_lt hbatch]
  have hliftMem : (n / k, encodePair initial pair) ∈
      liftedEvents (mapEvents (encodePair initial) events) cut := by
    exact List.mem_map.mpr ⟨(cut + (n / k : Nat), encodePair initial pair),
      Finset.mem_toList.mpr hencoded, hlift⟩
  have hflat := hgroups.mem_iff.mpr hliftMem
  have havoid := Asym25.event_prefix_avoids k M hk groups hfirst hbefore
    (n / k, encodePair initial pair) hflat (encodePair_role initial pair) pair.2.rev.isLt n rfl
  apply finite_avoidance _ initial pair.1 pair.2.rev
  rw [List.map_take, FiniteProgram.word_map]
  exact havoid

end CoefficientTwoPrecision.TD.CanonicalEventAvoidance

#print axioms CoefficientTwoPrecision.TD.CanonicalEventAvoidance.canonical_prefix_avoids
