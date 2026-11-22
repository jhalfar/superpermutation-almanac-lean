import Asym25.Degree
import Asym25.Aligned
import Quantitative.PhysicalEnvelope

/-!
# Exponent 25: the tied literal envelope is the counted tied envelope

`Asym25.Aligned.EnvelopeT` is stated in the conventions of the schedule
(descending normal-order ranks, Jay Pantone's joint index with the parking
order as a Boolean). `Asym25.Degree` counts intersections for the index
`(role phase, prefix)` and increasing physical cuts. `literal_memT` converts
one into the other; it is his `PhysicalEnvelope.literal_mem` with the joint
index and its tie to the translation carried along.
-/

namespace CoefficientTwoPrecision.Asym25

open FiniteRoles JointStates BatchSafety StationaryCircle LiteralSchedule TargetTrace
open ActualCyclicMatching EnvelopeDegree RobustMatching RobustSafety

/-- The joint states of the normal parking order: role phase and prefix. -/
abbrev IndexT (d : Nat) := Fin (d + 3) × Fin (2 * (d + 2) + 1)

def toIndex {d : Nat} (index : IndexT d) : Index (d + 2) := (index.1, false, index.2)

def actionT (d : Nat) (index : IndexT d) : Equiv.Perm (FiniteRoles.Role (d + 2)) :=
  PhysicalJointStates.action (d + 2) (toIndex index)

def phaseT (d : Nat) (index : IndexT d) : Fin (d + 2) → Bool :=
  PhysicalJointStates.phase (d + 2) (toIndex index)

theorem phaseT_indep (d : Nat) (s s' : Fin (d + 3)) (j : Fin (2 * (d + 2) + 1)) :
    phaseT d (s, j) = phaseT d (s', j) := rfl

theorem indexT_card (d : Nat) : Fintype.card (Fin (2 * (d + 2) + 1)) ≤ 2 * (d + 3) := by
  rw [Fintype.card_fin]
  omega

theorem literal_memT {M d : Nat} [NeZero M] {α : Type} [DecidableEq α] (hdiv : d + 3 ∣ M)
    (background : Fin M → α) (embed : FiniteRoles.Role (d + 2) → α)
    (initial : Equiv.Perm (FiniteRoles.Role (d + 2))) (q : Fin (d + 2) → Fin M)
    (hrobust : Robust (fun i => cutValue (q i))) (source : List α)
    (hsource : EnvelopeT background
      (fun p => embed (FiniteRoles.lift ((PhysicalJointStates.reverseRoles (d + 2)).trans initial) p))
      (fun i => q i.rev) source) :
    ∃ index : IndexT d, ∃ translation : ZMod M, ∃ gap : Nat,
      Tied index translation ∧
      source = EnvelopeDegree.row background embed (actionT d) (phaseT d) (q, initial)
        index translation gap := by
  classical
  obtain ⟨index0, translation, hfalse, htie, cuts, gap, hbase, hcuts⟩ := hsource
  obtain ⟨s, c, ell⟩ := index0
  dsimp only at hfalse htie
  subst hfalse
  let index : Index (d + 2) := (s, false, ell)
  let labels : Option Nat → α := fun p => embed (FiniteRoles.lift
    ((PhysicalJointStates.reverseRoles (d + 2)).trans initial)
      ((interpret (d + 2) (List.range (d + 2)) index).labels p))
  let physicalCuts := phaseCuts q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index)
  have hvalues (i : Fin (d + 2)) :
      cutValue (cuts i.rev) = cutValue (q i) + (translation : ZMod M) +
        (bit (PhysicalJointStates.phase (d + 2) index i) : ZMod M) := by
    unfold cutValue
    rw [hcuts i.rev]
    simp only [Fin.rev_rev, ZMod.natCast_mod, Nat.cast_add]
    rw [PhysicalJointStates.phase_value]
  have hreindex : cuts ∘ Fin.revPerm = physicalCuts := by
    funext i
    apply cutValue_injective
    change cutValue (cuts i.rev) = cutValue (physicalCuts i)
    rw [hvalues]
    exact (phaseCuts_represents q (translation : ZMod M)
      (PhysicalJointStates.phase (d + 2) index) i).symm
  have hphysicalInj : Function.Injective physicalCuts := by
    intro i j hij
    apply perturbed_injective (fun i => cutValue (q i)) hrobust
      (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index)
    have h := congrArg cutValue hij
    rw [phaseCuts_represents q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index) i,
      phaseCuts_represents q (translation : ZMod M) (PhysicalJointStates.phase (d + 2) index) j] at h
    exact h
  have hcutInj : Function.Injective cuts := by
    intro i j hij
    apply Fin.rev_injective
    apply hphysicalInj
    rw [← hreindex]
    simpa only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev] using hij
  have hresidents : residents labels ∘ Fin.revPerm =
      ActualMatching.resident embed ((PhysicalJointStates.action (d + 2) index).trans initial) := by
    funext i
    exact congrArg embed (PhysicalJointStates.stationary_label index initial i)
  have hmobile : labels none = embed (((PhysicalJointStates.action (d + 2) index).trans initial) none) :=
    congrArg embed (PhysicalJointStates.mobile_label index initial)
  have hrender := RendererReindex.render_reindex background (residents labels) cuts hcutInj Fin.revPerm
  rw [hreindex, hresidents] at hrender
  refine ⟨(s, ell), (translation : ZMod M), gap, ?_, ?_⟩
  · have hval : ((translation : ℕ) : ZMod M).val % (d + 3) = translation % (d + 3) := by
      rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ hdiv]
    rcases htie with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (h.trans hval.symm))
  · change source = (render background
      (ActualMatching.resident embed ((PhysicalJointStates.action (d + 2) index).trans initial))
        physicalCuts).rotateLeft gap ++ [embed (((PhysicalJointStates.action (d + 2) index).trans initial) none)]
    change source = (render background (residents labels) cuts).rotateLeft gap ++ [labels none] at hbase
    rw [hrender, ← hmobile]
    exact hbase

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.literal_memT
