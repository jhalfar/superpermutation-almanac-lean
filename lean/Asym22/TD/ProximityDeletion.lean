import Asym22.TD.ProximityPairCount

/-!
Copy of Jay Pantone's `Quantitative/ProximityDeletion.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.ProximityDeletion`, imports of the copied modules
redirected to `Asym22.TD`. Changed: the block count is `A * tdQ (d+3) A` in place of `A ((d+3)A)`.
Changed for the exponent-22 batch (November 2026): his count by the maximum of the two rank
cases (`scaledBound`, `deleted_scaled`) is left out; `Asym22.IntervalKeys` counts instead.

# Global cardinality of the actual proximity deletion

The two rank cases partition the pair-event catalogue. A common upper
bound is their maximum, so the final estimate does not pay for both
cases on every entry. All finite sets below are subsets of the fixed
candidate product used by the construction.
-/

namespace CoefficientTwoPrecision.TD.ProximityDeletion

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue ProximitySurvivors ProximityPairCount

variable {m d A : Nat}

def frameBound (m d A : Nat) : Nat :=
  m.descFactorial (guardNumber d A) * (d + 3).factorial *
    ((d + 1) * d * ((m + guardNumber d A) ^ (d - 1) * (2 * (d - 1) ^ 2)))

noncomputable def badFiber (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Fiber m d A) := by
  classical
  exact Finset.univ.biUnion (pairSolutions hA active S)

noncomputable def allBad (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact (candidates m d A S).filter (Bad hA)

noncomputable def badFiberFilter (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Fiber m d A) := by
  classical
  exact ((Finset.univ : Finset (Fin (guardNumber d A) ↪ Fin m)) ×ˢ S).filter
    (fun p => Bad hA (active, p))

theorem badFiber_eq (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    badFiber hA active S = badFiberFilter hA active S := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨event, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hbase, hdistinct, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hbase, ⟨event, hdistinct, heq⟩⟩
  · intro hp
    obtain ⟨hbase, event, hdistinct, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨event, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hbase, hdistinct, heq⟩⟩

theorem allBad_card (hA : 0 < A) (S : Finset (Labelled (m + guardNumber d A) d)) :
    (allBad hA S).card = ∑ active : Active d A, (badFiber hA active S).card := by
  classical
  simp only [allBad, candidates, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro active _
  rw [badFiber_eq]
  simp only [badFiberFilter, Finset.card_filter, Finset.sum_product]

theorem deleted_le_allBad (hA : 0 < A)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (GuardCandidateLoss.retained m d A hA S).card - (survivors m d A hA S).card ≤
      (allBad hA S).card := by
  classical
  have hsub : (GuardCandidateLoss.retained m d A hA S).filter (Bad hA) ⊆ allBad hA S := by
    intro c hc
    obtain ⟨hret, hbad⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr
      ⟨GuardCandidateLoss.retained_subset m d A hA S hret, hbad⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := GuardCandidateLoss.retained m d A hA S) (Bad hA)
  have hle := Finset.card_le_card hsub
  change ((GuardCandidateLoss.retained m d A hA S).filter (Bad hA)).card +
    (survivors m d A hA S).card = (GuardCandidateLoss.retained m d A hA S).card at hcard
  omega

end CoefficientTwoPrecision.TD.ProximityDeletion

#print axioms CoefficientTwoPrecision.TD.ProximityDeletion.deleted_le_allBad
