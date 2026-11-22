import Quantitative.UniformPacking
import Asym28.TD.GuardCatalogue
import Quantitative.CandidateFactorization

/-!
Copy of Jay Pantone's `Quantitative/CandidateSpace.lean` (release 9ccbe66) for the
transversal design of `Asym28.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.CandidateSpace`, imports of the copied modules
redirected to `Asym28.TD`. Changed: the block count in `candidates_card` is
`A * tdQ (d+3) A`; Jay's `guard_number_eq` and `prescribed_card` for his
`sourceA` are dropped (`Asym28.Width` has them for the new `A`).

# The actual finite candidate space with a fixed selected frame family

A candidate is an active block, an injective assignment of guard cuts,
and one labelled frame from the single uniformly separated selection.
The frame selection is a parameter shared by all blocks and backgrounds.
-/

namespace CoefficientTwoPrecision.TD.CandidateSpace

open GuardCatalogue LabelledReconstruction

abbrev Candidate (m d A : Nat) :=
  Active d A × (Fin (guardNumber d A) ↪ Fin m) × Labelled (m + guardNumber d A) d

noncomputable def candidates (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) : Finset (Candidate m d A) := by
  classical
  exact Finset.univ ×ˢ (Finset.univ ×ˢ S)

theorem mem_candidates (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) (candidate : Candidate m d A) :
    candidate ∈ candidates m d A S ↔ candidate.2.2 ∈ S := by
  classical
  simp only [candidates, Finset.mem_product, Finset.mem_univ, true_and]

theorem candidates_card (m d A : Nat)
    (S : Finset (Labelled (m + guardNumber d A) d)) :
    (candidates m d A S).card =
      (A * tdQ (d + 3) A) * m.descFactorial (guardNumber d A) * S.card := by
  classical
  simp only [candidates, Finset.card_product, Finset.card_univ,
    Fintype.card_embedding_eq, Fintype.card_fin, ActiveGrid.blocks_card, mul_assoc]

end CoefficientTwoPrecision.TD.CandidateSpace

#print axioms CoefficientTwoPrecision.TD.CandidateSpace.candidates_card
