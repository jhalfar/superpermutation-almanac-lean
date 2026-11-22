import Asym22.TD.ProximitySurvivors
import Quantitative.GuardFreeCount

/-!
Copy of Jay Pantone's `Quantitative/ProximityPairCount.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.ProximityPairCount`, imports of the copied modules
redirected to `Asym22.TD`. Changed for the exponent-22 batch (November 2026): his two
per-equation counts (`guard_variable_count`, `guard_free_count`) are left out; their roles
are taken by `Asym22.IntervalKeys`, which counts in local positions.

# Counting one actual proximity equation in the candidate product

For a nonzero guard coefficient, fix the selected labelled node and count
guard assignments. If all guard coefficients vanish, count ambient
labelled frames and multiply by the exact number of injective guard maps.
Both arguments apply to one fixed selection shared by every background.
-/

namespace CoefficientTwoPrecision.TD.ProximityPairCount

open GuardCatalogue CandidateSpace LabelledReconstruction PrimaryCatalogue PrimaryRank
open ProximityCatalogue ProximitySurvivors SortedFrameSupply

variable {m d A : Nat}

abbrev Fiber (m d A : Nat) :=
  (Fin (guardNumber d A) ↪ Fin m) × Labelled (m + guardNumber d A) d

noncomputable def pairSolutions (hA : 0 < A) (active : Active d A)
    (S : Finset (Labelled (m + guardNumber d A) d)) (event : PairEvent d A hA active) :
    Finset (Fiber m d A) := by
  classical
  exact (Finset.univ ×ˢ S).filter (fun p =>
    forbiddenPair hA active event.1 ≠ forbiddenPair hA active event.2.1 ∧
      Equation hA active p.1 p.2.1 event)

theorem labelled_frame_count (m M : Nat) [NeZero M] (hm : 0 < m) (hMpos : 0 < M)
    (hM : M ≤ 2 * m) (hd : 3 ≤ d) (a : Int) (ha : a ≠ 0)
    (j l : Fin (d + 2)) (hne : j ≠ l) (b : Int) :
    (d - 1).factorial * ((labelledFrames M d).filter
      (fun node => Int.ModEq (m : Int) (a * ((node.1 j).val - ((node.1 l).val : Int))) b)).card ≤
        (d + 3).factorial * ((d + 1) * d * (M ^ (d - 1) * (2 * a.natAbs))) := by
  classical
  have he : ((labelledFrames M d).filter
      (fun node => Int.ModEq (m : Int) (a * ((node.1 j).val - ((node.1 l).val : Int))) b)).card =
      ((physicalFrames M d).filter
        (fun q => Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b)).card *
          (d + 3).factorial := by
    rw [labelledFrames, Finset.filter_product_left
      (fun q : Fin (d + 2) → Fin M =>
        Int.ModEq (m : Int) (a * ((q j).val - ((q l).val : Int))) b), Finset.card_product]
    simp [FiniteRoles.Role, Fintype.card_perm, Nat.add_assoc]
  rw [he]
  have h := Nat.mul_le_mul_left (d + 3).factorial
    (GuardFreeCount.physical_count m M hm hMpos hM hd a ha j l hne b)
  nlinarith only [h]

end CoefficientTwoPrecision.TD.ProximityPairCount

