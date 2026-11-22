import Asym22.TD.PhysicalOldCuts
import Asym22.TD.GridBackground
import Quantitative.CrossBackgroundProjection
import Quantitative.StationaryWeightTransport

/-!
Copy of Jay Pantone's `Quantitative/PhysicalGuardExclusion.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.PhysicalGuardExclusion`, imports of the copied modules
redirected to `Asym22.TD`. Changed for the exponent-22 batch (November 2026): the foreign
relation is transported to the local positions of the current guards
(`PhysicalOldCuts.resident_guard_local`, offsets at most `d + 4`) instead of their original cuts.

# Actual cross-background collision exclusion after guard-only deletion

Both rows below use canonical guard backgrounds and genuine bijective
physical role assignments. The foreign frame relation is stated on the
foreign row's own local cuts. All one-control filters are the canonical
predicate retaining the common old alphabet and that physical control.
Their values follow from grid membership and label injectivity. Thus no
coordinate-identification or filter table is assumed in the conclusion.
-/

namespace CoefficientTwoPrecision.TD.PhysicalGuardExclusion

open ActiveGrid GuardCatalogue GridBackground GuardBackgrounds
open StationaryCircle StationaryRelations StationaryWeightTransport
open CrossBackgroundProjection

variable {m d A : Nat} {α : Type} [DecidableEq α]

theorem no_guard_only_collision
    (hm : 0 < m) (hd : 2 ≤ d) (hA : 0 < A)
    (old : Fin m → α) (ho : Function.Injective old)
    (label : Physical d A → α) (hl : Function.Injective label)
    (hcross : ∀ p i, label p ≠ old i)
    (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) ↪ Fin m)
    (hgood : guardCutsL ∈ goodEmbeddings m d A hA active)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (hguards : AllGuards d A hA active foreign (roleR none))
    (sumSlot : Fin (d + 2)) (hsum : sumSlot ≠ 0)
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq ((m + guardNumber d A : Nat) : Int)
      (∑ i, AffineReconstruction.frameWeight d sumSlot i * q i) 0)
    (hlocal : ∀ i, Int.ModEq ((m + guardNumber d A : Nat) : Int) (localR i).val
      (q i + t + (phase i).val)) :
    ¬ (ActualMatching.base (background hA old ho label hl hcross active guardCutsL)
      (fun i => label (activeControl d A hA active i)) roleL localL gapL).IsRotated
      (ActualMatching.base (background hA old ho label hl hcross foreign guardCutsR)
        (fun i => label (activeControl d A hA foreign i)) roleR localR gapR) := by
  intro hcyclic
  let index := foreignGuardIndex d A hA active foreign (roleR none) hguards
  obtain ⟨slots, hslots⟩ := slotEquiv_exists roleR
  obtain ⟨assignment, hweight, hqphysical⟩ := physical_relation
    ((m + guardNumber d A : Nat) : Int) sumSlot hsum slots q hq
  have hoffsets (i : Fin (d + 2)) :
      (((localR (slots i)).val : Int) -
        (LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m) (index i)).val).natAbs ≤
          d + 4 := by
    have htracked : guardLabel d A hA active (index i) =
        PhysicalOldCuts.residentControl hA foreign roleR (slots i) := by
      dsimp [index]
      rw [foreign_guard_label]
      change foreignControl d A hA foreign (roleR none) i =
        activeControl d A hA foreign (roleR (some (slots i)))
      rw [hslots i]
      rfl
    exact PhysicalOldCuts.resident_guard_local hA old ho label hl hcross active foreign
      guardCutsL guardCutsR guardCutsL.injective roleL roleR localL localR gapL gapR
      (index i) (slots i) htracked hcyclic
  obtain ⟨b, hb, hrel⟩ := LocalPos.local_relation ((m + guardNumber d A : Nat) : Int) hd assignment
    (fun i => ((LocalPos.localPos (guardCutsL : Fin (guardNumber d A) → Fin m) (index i)).val : Int))
    (fun i => ((localR (slots i)).val : Int)) (d + 4) hoffsets
    (fun i => q (slots i)) (fun i => phase (slots i)) t hqphysical (fun i => hlocal (slots i))
  exact good_excludes m d A hA active foreign (roleR none) assignment hguards guardCutsL hgood b
    (hb.trans (LocalPos.local_bound_guard d)) hrel

end CoefficientTwoPrecision.TD.PhysicalGuardExclusion

#print axioms CoefficientTwoPrecision.TD.PhysicalGuardExclusion.no_guard_only_collision
