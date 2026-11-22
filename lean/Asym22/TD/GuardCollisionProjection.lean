import Asym22.TD.GuardCatalogue

/-!
Copy of Jay Pantone's `Quantitative/GuardCollisionProjection.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.GuardCollisionProjection`, imports of the copied modules
redirected to `Asym22.TD`. Changed for the exponent-22 batch (November 2026): his
`no_guard_only_frame` (a frame inside one background, in original cuts; not used by the
construction) is left out.

# Applying the guard catalogue to actual foreign stationary symbols

The coordinates in this argument are positions in the concrete rendered
background. Their symbols identify the corresponding physical foreign
controls. The prescribed guard-cut projection therefore yields one of the
events already deleted by GuardCatalogue. Two elementary grid lemmas cover
disjoint blocks and a shared control that is the foreign mobile.
-/

namespace CoefficientTwoPrecision.TD.GuardCollisionProjection

open ActiveGrid StationaryRelations StationaryCircle StationaryUpdate
open GuardPositions GuardEvents GuardCatalogue

theorem foreignControl_mem (d A : Nat) (hA : 0 < A) (foreign : Active d A)
    (mobile : Fin (d + 3)) (i : Fin (d + 2)) :
    foreignControl d A hA foreign mobile i ∈
      activeBlock (d + 3) A (by omega) hA foreign := by
  exact Finset.mem_image.mpr ⟨mobile.succAbove i, Finset.mem_univ _, rfl⟩

theorem allGuards_of_disjoint (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (mobile : Fin (d + 3))
    (hdisjoint : Disjoint (activeBlock (d + 3) A (by omega) hA active)
      (activeBlock (d + 3) A (by omega) hA foreign)) :
    AllGuards d A hA active foreign mobile := by
  intro i hi
  exact Finset.disjoint_left.mp hdisjoint hi (foreignControl_mem d A hA foreign mobile i)

/-- If distinct blocks share the foreign mobile, their other stationary
controls are all guards of the current active block. -/
theorem allGuards_of_shared_mobile (d A : Nat) (hA : 0 < A)
    (active foreign : Active d A) (hne : active ≠ foreign) (mobile : Fin (d + 3))
    (hshared : controlAt (d + 3) A (by omega) hA foreign mobile ∈
      activeBlock (d + 3) A (by omega) hA active) :
    AllGuards d A hA active foreign mobile := by
  intro i hi
  have hstationary : foreignControl d A hA foreign mobile i ∈
      activeBlock (d + 3) A (by omega) hA active ∩
        activeBlock (d + 3) A (by omega) hA foreign :=
    Finset.mem_inter.mpr ⟨hi, foreignControl_mem d A hA foreign mobile i⟩
  have hmobile : controlAt (d + 3) A (by omega) hA foreign mobile ∈
      activeBlock (d + 3) A (by omega) hA active ∩
        activeBlock (d + 3) A (by omega) hA foreign :=
    Finset.mem_inter.mpr ⟨hshared, Finset.mem_image.mpr ⟨mobile, Finset.mem_univ _, rfl⟩⟩
  have hcard := activeBlock_inter_card (d + 3) A (by omega) hA active foreign hne
  have he := Finset.card_le_one.mp hcard _ hstationary _ hmobile
  have hrow : mobile.succAbove i = mobile := congrArg Prod.fst he
  exact Fin.succAbove_ne mobile i hrow

end CoefficientTwoPrecision.TD.GuardCollisionProjection

#print axioms CoefficientTwoPrecision.TD.GuardCollisionProjection.allGuards_of_shared_mobile
