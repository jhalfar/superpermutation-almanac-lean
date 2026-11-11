import AlmanacDefs
import LowerBounds.SFinalTune

/-!
# Linking lemmas: the Almanac templates from the theorems of `LowerBounds.SFinalTune`

The development states its bounds with Pantone's `SuperpermutationBounds.Covers` (`Challenge.lean` of
github.com/jaypantone/superperm-upper-43-80). A word is a `List (Fin n)` in both vocabularies and its length
is `List.length` in both. This file proves that the two notions of superpermutation agree
(`covers_iff_isSuperpermutation`) and then the templates:

* `lower_twelve : Almanac.LowerBoundAt 12 522622401`, from `SuperpermLowerBounds.covers_length_ge_522622401`.
* `lower_thirteen : Almanac.LowerBoundAt 13 6746627048`, from `SuperpermLowerBounds.covers_length_ge_6746627048`.

These theorems are checked by the kernel; they use no `native_decide`.
-/

namespace LowerLinks

/-- Pantone's `Covers` is the Almanac's `IsSuperpermutation`. -/
theorem covers_iff_isSuperpermutation {n : Nat} (w : List (Fin n)) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    show ∃ s t, s ++ p ++ t = w
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ : ∃ s t, s ++ p ++ t = w := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

/-- **Every superpermutation on 12 symbols has at least 522,622,401 letters**, as the Almanac template. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622401 := fun w hw =>
  SuperpermLowerBounds.covers_length_ge_522622401 w ((covers_iff_isSuperpermutation w).mpr hw)

/-- **Every superpermutation on 13 symbols has at least 6,746,627,048 letters**, as the Almanac template. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627048 := fun w hw =>
  SuperpermLowerBounds.covers_length_ge_6746627048 w ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
