import AlmanacDefs
import K6.Final872

/-!
# Linking lemma: the Almanac template from the theorem of `K6/Final872.lean`

The development states its bound with Pantone's `SuperpermutationBounds.Covers` (`Challenge.lean` of
github.com/jaypantone/superperm-upper-43-80). A word is a `List (Fin n)` in both vocabularies and its length
is `List.length` in both. This file proves that the two notions of superpermutation agree
(`covers_iff_isSuperpermutation`) and then the template:

* `lower_six : Almanac.LowerBoundAt 6 872`, from `K6.covers_872`.

Everything is checked by the kernel; the axioms are `propext`, `Classical.choice` and `Quot.sound`.
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

/-- **Every superpermutation on 6 symbols has at least 872 letters**, as the Almanac template. -/
theorem lower_six : Almanac.LowerBoundAt 6 872 := fun w hw =>
  K6.covers_872 w ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
