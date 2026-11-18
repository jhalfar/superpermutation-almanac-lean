import AlmanacDefs
import LowerBounds.F5900K16Native

/-!
# Linking lemma: the Almanac template from the theorem of `LowerBounds.F5900K16Native`

The development states its bound with Pantone's `SuperpermutationBounds.Covers` (`Challenge.lean` of
github.com/jaypantone/superperm-upper-43-80). A word is a `List (Fin n)` in both vocabularies and its length
is `List.length` in both. This file proves that the two notions of superpermutation agree
(`covers_iff_isSuperpermutation`) and then the template:

* `lower_seven : Almanac.LowerBoundAt 7 5900`, from `SuperpermLowerBounds.covers_lower_bound_7_5900_native`.

That theorem depends on 89 equations evaluated by `native_decide` (see `LowerBounds/F5900K16Native.lean`).
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

/-- **Every superpermutation on 7 symbols has at least 5,900 letters**, as the Almanac template. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5900 := fun w hw =>
  SuperpermLowerBounds.covers_lower_bound_7_5900_native w ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
