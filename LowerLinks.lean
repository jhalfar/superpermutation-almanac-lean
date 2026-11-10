import AlmanacDefs
import K7.Main

/-!
# Linking lemma: the Almanac template from the theorem of `K7.Main`

The development states its bound with Pantone's `SuperpermutationBounds.Covers` (`Challenge.lean` of
github.com/jaypantone/superperm-upper-43-80). A word is a `List (Fin n)` in both vocabularies and its length
is `List.length` in both. This file proves that the two notions of superpermutation agree
(`covers_iff_isSuperpermutation`) and then the template:

* `lower_seven : Almanac.LowerBoundAt 7 5898`, from `K7.covers_lower_bound_7_kernel`.

That theorem is checked by the kernel; it uses no `native_decide`.
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

/-- **Every superpermutation on 7 symbols has at least 5,898 letters**, as the Almanac template. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5898 := fun w hw =>
  K7.covers_lower_bound_7_kernel w ((covers_iff_isSuperpermutation w).mpr hw)

end LowerLinks
