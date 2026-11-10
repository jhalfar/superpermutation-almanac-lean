import K7.Final
import K7.TabCheck
import K7.CE.ETop
import K7.FE.P0Top
import K7.FE.P1Top
import K7.FE.P2Top
import K7.FE.P3Top
import K7.FE.P4Top

/-!
# 5,898 for 7 symbols, checked by the kernel

The chain caps `W5898` up to 78 holes (`chainCap8`) and the five profile statements of 5,899 (`profiles8`) from
the kernel search of `Engine.lean` (evaluations in `K7/CE` and `K7/FE`, soundness in `Prove.lean`), and from
them the theorem (`Final.lean`).  No `native_decide`.
-/

namespace K7

open SuperpermLowerBounds SuperpermLowerBounds.PS

/-- **F0 for 5,898**: a chain on 7 symbols with `x ≤ 78` holes has at most `W5898[x]` rows. -/
theorem chainCap8 : ChainCap Wf 78 :=
  chainCapK_of_part tabBc tabKc tabJc CE.top

/-- The chain caps for chains of words, up to 36 holes (for the profile searches). -/
theorem wcap8 : WCap 7 (fun x => W5898.getD x 0) 36 := by
  have h := wcap_of_part tabBc tabKc tabJc CE.top
  intro C hC hle
  exact h C hC (le_trans hle (by norm_num))

/-- **FF**: the five profile statements of 5,899, for the caps `W5898` (equal to those of 5,899 up to 36
holes). -/
theorem profiles8 : Profiles :=
  ⟨noProfileK_of_part wcap8 (by decide) (by decide) tabB0 tabK0 tabJ0 FE.top0,
   noProfileK_of_part wcap8 (by decide) (by decide) tabB1 tabK1 tabJ1 FE.top1,
   noProfileK_of_part wcap8 (by decide) (by decide) tabB2 tabK2 tabJ2 FE.top2,
   noProfileK_of_part wcap8 (by decide) (by decide) tabB3 tabK3 tabJ3 FE.top3,
   noProfileK_of_part wcap8 (by decide) (by decide) tabB4 tabK4 tabJ4 FE.top4⟩

/-- **Every word over `Fin 7` that contains all permutations has at least 5,898 letters.** -/
theorem covers_lower_bound_7_kernel :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5898 ≤ w.length :=
  covers_5898_of_caps chainCap8 profiles8

end K7

#print axioms K7.covers_lower_bound_7_kernel
