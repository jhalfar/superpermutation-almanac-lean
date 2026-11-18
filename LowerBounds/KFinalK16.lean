import LowerBounds.KFinal
import LowerBounds.PFinalK16

/-!
# Set B from the searches of `K16Search.lean`

`KFinal.lean` takes set B (the tables of the proof of 5,899 for sequences and rings, `KS.SetB`) from the
equations F0 … F5 and FR of `PSearch.lean` (`KS.setB_of_search`). Here F0 … F5 come from the search of
`K16Search.lean` instead, as in `PFinalK16.lean` (`seqCaps_of_k16`: the same six statements, searched with
the reversal cut and, if `js`, Rule JS); FR stays the ring search of `PSearch.lean`. The statement `KS.SetB`
is the same, so table T' and Theorem K follow from it by `KS.tableT_of_search` and `KS.theoremK_of_search`
as before.

No `native_decide` here: the equations are hypotheses.
-/

namespace SuperpermLowerBounds
namespace KS

open T5899

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
variable {a₀ b₀ h₀ a₁ b₁ h₁ a₂ b₂ h₂ a₃ b₃ h₃ a₄ b₄ h₄ a₅ b₅ h₅ : ℕ}
variable {j₀ j₁ j₂ j₃ j₄ j₅ : Bool}

/-- Set B on words, from the searches F0 … F5 of `K16Search.lean` and FR of `PSearch.lean`. -/
theorem setB_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (K16.seqSearch 7 Ptabs 1 0 78 a₁ b₁ h₁ j₁ f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (K16.seqSearch 7 Ptabs 2 0 72 a₂ b₂ h₂ j₂ f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (K16.seqSearch 7 Ptabs 3 0 66 a₃ b₃ h₃ j₃ f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (K16.seqSearch 7 Ptabs 4 0 60 a₄ b₄ h₄ j₄ f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (K16.seqSearch 7 Ptabs 5 0 54 a₅ b₅ h₅ j₅ f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR)) : SetB := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ h0 h1 h2 h3 h4 h5
  refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
  have hM : PS.SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
    rw [← capF_zero]
    exact c0.mono (by norm_num)
  exact PS.ringCapT_of_search (by norm_num) (by norm_num) hnR hM hR

end

end KS
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.KS.setB_of_k16
