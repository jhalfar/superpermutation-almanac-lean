import LowerBounds.F5900Joint
import LowerBounds.J15Final
import LowerBounds.KFinalK16

/-!
# 5,900 for 7 symbols, from the searches, with F0 … F5 searched by the engine of `K16Search.lean`

`covers_5900_of_k16`: every word over `Fin 7` that contains all permutations has at least 5,900 letters, if
the searches answer `false`: the twelve searches of the proof of 5,899 as in `PFinalK16.lean` (F0 … F5 by
`K16Search.lean`, FR and the five profile searches by `PSearch.lean`), the searches for table T'
(`KS.EvalsT`), the searches for Theorem K (`KS.EvalsK`) and the six searches for the joint statements
(`J15.Evals`).

This is `covers_5900_of_search` of `F5900.lean` in the main repository with `caps_of_k16`,
`profiles_of_k16` and `KS.setB_of_k16` in place of `caps_of_search`, `profiles_of_search` and
`KS.setB_of_search`. No `native_decide`.
-/

namespace SuperpermLowerBounds

open T5899

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
variable {a₀ b₀ h₀ a₁ b₁ h₁ a₂ b₂ h₂ a₃ b₃ h₃ a₄ b₄ h₄ a₅ b₅ h₅ : ℕ}
variable {j₀ j₁ j₂ j₃ j₄ j₅ : Bool}
variable {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters**, if the
searches answer `false`. -/
theorem covers_5900_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (K16.seqSearch 7 Ptabs 1 0 78 a₁ b₁ h₁ j₁ f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (K16.seqSearch 7 Ptabs 2 0 72 a₂ b₂ h₂ j₂ f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (K16.seqSearch 7 Ptabs 3 0 66 a₃ b₃ h₃ j₃ f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (K16.seqSearch 7 Ptabs 4 0 60 a₄ b₄ h₄ j₄ f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (K16.seqSearch 7 Ptabs 5 0 54 a₅ b₅ h₅ j₅ f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne))
    (hT : KS.EvalsT) (hK : KS.EvalsK) (hE : J15.Evals) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length := by
  have hB : KS.SetB := KS.setB_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR
  have hTT : KS.TableT := KS.tableT_of_search hB hT
  have hKK : KS.TheoremK := KS.theoremK_of_search hB hT hK
  exact covers_5900_of_caps (caps_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR)
    (profiles_of_k16 hn₀ hna hnb hnc hnd hne h0 ha hb hc hd he) hTT hKK (J15.joint_of_search hTT hKK hE)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_5900_of_k16
