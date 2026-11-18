import LowerBounds.PFinal
import LowerBounds.K16Rules

/-!
# 5,899 for 7 symbols, with the statements F0 … F5 searched by the engine of `K16Search.lean`

`PFinal.lean` proves 5,899 from twelve equations of `PSearch.lean`. The six equations F0 … F5 there are
searches with the plain rule of the written proof of 5,899 (section 8.1). Here the same six statements
(F_s: every sequence with exactly `s` links of weight 4 and at most `84 - 6 s` holes has at most `P_s(x)`
rows, for the tables `T5899.Ptabs` of set B) are taken from the search of `K16Search.lean` instead: the
search of 5,900 with the reversal cut and, if `js`, Rule JS of 5,901. Its soundness is
`K16.seqCap_of_k16search` (`K16Rules.lean`), for every potential `(a, b, h)` and with or without Rule JS.
The statements are the same, so the tree is smaller and the theorem is the same.

FR (rings) and FF (the five profiles) stay the searches of `PSearch.lean`.

No `native_decide` here: the equations are hypotheses. `PFinalK16Native.lean` supplies them.
-/

namespace SuperpermLowerBounds

open T5899

section

variable {f₀ d₀ n₀ f₁ d₁ n₁ f₂ d₂ n₂ f₃ d₃ n₃ f₄ d₄ n₄ f₅ d₅ n₅ fR dR nR : ℕ}
variable {a₀ b₀ h₀ a₁ b₁ h₁ a₂ b₂ h₂ a₃ b₃ h₃ a₄ b₄ h₄ a₅ b₅ h₅ : ℕ}
variable {j₀ j₁ j₂ j₃ j₄ j₅ : Bool}

/-- The caps for sequences on words, from the six searches F0 … F5 of `K16Search.lean`. -/
theorem seqCaps_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (K16.seqSearch 7 Ptabs 1 0 78 a₁ b₁ h₁ j₁ f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (K16.seqSearch 7 Ptabs 2 0 72 a₂ b₂ h₂ j₂ f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (K16.seqSearch 7 Ptabs 3 0 66 a₃ b₃ h₃ j₃ f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (K16.seqSearch 7 Ptabs 4 0 60 a₄ b₄ h₄ j₄ f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (K16.seqSearch 7 Ptabs 5 0 54 a₅ b₅ h₅ j₅ f₅ d₅ n₅)) :
    PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 ∧ PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 ∧
      PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 ∧ PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 ∧
      PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 ∧ PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 := by
  have c0 : PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₀
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (PS.seqCapLt_zero _ _ _) h0
  have c1 : PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₁
      (fun j hj => by
        interval_cases j
        exact c0.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h1
  have c2 : PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₂
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h2
  have c3 : PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₃
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h3
  have c4 : PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₄
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num)
        · exact c3.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h4
  have c5 : PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₅
      (fun j hj => by
        interval_cases j
        · exact c0.mono (by norm_num)
        · exact c1.mono (by norm_num)
        · exact c2.mono (by norm_num)
        · exact c3.mono (by norm_num)
        · exact c4.mono (by norm_num))
      (PS.seqCapLt_zero _ _ _) h5
  exact ⟨c0, c1, c2, c3, c4, c5⟩

/-- **`Caps`, from F0 … F5 searched by `K16Search.lean` and FR searched by `PSearch.lean`.** -/
theorem caps_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
    (hn₄ : 0 < n₄) (hn₅ : 0 < n₅) (hnR : 0 < nR)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (h1 : PS.Covered n₁ (K16.seqSearch 7 Ptabs 1 0 78 a₁ b₁ h₁ j₁ f₁ d₁ n₁))
    (h2 : PS.Covered n₂ (K16.seqSearch 7 Ptabs 2 0 72 a₂ b₂ h₂ j₂ f₂ d₂ n₂))
    (h3 : PS.Covered n₃ (K16.seqSearch 7 Ptabs 3 0 66 a₃ b₃ h₃ j₃ f₃ d₃ n₃))
    (h4 : PS.Covered n₄ (K16.seqSearch 7 Ptabs 4 0 60 a₄ b₄ h₄ j₄ f₄ d₄ n₄))
    (h5 : PS.Covered n₅ (K16.seqSearch 7 Ptabs 5 0 54 a₅ b₅ h₅ j₅ f₅ d₅ n₅))
    (hR : PS.Covered nR (PS.ringSearch 7 Mtab PRtab 77 fR dR nR)) : Caps := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ h0 h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_⟩
  · exact PS.chainCapK_of_wcap (PS.wcap_of_seqCap c0)
  · intro s hs1 hs5
    interval_cases s
    · exact PS.pathCapK_of_seqCap c1
    · exact PS.pathCapK_of_seqCap c2
    · exact PS.pathCapK_of_seqCap c3
    · exact PS.pathCapK_of_seqCap c4
    · exact PS.pathCapK_of_seqCap c5
  · have hM : PS.SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
      rw [← capF_zero]
      exact c0.mono (by norm_num)
    exact PS.ringCapK_of_ringCapT
      (PS.ringCapT_of_search (by norm_num) (by norm_num) hnR hM hR)

variable {fa da na fb db nb fc dc nc fd dd nd fe de ne : ℕ}

/-- **`Profiles`, from F0 searched by `K16Search.lean` and the five searches FF.** -/
theorem profiles_of_k16 (hn₀ : 0 < n₀) (hna : 0 < na) (hnb : 0 < nb) (hnc : 0 < nc)
    (hnd : 0 < nd) (hne : 0 < ne)
    (h0 : PS.Covered n₀ (K16.seqSearch 7 Ptabs 0 0 84 a₀ b₀ h₀ j₀ f₀ d₀ n₀))
    (ha : PS.Covered na (PS.profSearch 7 Mtab [(66, 36), (66, 36)] fa da na))
    (hb : PS.Covered nb (PS.profSearch 7 Mtab [(50, 26), (50, 26)] fb db nb))
    (hc : PS.Covered nc (PS.profSearch 7 Mtab [(63, 34), (34, 16)] fc dc nc))
    (hd : PS.Covered nd (PS.profSearch 7 Mtab [(66, 36), (31, 14)] fd dd nd))
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne)) :
    Profiles := by
  have c0 : PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 :=
    K16.seqCap_of_k16search (by norm_num) (by norm_num) hn₀
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (PS.seqCapLt_zero _ _ _) h0
  have hM : PS.WCap 7 (fun x => Mtab.getD x 0) 36 := by
    rw [← capF_zero]
    exact PS.wcap_of_seqCap (c0.mono (by norm_num))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hna hM (by decide) (by decide) ha
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnb hM (by decide) (by decide) hb
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnc hM (by decide) (by decide) hc
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hnd hM (by decide) (by decide) hd
  · exact PS.noProfileK_of_search (by norm_num) (by norm_num) hne hM (by decide) (by decide) he

/-- **Every word over `Fin 7` that contains all permutations has at least 5,899 letters**, if the six
searches of `K16Search.lean` and the six searches of `PSearch.lean` answer `false`. -/
theorem covers_5899_of_k16 (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃)
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
    (he : PS.Covered ne (PS.profSearch 7 Mtab [(31, 14), (31, 14), (34, 16), (34, 16)] fe de ne)) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length :=
  covers_5899_of_caps (caps_of_k16 hn₀ hn₁ hn₂ hn₃ hn₄ hn₅ hnR h0 h1 h2 h3 h4 h5 hR)
    (profiles_of_k16 hn₀ hna hnb hnc hnd hne h0 ha hb hc hd he)

end

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.caps_of_k16
#print axioms SuperpermLowerBounds.profiles_of_k16
#print axioms SuperpermLowerBounds.covers_5899_of_k16
