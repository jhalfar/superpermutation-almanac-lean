import LowerBounds.PTheorem
import K7.Arith

/-!
# No valid configuration of cost at most 133 on 7 symbols, from the chain caps and the profiles

The coarse part of the accounting of 5,899 (`PTheorem.lean`, `PFamily.lean`) at cost 133 instead of 134.
A valid configuration of cost at most 133 has value at least 55 and weight at most 78 (`acc_value133`,
`acc_weight133`, Lemma ACC with 133 for 134).  Its family of trails (`famC`, Lemma FAM, unchanged) then has
weight `Σ (holes + 6)` at most 84 and value `Σ (rows - holes - 5)` at least 50, whatever the excess of its link
costs.  `family_le_49_8` (Lemma FF of 5,899 for the caps `Wf` of 5,898, trails with at most 78 holes) says that
such a family has value at most 49.  So no link costs, no heavy seams, no rings and no hanging items need to be
looked at: only the chain caps F0 (up to 78 holes) and the five profile statements FF of 5,899.

* `no_config_133 (hC : ChainCap Wf 78) (hF : Profiles)`;
* `covers_5898_of_caps`: every covering word on 7 symbols has at least 5,898 letters.
-/

namespace K7

open SuperpermLowerBounds SuperpermLowerBounds.T5899 Hunter PreimageChain

/-- The pairs of a family of trails obey the chain caps, for weight at most 84. -/
theorem pairs_ok78 {M : ℕ → ℕ} (h0 : ChainCap M 78) {S : List (List (NRow 7))}
    (h : TrailFam 7 S) (hW : lW (prs S) ≤ 84) : ∀ p ∈ prs S, p.2 ≤ M p.1 := by
  intro p hp
  have hx : p.1 ≤ 78 := by
    have := mem_le_lW hp
    omega
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hp
  exact chain_cap_rows h0 (h.trails A hA) (h.classes.sublist (rowsEntries_sublist_flatten hA)) hx

/-- **Lemma FF for 5,898.**  A family of trails of weight at most 84 has value at most 49. -/
theorem family_le_49_8 (h0 : ChainCap Wf 78) (hF : Profiles) {S : List (List (NRow 7))}
    (h : TrailFam 7 S) (hW : lW (prs S) ≤ 84) : lE (prs S) ≤ 49 := by
  by_contra hcon
  have hE : 50 ≤ lE (prs S) := by omega
  have hok : lOK8 (prs S) := pairs_ok78 h0 h hW
  have hnd := h.nodup
  have key := profile_of_family8 hok hW hE
  have pair : ∀ {A B : List (NRow 7)}, A ∈ S → B ∈ S → A ≠ B → TrailFam 7 [A, B] := by
    intro A B hA hB hne
    refine h.of_subperm (List.Nodup.subperm ?_ ?_)
    · simp [hne]
    · intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
  unfold prs at key
  rcases key with k1 | k1 | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    simp only [Prod.mk.injEq] at fA fB
    refine noProfile_rows hF.p36 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    simp only [Prod.mk.injEq] at fA fB
    refine noProfile_rows hF.p26 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, hA, fA⟩ := exists_of_count_one _ _ k1
    obtain ⟨B, hB, fB⟩ := exists_of_count_one _ _ k2
    simp only [Prod.mk.injEq] at fA fB
    have hne : A ≠ B := by
      rintro rfl
      omega
    refine noProfile_rows hF.p34 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, hA, fA⟩ := exists_of_count_one _ _ k1
    obtain ⟨B, hB, fB⟩ := exists_of_count_one _ _ k2
    simp only [Prod.mk.injEq] at fA fB
    have hne : A ≠ B := by
      rintro rfl
      omega
    refine noProfile_rows hF.p14 (pair hA hB hne) ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)
  · obtain ⟨A, B, hA, hB, hne, fA, fB⟩ := exists_of_count_two _ _ hnd k1
    obtain ⟨C, D, hC, hD, hne', fC, fD⟩ := exists_of_count_two _ _ hnd k2
    simp only [Prod.mk.injEq] at fA fB fC fD
    have hfam : TrailFam 7 [A, B, C, D] := by
      refine h.of_subperm (List.Nodup.subperm ?_ ?_)
      · have h1 : A ≠ C := by rintro rfl; omega
        have h2 : A ≠ D := by rintro rfl; omega
        have h3 : B ≠ C := by rintro rfl; omega
        have h4 : B ≠ D := by rintro rfl; omega
        simp [hne, hne', h1, h2, h3, h4]
      · intro X hX
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
        rcases hX with rfl | rfl | rfl | rfl
        · exact hA
        · exact hB
        · exact hC
        · exact hD
    refine noProfile_rows hF.p4 hfam ?_
    exact .cons ⟨by simp only; omega, by simp only; omega⟩
      (.cons ⟨by simp only; omega, by simp only; omega⟩
        (.cons ⟨by simp only; omega, by simp only; omega⟩
          (.cons ⟨by simp only; omega, by simp only; omega⟩ .nil)))

/-- **Lemma ACC at cost 133, values.** -/
theorem acc_value133 {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 133) :
    55 ≤ valR c.kernel (rX c.kernel) + (c.hanging.map vH).sum := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  rw [valR_eq hlen.1, sum_vH c.hanging hlen.2]
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 133 := by
    exact_mod_cast (hC ▸ hc)
  linarith

/-- **Lemma ACC at cost 133, weights.** -/
theorem acc_weight133 {c : NConfig 7} (hv : c.Valid) (hc : c.cost ≤ 133) :
    wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum ≤ 78 := by
  have hlen := hv.len_le (by norm_num : 2 ≤ 7)
  have hE := entries_length_ge hv
  have hEl : c.entries.length =
      (rowsEntries c.kernel).length + (c.hanging.flatMap fun H => rowsEntries H.rows).length := by
    unfold NConfig.entries
    rw [List.length_append]
  have hC : c.cost = (c.kernel.length + rX c.kernel) + (c.hanging.map NHanging.cost).sum := rfl
  have h0 := wtR_eq hlen.1 (rX c.kernel)
  have h3 := sum_wH c.hanging hlen.2
  have h1 : (720 : ℤ) ≤ ((rowsEntries c.kernel).length : ℤ) +
      ((c.hanging.flatMap fun H => rowsEntries H.rows).length : ℤ) := by
    exact_mod_cast (hEl ▸ hE)
  have h2 : ((c.kernel.length + rX c.kernel : ℕ) : ℤ) +
      (((c.hanging.map NHanging.cost).sum : ℕ) : ℤ) ≤ 133 := by
    exact_mod_cast (hC ▸ hc)
  have : ((wtR c.kernel (rX c.kernel) + (c.hanging.map wH).sum : ℕ) : ℤ) ≤ 78 := by
    rw [Nat.cast_add]
    linarith
  exact_mod_cast this

/-- **No valid configuration of cost at most 133**, from the chain caps and the profiles. -/
theorem no_config_133 (hC : ChainCap Wf 78) (hF : Profiles) (c : NConfig 7) (hv : c.Valid) :
    ¬ c.cost ≤ 133 := by
  intro hc
  have hav := acc_value133 hv hc
  have haw := acc_weight133 hv hc
  obtain ⟨n1, n2⟩ := famC_num hv
  have hfam := famC_trailFam hv
  have hW : lW (prs (famC c)) ≤ 84 := by omega
  have hE := family_le_49_8 hC hF hfam hW
  have h0 : (0 : ℤ) ≤ (epsC c : ℤ) := Int.natCast_nonneg _
  linarith

/-- **Every covering word on 7 symbols has at least 5,898 letters**, from the chain caps and the
profiles. -/
theorem covers_5898_of_caps (hC : ChainCap Wf 78) (hF : Profiles) :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5898 ≤ w.length := by
  have e1 : (7 - 2).factorial + 13 = 133 := by decide
  have e2 : hpv 7 + 13 + 1 = 5898 := by decide
  have h := covers_length_gt_of_no_stdConfig (k := 7) (by norm_num) 13
    (by rw [e1]; exact no_config_133 hC hF)
  rw [e2] at h
  exact h

end K7

#print axioms K7.no_config_133
#print axioms K7.covers_5898_of_caps
