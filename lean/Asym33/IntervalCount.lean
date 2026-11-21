import Quantitative.LinearCount

/-!
# Exponent 33: counting a linear form that lands in an interval

Addition to Jay Pantone's quantitative development (release 9ccbe66).
Jay's `ModularRoots.integer_root_count` bounds the roots of one congruence
`a x ≡ b (mod M)` by `|a|`. The proximity deletion of `Asym37` applies it
once for every constant `b` of an interval of length `K`, which gives
`K |a|`. Here the whole interval is counted at once: the values `|a| x`,
`0 ≤ x < M`, are `|a|` apart and meet at most `|a| + 1` translates of the
interval, so at most `(|a| + 1)((K - 1)/|a| + 1) ≤ 2K + |a|` residues `x`
have `a x ≡ c` for some `c` in the interval.
-/

namespace CoefficientTwoPrecision.Asym33

theorem emod_le_self_of_nonneg (t m : ℤ) (hm : 0 < m) (ht : 0 ≤ t) : t % m ≤ t := by
  have h := Int.mul_ediv_add_emod t m
  have hq := Int.ediv_nonneg ht hm.le
  nlinarith


open Classical in
/-- The positive form: `(n x - lo) mod M < K` has at most `(n+1)((K-1)/n+1)` solutions. -/
theorem shifted_residue_count (M n : ℕ) (hM : 0 < M) (hn : 0 < n) (lo : ℤ) (K : ℕ) :
    (Finset.univ.filter (fun x : Fin M => ((n : ℤ) * x.val - lo) % (M : ℤ) < (K : ℤ))).card ≤
      (n + 1) * ((K - 1) / n + 1) := by
  classical
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  set kmin : ℤ := (-lo) / (M : ℤ) with hkmin
  have hk0 := Int.mul_ediv_add_emod (-lo) (M : ℤ)
  have hr0 := Int.emod_nonneg (-lo) (ne_of_gt hMZ)
  have hr0' := Int.emod_lt_of_pos (-lo) hMZ
  rw [← hkmin] at hk0
  let f : Fin M → ℕ × ℕ := fun x =>
    ((((n : ℤ) * x.val - lo) / (M : ℤ) - kmin).toNat,
      ((((n : ℤ) * x.val - lo) % (M : ℤ)) / (n : ℤ)).toNat)
  have hfacts (x : Fin M) :
      (M : ℤ) * (((n : ℤ) * x.val - lo) / (M : ℤ)) + ((n : ℤ) * x.val - lo) % (M : ℤ) =
        (n : ℤ) * x.val - lo ∧
      0 ≤ ((n : ℤ) * x.val - lo) % (M : ℤ) ∧ ((n : ℤ) * x.val - lo) % (M : ℤ) < M ∧
      0 ≤ ((n : ℤ) * x.val - lo) / (M : ℤ) - kmin ∧
      ((n : ℤ) * x.val - lo) / (M : ℤ) - kmin ≤ n := by
    set Y : ℤ := (n : ℤ) * x.val - lo with hY
    have h1 := Int.mul_ediv_add_emod Y (M : ℤ)
    have h2 := Int.emod_nonneg Y (ne_of_gt hMZ)
    have h3 := Int.emod_lt_of_pos Y hMZ
    have hx0 : (0 : ℤ) ≤ x.val := Nat.cast_nonneg _
    have hxM : (x.val : ℤ) ≤ (M : ℤ) - 1 := by
      have := x.isLt
      omega
    have hYlo : -lo ≤ Y := by
      have : (0 : ℤ) ≤ (n : ℤ) * x.val := mul_nonneg hnZ.le hx0
      linarith
    have hYhi : Y ≤ (n : ℤ) * ((M : ℤ) - 1) - lo := by
      have := mul_le_mul_of_nonneg_left hxM hnZ.le
      linarith
    set q : ℤ := Y / (M : ℤ)
    set ρ : ℤ := Y % (M : ℤ)
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · by_contra hneg
      have hle : q - kmin + 1 ≤ 0 := by omega
      have := mul_le_mul_of_nonneg_left hle hMZ.le
      nlinarith
    · by_contra hbig
      have hge : (n : ℤ) + 1 ≤ q - kmin := by omega
      have := mul_le_mul_of_nonneg_left hge hMZ.le
      nlinarith
  have hmap : Set.MapsTo f
      ((Finset.univ.filter (fun x : Fin M => ((n : ℤ) * x.val - lo) % (M : ℤ) < (K : ℤ))) :
        Set (Fin M))
      ((Finset.range (n + 1) ×ˢ Finset.range ((K - 1) / n + 1) : Finset (ℕ × ℕ)) :
        Set (ℕ × ℕ)) := by
    intro x hx
    have hK := (Finset.mem_filter.mp hx).2
    obtain ⟨_, h2, _, h4, h5⟩ := hfacts x
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, f]
    constructor
    · omega
    · have hK1 : 1 ≤ K := by omega
      have hle : ((n : ℤ) * x.val - lo) % (M : ℤ) ≤ ((K - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hK1]; push_cast; omega
      have hdiv := Int.ediv_le_ediv hnZ hle
      rw [← Int.natCast_ediv] at hdiv
      have hq0 : 0 ≤ (((n : ℤ) * x.val - lo) % (M : ℤ)) / (n : ℤ) := Int.ediv_nonneg h2 hnZ.le
      omega
  have hinj : Set.InjOn f
      ((Finset.univ.filter (fun x : Fin M => ((n : ℤ) * x.val - lo) % (M : ℤ) < (K : ℤ))) :
        Set (Fin M)) := by
    intro x _ y _ hxy
    obtain ⟨hx1, hx2, _, hx4, _⟩ := hfacts x
    obtain ⟨hy1, hy2, _, hy4, _⟩ := hfacts y
    have hfst := congrArg Prod.fst hxy
    have hsnd := congrArg Prod.snd hxy
    simp only [f] at hfst hsnd
    have hq : ((n : ℤ) * x.val - lo) / (M : ℤ) = ((n : ℤ) * y.val - lo) / (M : ℤ) := by omega
    have hdx := Int.mul_ediv_add_emod (((n : ℤ) * x.val - lo) % (M : ℤ)) (n : ℤ)
    have hdy := Int.mul_ediv_add_emod (((n : ℤ) * y.val - lo) % (M : ℤ)) (n : ℤ)
    have hex := Int.emod_lt_of_pos (((n : ℤ) * x.val - lo) % (M : ℤ)) hnZ
    have hey := Int.emod_lt_of_pos (((n : ℤ) * y.val - lo) % (M : ℤ)) hnZ
    have hfx := Int.emod_nonneg (((n : ℤ) * x.val - lo) % (M : ℤ)) (ne_of_gt hnZ)
    have hfy := Int.emod_nonneg (((n : ℤ) * y.val - lo) % (M : ℤ)) (ne_of_gt hnZ)
    have hqx := Int.ediv_nonneg hx2 hnZ.le
    have hqy := Int.ediv_nonneg hy2 hnZ.le
    have hd : (((n : ℤ) * x.val - lo) % (M : ℤ)) / (n : ℤ) =
        (((n : ℤ) * y.val - lo) % (M : ℤ)) / (n : ℤ) := by omega
    rw [hq] at hx1
    rw [hd] at hdx
    -- n (x - y) is the difference of the two residues, which is less than n in size
    have hdiff : (n : ℤ) * ((x.val : ℤ) - y.val) =
        ((n : ℤ) * x.val - lo) % (M : ℤ) - ((n : ℤ) * y.val - lo) % (M : ℤ) := by linarith
    have hlt : (n : ℤ) * ((x.val : ℤ) - y.val) < n := by linarith
    have hgt : -(n : ℤ) < (n : ℤ) * ((x.val : ℤ) - y.val) := by linarith
    have hxy0 : (x.val : ℤ) - y.val = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have h' : (x.val : ℤ) - y.val ≤ -1 := by omega
        have := mul_le_mul_of_nonneg_left h' hnZ.le
        linarith
      · have h' : (1 : ℤ) ≤ (x.val : ℤ) - y.val := by omega
        have := mul_le_mul_of_nonneg_left h' hnZ.le
        linarith
    exact Fin.ext (by omega)
  have h := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [Finset.card_product, Finset.card_range] using h

open Classical in
/-- One coordinate: `a x ≡ c (mod M)` for some `c` in `[lo, lo + K)`. -/
theorem interval_root_count (M : ℕ) (hM : 0 < M) (a lo : ℤ) (K : ℕ) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : Fin M =>
      ∃ c : ℤ, lo ≤ c ∧ c < lo + K ∧ Int.ModEq (M : ℤ) (a * x.val) c)).card ≤
      (a.natAbs + 1) * ((K - 1) / a.natAbs + 1) := by
  classical
  have hn : 0 < a.natAbs := Int.natAbs_pos.mpr ha
  rcases le_or_gt 0 a with hpos | hneg
  · have ha' : a = (a.natAbs : ℤ) := (Int.natAbs_of_nonneg hpos).symm
    refine le_trans (Finset.card_le_card ?_) (shifted_residue_count M a.natAbs hM hn lo K)
    intro x hx
    obtain ⟨c, hc1, hc2, hc⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hmod : Int.ModEq (M : ℤ) ((a.natAbs : ℤ) * x.val - lo) (c - lo) := by
      rw [← ha']; exact hc.sub_right lo
    rw [hmod]
    have h0 : 0 ≤ c - lo := by linarith
    have hle := emod_le_self_of_nonneg (c - lo) (M : ℤ) (by positivity) h0
    omega
  · have ha' : a = -(a.natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos hneg.le]; ring
    refine le_trans (Finset.card_le_card ?_)
      (shifted_residue_count M a.natAbs hM hn (-(lo + K - 1)) K)
    intro x hx
    obtain ⟨c, hc1, hc2, hc⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hmod : Int.ModEq (M : ℤ) ((a.natAbs : ℤ) * x.val - -(lo + K - 1)) (lo + K - 1 - c) := by
      have h1 : Int.ModEq (M : ℤ) (-(a * x.val)) (-c) := hc.neg
      rw [ha'] at h1
      have h2 := h1.add_right (lo + K - 1)
      convert h2 using 1 <;> ring
    rw [hmod]
    have h0 : 0 ≤ lo + K - 1 - c := by linarith
    have hle := emod_le_self_of_nonneg (lo + K - 1 - c) (M : ℤ) (by positivity) h0
    omega

open Classical in
/-- A linear form in several coordinates, one of them with a nonzero coefficient, lands in an
interval of length `K` (modulo `M`) for at most `M^(d-1) (|a_j| + 1)((K-1)/|a_j| + 1)` points. -/
theorem linear_interval_count (M d : ℕ) (hM : 0 < M) (a : Fin d → ℤ) (lo : ℤ) (K : ℕ)
    (j : Fin d) (ha : a j ≠ 0) :
    (Finset.univ.filter (fun x : Fin d → Fin M =>
      ∃ c : ℤ, lo ≤ c ∧ c < lo + K ∧ Int.ModEq (M : ℤ) (∑ i, a i * (x i).val) c)).card ≤
      M ^ (d - 1) * ((a j).natAbs + 1) * ((K - 1) / (a j).natAbs + 1) := by
  classical
  let S := Finset.univ.filter (fun x : Fin d → Fin M =>
      ∃ c : ℤ, lo ≤ c ∧ c < lo + K ∧ Int.ModEq (M : ℤ) (∑ i, a i * (x i).val) c)
  let g : (Fin d → Fin M) → ({i : Fin d // i ≠ j} → Fin M) := fun x i => x i.val
  have hcard : Fintype.card {i : Fin d // i ≠ j} = d - 1 := by
    rw [Fintype.card_subtype_compl (fun i : Fin d => i = j)]
    simp
  have hproduct : Fintype.card ({i : Fin d // i ≠ j} → Fin M) = M ^ (d - 1) := by
    simp [hcard]
  have hfiber : ∀ y ∈ (Finset.univ : Finset ({i : Fin d // i ≠ j} → Fin M)),
      (S.filter (fun x => g x = y)).card ≤
        ((a j).natAbs + 1) * ((K - 1) / (a j).natAbs + 1) := by
    intro y _
    let R := LinearCount.restSum j a y
    let T := Finset.univ.filter (fun t : Fin M =>
      ∃ c : ℤ, lo - R ≤ c ∧ c < lo - R + K ∧ Int.ModEq (M : ℤ) (a j * t.val) c)
    have hmap : Set.MapsTo (fun x : Fin d → Fin M => x j)
        ((S.filter (fun x => g x = y)) : Set (Fin d → Fin M)) (T : Set (Fin M)) := by
      intro x hx
      obtain ⟨hxS, hgx⟩ := Finset.mem_filter.mp hx
      obtain ⟨c, hc1, hc2, hc⟩ := (Finset.mem_filter.mp hxS).2
      have hsplit := LinearCount.split_sum j a x
      have hrest : LinearCount.restSum j a (fun i => x i.val) = R := by
        simp only [R]; rw [← hgx]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, c - R, by linarith, by linarith, ?_⟩
      rw [hsplit, hrest] at hc
      have := hc.sub_right R
      simpa using this
    have hinj : ((S.filter (fun x => g x = y)) : Set (Fin d → Fin M)).InjOn
        (fun x : Fin d → Fin M => x j) := by
      intro x hx x' hx' hjx
      have hgx := (Finset.mem_filter.mp hx).2
      have hgx' := (Finset.mem_filter.mp hx').2
      funext i
      by_cases hi : i = j
      · subst hi; exact hjx
      · have := congrFun (hgx.trans hgx'.symm) ⟨i, hi⟩
        exact this
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
      (interval_root_count M hM (a j) (lo - R) K ha)
  have h := FiniteFibers.card_le_of_fiber_bound S Finset.univ g _
    (fun _ _ => Finset.mem_univ _) hfiber
  rw [Finset.card_univ, hproduct] at h
  calc
    S.card ≤ M ^ (d - 1) * (((a j).natAbs + 1) * ((K - 1) / (a j).natAbs + 1)) := h
    _ = M ^ (d - 1) * ((a j).natAbs + 1) * ((K - 1) / (a j).natAbs + 1) := by ring

end CoefficientTwoPrecision.Asym33

#print axioms CoefficientTwoPrecision.Asym33.shifted_residue_count
#print axioms CoefficientTwoPrecision.Asym33.interval_root_count
#print axioms CoefficientTwoPrecision.Asym33.linear_interval_count
