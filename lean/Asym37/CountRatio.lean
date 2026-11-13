import Asym37.Params
import Quantitative.ActualCountEstimates

/-!
# Exponent 37: the ratio form of the count estimates

Addition to Jay Pantone's quantitative development (release 9ccbe66).
`ActualCountEstimates.estimates` writes the row density and the cost rate
with two relative errors `theta`, `epsilon`, each containing every factor
(guards, rounding, retention, background powers, insertions). The transfer
only needs the cost-to-density ratio and a lower bound for the density.
In the ratio all these factors cancel except one background factor
`(m+G)/m ≥ 1`, so only the contour error `u` and the connector error `v`
remain. Here the retention may be as small as `7/8`.
-/

namespace CoefficientTwoPrecision.Asym37

open SuperpermutationUpperBound SourceFamilyAdapter SourceAdvancement
open CandidateFactorization ContourAggregation

/-- The leading coefficient of the cost: `c_r = 2(r-1)/(r-2)`. -/
def costCoefficient (r : ℚ) : ℚ := 2 * (r - 1) / (r - 2)

/-- The ratio allowance `(4r+1)/(4r-1)`, i.e. `(1+1/(4r))/(1-1/(4r))`. -/
def ratioAllowance (r : ℚ) : ℚ := (4 * r + 1) / (4 * r - 1)

/-- The density lower bound from the factor bounds (pure arithmetic). -/
theorem density_from_factors (rw m gf ff t bge u ins : ℚ) (hm : 0 < m) (hrw : 0 ≤ rw)
    (hgf1 : 99 / 100 ≤ gf) (hff1 : 99 / 100 ≤ ff) (ht1 : 7 / 8 ≤ t) (hbg : 1 ≤ bge)
    (hu1 : 99 / 100 ≤ 1 + u) (hins0 : 0 < ins) (hins1 : ins ≤ 101 / 100) :
    rw / (2 * m) ≤ (rw / m) * (gf * ff * t * bge * (1 + u) / ins) := by
  have hgf0 : 0 ≤ gf := by linarith
  have hff0 : 0 ≤ ff := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hbg0 : 0 ≤ bge := by linarith
  have h12 : (99 / 100 : ℚ) * (99 / 100) ≤ gf * ff := mul_le_mul hgf1 hff1 (by norm_num) hgf0
  have h123 : (99 / 100 : ℚ) * (99 / 100) * (7 / 8) ≤ gf * ff * t :=
    mul_le_mul h12 ht1 (by norm_num) (mul_nonneg hgf0 hff0)
  have h1234 : (99 / 100 : ℚ) * (99 / 100) * (7 / 8) * 1 ≤ gf * ff * t * bge :=
    mul_le_mul h123 hbg (by norm_num) (mul_nonneg (mul_nonneg hgf0 hff0) ht0)
  have hX : (99 / 100 : ℚ) * (99 / 100) * (7 / 8) * 1 * (99 / 100) ≤
      gf * ff * t * bge * (1 + u) :=
    mul_le_mul h1234 hu1 (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hgf0 hff0) ht0) hbg0)
  have hhalf : (1 / 2 : ℚ) ≤ gf * ff * t * bge * (1 + u) / ins := by
    rw [le_div_iff₀ hins0]
    linarith
  have hbase : 0 ≤ rw / m := div_nonneg hrw hm.le
  calc
    rw / (2 * m) = (rw / m) * (1 / 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf hbase

/-- The cost ratio from the factorised rates (pure arithmetic). -/
theorem ratio_from_factors (r c rw m P bg u v : ℚ) (hr : 6 ≤ r) (hm : 0 < m) (hc : 0 ≤ c)
    (hrw : 0 ≤ rw) (hP : 0 ≤ P) (hbg : 1 ≤ bg) (hu4 : -(1 / (4 * r)) ≤ u)
    (hv4 : v ≤ 1 / (4 * r)) :
    m * (c * rw / m ^ 2 * (P * (1 + v))) ≤ c * ratioAllowance r * ((rw / m) * (P * bg * (1 + u))) := by
  have hr0 : (0 : ℚ) < 4 * r := by linarith
  have hk : 0 ≤ ratioAllowance r := by
    unfold ratioAllowance; apply div_nonneg <;> linarith
  have hq : 1 / (4 * r) ≤ 1 / 24 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have hu0 : 0 ≤ 1 + u := by linarith
  have h1 : ratioAllowance r * (1 + u) ≤ ratioAllowance r * (bg * (1 + u)) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have := mul_le_mul_of_nonneg_right hbg hu0
    linarith
  have h2 : 1 + 1 / (4 * r) ≤ ratioAllowance r * (1 + u) := by
    have hden : (0 : ℚ) < 4 * r - 1 := by linarith
    have hu' : 1 - 1 / (4 * r) ≤ 1 + u := by linarith
    calc
      1 + 1 / (4 * r) = ratioAllowance r * (1 - 1 / (4 * r)) := by
        unfold ratioAllowance
        field_simp
      _ ≤ ratioAllowance r * (1 + u) := mul_le_mul_of_nonneg_left hu' hk
  have hkey : 1 + v ≤ ratioAllowance r * (bg * (1 + u)) := by linarith
  have hbase : 0 ≤ c * (rw / m) * P := mul_nonneg (mul_nonneg hc (div_nonneg hrw hm.le)) hP
  have hmid := mul_le_mul_of_nonneg_left hkey hbase
  have hlhs : m * (c * rw / m ^ 2 * (P * (1 + v))) = c * (rw / m) * P * (1 + v) := by
    field_simp
  rw [hlhs]
  calc
    c * (rw / m) * P * (1 + v) ≤ c * (rw / m) * P * (ratioAllowance r * (bg * (1 + u))) := hmid
    _ = _ := by ring

theorem estimates37 {alphabet : List Nat} {h : Nat}
    (F : List (SourceContour alphabet h)) (r m K : Nat) (hr : 6 ≤ r)
    (hm : threshold37 r ≤ m)
    (hK : K ≤ 52 * r ^ 4 * sourceWidth r ^ 2)
    (hretention : |(F.length : ℚ) / candidateCount r m - 1| ≤
      deletionNumerator37 r (sourceWidth r) / m)
    (hperturb : ∀ C ∈ F,
      |(C.rows.length : ℚ) - (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 +
        ((r : ℚ) * ((r : ℚ) - 1) + 1) * backgroundSize r m)| ≤
      10 * (r : ℚ) ^ 2 * K * backgroundSize r m)
    (hcharge : ∀ C ∈ F,
      (C.rows.map Row.charge).sum = 2 * (r - 1) * backgroundSize r m)
    (hg : ∀ C ∈ F, portGcd C.rows h ≤ r - 1) :
    sourceRho r * sourceWidth r / (2 * m) ≤
        ((sourceRows F).length : ℚ) / (SourceUniverse.risingCount m (sourceWidth r) : ℚ) ∧
      (m : ℚ) * (((((sourceRows F).map Row.charge).sum : ℚ) + (circles F).length) /
          (SourceUniverse.risingCount m (sourceWidth r) : ℚ)) ≤
        costCoefficient r * ratioAllowance r *
          (((sourceRows F).length : ℚ) / (SourceUniverse.risingCount m (sourceWidth r) : ℚ)) ∧
      ((circles F).length : ℚ) ≤ ((r : ℚ) - 1) *
        (((sourceRows F).map Row.charge).sum : ℚ) / m := by
  have hm0 := (threshold_conditions37 r m hr hm).1
  have hmM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have hcount0 : (candidateCount r m : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (candidate_positive37 r m hr hm)
  -- small errors
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := small_errors37 r m hr hm
  set W := sourceWidth r with hWdef
  have hW1 : (1 : ℚ) ≤ W := by exact_mod_cast ConstructionSize.width_positive r hr
  have hs1Q : 100 * (W : ℚ) ^ 2 ≤ m := by exact_mod_cast hs1
  have hs2Q : 8 * deletionNumerator37 r W ≤ m := by
    unfold deletionNumerator37
    exact_mod_cast hs2
  have hs3Q : 100 * (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) ≤ m := by
    exact_mod_cast hs3
  have hs4Q : 4 * (r : ℚ) * (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) ≤ m := by
    exact_mod_cast hs4
  have hs5Q : 4 * (r : ℚ) * r ≤ m := by exact_mod_cast hs5
  obtain ⟨t, htdef⟩ : ∃ t : ℚ, t = (F.length : ℚ) / candidateCount r m := ⟨_, rfl⟩
  have hcount : (F.length : ℚ) = candidateCount r m * t := by
    rw [htdef]
    field_simp
  obtain ⟨u, hrows, hu⟩ := averaged_row_error F r m (backgroundSize r m)
    W K hr hm0 hmM hK hperturb
  have hconnect := connector_ratio F r m (backgroundSize r m) (by omega) hm0 hmM hcharge hg
  obtain ⟨v, hcost, hv⟩ := ActualCountEstimates.connector_factor
    (((sourceRows F).map Row.charge).sum) (circles F).length ((r : ℚ) - 1) m
    (by positivity) (by positivity) (by linarith) hmQ hconnect
  have hchargeQ : (((sourceRows F).map Row.charge).sum : ℚ) =
      (F.length : ℚ) * (2 * ((r : ℚ) - 1) * backgroundSize r m) := by
    rw [uniform_charge F r (backgroundSize r m) hcharge]
    simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one, Nat.cast_ofNat]
  -- the factors
  have hgf := guard_error37 r m hr hm
  have hff := floor_error37 r m hr hm
  have hins := insertion_error37 r m hr hm
  have hins0 := insertion_pos37 r m hr hm
  have hbg1 := background_ge_one37 r m hr hm 1
  rw [pow_one] at hbg1
  have hbgE := background_ge_one37 r m hr hm (r - 3 + 1)
  have hW2m : (W : ℚ) ^ 2 / m ≤ 1 / 100 := by
    rw [div_le_iff₀ hmQ]; linarith
  have hWm : (W : ℚ) / m ≤ 1 / 100 := by
    rw [div_le_iff₀ hmQ]; nlinarith
  have hgf1 : 99 / 100 ≤ guardFactor r m := by
    have h1 : (W : ℚ) ^ 2 / (2 * m) ≤ 1 / 100 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have := (abs_le.mp hgf).1
    linarith
  have hff1 : 99 / 100 ≤ floorFactor r m := by
    have := (abs_le.mp hff).1
    linarith
  have hins1 : insertionFactor r m ≤ 101 / 100 := by
    have := (abs_le.mp hins).2
    linarith
  have ht1 : 7 / 8 ≤ t := by
    have h1 : deletionNumerator37 r W / m ≤ 1 / 8 := by
      rw [div_le_iff₀ hmQ]; linarith
    have := (abs_le.mp hretention).1
    rw [htdef]
    linarith
  have hU : (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) / m ≤ 1 / 100 := by
    rw [div_le_iff₀ hmQ]; linarith
  have hu1 : 99 / 100 ≤ 1 + u := by
    have := (abs_le.mp hu).1
    linarith
  have hr0 : (0 : ℚ) < 4 * r := by linarith
  have hu4 : -(1 / (4 * (r : ℚ))) ≤ u := by
    have h1 : (2 * (r : ℚ) + 1040 * (r : ℚ) ^ 5 * (W : ℚ) ^ 2) / m ≤ 1 / (4 * r) := by
      rw [div_le_div_iff₀ hmQ hr0]; linarith
    have := (abs_le.mp hu).1
    linarith
  have hv4 : v ≤ 1 / (4 * (r : ℚ)) := by
    have h1 : ((r : ℚ) - 1) / m ≤ 1 / (4 * r) := by
      rw [div_le_div_iff₀ hmQ hr0]
      have e : ((r : ℚ) - 1) * (4 * r) = 4 * r * r - 4 * r := by ring
      linarith
    have := (abs_le.mp hv).2
    linarith
  have hgf0 : 0 ≤ guardFactor r m := by linarith
  have hff0 : 0 ≤ floorFactor r m := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hbg0 : 0 ≤ backgroundFactor r m := by linarith
  have hrho : 0 ≤ sourceRho r * W := by
    have := (sourceRho_bounds r hr).1
    have hW0 : (0 : ℚ) ≤ W := by linarith
    exact mul_nonneg ((sq_nonneg (r : ℚ)).trans this) hW0
  -- exact factorisations of the two rates
  obtain ⟨P, hPdef⟩ : ∃ P : ℚ, P = guardFactor r m * floorFactor r m * t *
    backgroundFactor r m ^ (r - 3 + 1) / insertionFactor r m := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hgf0 hff0) ht0) (pow_nonneg hbg0 _))
      hins0.le
  have hrowsEq : ((sourceRows F).length : ℚ) / (SourceUniverse.risingCount m W : ℚ) =
      (sourceRho r * W / m) * (guardFactor r m * floorFactor r m * t *
        backgroundFactor r m ^ (r - 3 + 2) * (1 + u) / insertionFactor r m) := by
    rw [hrows, hcount]
    calc
      ((candidateCount r m : ℚ) * t * (((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2) * (1 + u)) /
          (SourceUniverse.risingCount m W : ℚ) =
        ((candidateCount r m : ℚ) * ((r : ℚ) - 2) * (backgroundSize r m : ℚ) ^ 2 /
          (SourceUniverse.risingCount m W : ℚ)) * t * (1 + u) := by ring
      _ = _ := by
        rw [actual_leading_rows r m hr hm0]
        ring
  have hcostEq : ((((sourceRows F).map Row.charge).sum : ℚ) + (circles F).length) /
      (SourceUniverse.risingCount m W : ℚ) =
      (costCoefficient r * (sourceRho r * W) / (m : ℚ) ^ 2) * (P * (1 + v)) := by
    rw [hcost, hchargeQ, hcount]
    calc
      ((candidateCount r m : ℚ) * t * (2 * ((r : ℚ) - 1) * backgroundSize r m) * (1 + v)) /
          (SourceUniverse.risingCount m W : ℚ) =
        ((candidateCount r m : ℚ) * (2 * ((r : ℚ) - 1)) * backgroundSize r m /
          (SourceUniverse.risingCount m W : ℚ)) * t * (1 + v) := by ring
      _ = _ := by
        rw [actual_leading_charge r m hr hm0]
        rw [hPdef]
        unfold costCoefficient
        ring
  have hrowsP : ((sourceRows F).length : ℚ) / (SourceUniverse.risingCount m W : ℚ) =
      (sourceRho r * W / m) * (P * backgroundFactor r m * (1 + u)) := by
    rw [hrowsEq, hPdef]
    rw [show r - 3 + 2 = (r - 3 + 1) + 1 by omega, pow_succ]
    ring
  have hc : 0 ≤ costCoefficient r := by
    unfold costCoefficient; apply div_nonneg <;> linarith only [hrQ]
  refine ⟨?_, ?_, hconnect⟩
  · rw [hrowsEq]
    exact density_from_factors _ _ _ _ _ _ _ _ hmQ hrho hgf1 hff1 ht1
      (background_ge_one37 r m hr hm (r - 3 + 2)) hu1 hins0 hins1
  · rw [hcostEq, hrowsP]
    exact ratio_from_factors (r : ℚ) (costCoefficient r) (sourceRho r * W) m P
      (backgroundFactor r m) u v hrQ hmQ hc hrho hP0 hbg1 hu4 hv4

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.estimates37
