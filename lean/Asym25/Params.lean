import Quantitative.ConstructionParameters

/-!
# Exponent 25: the packing degree `240 r^6` and the frame density

Jay Pantone's `ConstructionParameters` defines `sourceDegree`, `sourceEta`
and `sourceBeta` for his envelope degree (`192 r^7` since the exponent-29
batch). The tied envelopes of `Asym25.Degree` have degree `240 r^6`; the
same definitions and bounds for that degree are here, with the suffix `25`.
The proofs are his, with the numbers changed.
-/

namespace CoefficientTwoPrecision

def sourceDegree25 (r : ℕ) : ℕ := 240 * r ^ 6

def sourceEta25 (r : ℕ) : ℚ :=
  (r.factorial : ℚ) /
    (2 * ((r - 3).factorial : ℚ) * ((sourceDegree25 r : ℚ) + 1))

def sourceBeta25 (r : ℕ) : ℚ := ((r : ℚ) - 2) * sourceEta25 r

def betaPolynomial25 (x : ℚ) : ℚ :=
  x * (x - 1) * (x - 2) ^ 2 / (2 * (240 * x ^ 6 + 1))

theorem sourceEta25_closed_form (r : ℕ) (hr : 3 ≤ r) :
    sourceEta25 r =
      (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) - 2) /
        (2 * (240 * (r : ℚ) ^ 6 + 1)) := by
  have hfac : (r.factorial : ℚ) =
      (r : ℚ) * ((r : ℚ) - 1) * ((r : ℚ) - 2) * ((r - 3).factorial : ℚ) := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
    subst r
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_ofNat]
    ring
  have hfac0 : ((r - 3).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r - 3)
  have hden : (240 : ℚ) * (r : ℚ) ^ 6 + 1 ≠ 0 := by positivity
  unfold sourceEta25 sourceDegree25
  push_cast
  rw [hfac]
  field_simp [hfac0, hden] <;> ring

theorem sourceBeta25_closed_form (r : ℕ) (hr : 3 ≤ r) :
    sourceBeta25 r = betaPolynomial25 (r : ℚ) := by
  unfold sourceBeta25
  rw [sourceEta25_closed_form r hr]
  unfold betaPolynomial25
  ring

/-- A lower bound sharp enough to give the stated constant 352 in the
width estimate, together with the positivity needed for the ceiling. -/
theorem betaPolynomial25_bounds (x : ℚ) (hx : 6 ≤ x) :
    0 < betaPolynomial25 x ∧ betaPolynomial25 x < 1 ∧
      1 / (351 * x ^ 4) ≤ betaPolynomial25 x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℚ) ≤ x := by linarith
  have hxsub1 : 0 < x - 1 := by linarith
  have hxsub2 : 0 < x - 2 := by linarith
  let N : ℚ := x * (x - 1) * (x - 2) ^ 2
  let D : ℚ := 2 * (240 * x ^ 6 + 1)
  have hNpos : 0 < N := mul_pos (mul_pos hx0 hxsub1) (pow_pos hxsub2 2)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have h1 : (5 / 6 : ℚ) * x ≤ x - 1 := by linarith
  have h2 : (2 / 3 : ℚ) * x ≤ x - 2 := by linarith
  have h2sq : ((2 / 3 : ℚ) * x) ^ 2 ≤ (x - 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have hprodLower := mul_le_mul_of_nonneg_left
    (mul_le_mul h1 h2sq (sq_nonneg _) (le_of_lt hxsub1)) (le_of_lt hx0)
  have hNlower : (10 / 27 : ℚ) * x ^ 4 ≤ N := by
    calc
      (10 / 27 : ℚ) * x ^ 4 =
          x * (((5 / 6 : ℚ) * x) * (((2 / 3 : ℚ) * x) ^ 2)) := by ring
      _ ≤ x * ((x - 1) * (x - 2) ^ 2) := hprodLower
      _ = N := by dsimp [N]; ring
  have h2upper : (x - 2) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hxsub2) (by linarith) 2
  have hprodUpper := mul_le_mul_of_nonneg_left
    (mul_le_mul (show x - 1 ≤ x by linarith) h2upper (sq_nonneg _) (le_of_lt hx0))
    (le_of_lt hx0)
  have hNupper : N ≤ x ^ 4 := by
    calc
      N = x * ((x - 1) * (x - 2) ^ 2) := by dsimp [N]; ring
      _ ≤ x * (x * x ^ 2) := hprodUpper
      _ = x ^ 4 := by ring
  have h7 : (1 : ℚ) ≤ x ^ 6 := one_le_pow₀ hx1
  have h47 : x ^ 4 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by decide : 4 ≤ 6)
  have h78 : 36 * x ^ 6 ≤ x ^ 8 := by
    have h : x ^ 8 = x ^ 2 * x ^ 6 := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hDupper : D ≤ 130 * x ^ 8 := by dsimp [D]; linarith only [h7, h78]
  have hNltD : N < D := hNupper.trans_lt (h47.trans_lt (by dsimp [D]; linarith only [h7]))
  change 0 < N / D ∧ N / D < 1 ∧ 1 / (351 * x ^ 4) ≤ N / D
  refine ⟨div_pos hNpos hDpos, ?_, ?_⟩
  · apply (div_lt_iff₀ hDpos).2
    simpa only [one_mul] using hNltD
  · apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 351 * x ^ 4) hDpos).2
    calc
      1 * D = D := by ring
      _ ≤ 130 * x ^ 8 := hDupper
      _ = ((10 / 27 : ℚ) * x ^ 4) * (351 * x ^ 4) := by ring
      _ ≤ N * (351 * x ^ 4) := mul_le_mul_of_nonneg_right hNlower (by positivity)

theorem sourceBeta25_bounds (r : ℕ) (hr : 6 ≤ r) :
    0 < sourceBeta25 r ∧ sourceBeta25 r < 1 ∧
      1 / (351 * (r : ℚ) ^ 4) ≤ sourceBeta25 r := by
  simp only [sourceBeta25_closed_form r (by omega)]
  exact betaPolynomial25_bounds (r : ℚ) (by exact_mod_cast hr)

/-- `CandidateFactorization.eta_pos` for the new density. -/
theorem sourceEta25_pos (r : ℕ) (_hr : 6 ≤ r) : 0 < sourceEta25 r := by
  unfold sourceEta25
  positivity

end CoefficientTwoPrecision

#print axioms CoefficientTwoPrecision.sourceEta25_closed_form
#print axioms CoefficientTwoPrecision.sourceBeta25_bounds
