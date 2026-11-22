import Quantitative.CandidatePositivity

/-!
# The smaller block count

Addition to Jay Pantone's quantitative development (release 9ccbe66).
His source family has `A = ⌈r^3/β⌉` blocks per letter, so that the
normalised density is `ρ = Aβ/r ≥ r^2`; this is used only to make the
pending mass after the sparse blocks at most `4/r`
(`ScheduleArithmetic.sparse_densitySum_ge`). With the blockwise estimate of
`Asym35.Pending` the density `ρ ≥ 4 r (log₂ r + 2)` already gives a
pending mass of at most `1/r`. So here
`A = ⌈4 r^2 (log₂ r + 2)/β⌉` and `ρ ≥ 4 r (log₂ r + 2)`. With the packing
degree `192 r^7` of `Asym29.Degree` the density is `β ≥ 1/(1040 r^3)`, so
`1536 r^5 (log₂ r + 2) ≤ A < 4160 r^5 (log₂ r + 2) + 1`.

The width and the counts that depend on the control grid are in
`Asym28.Width` (transversal design, width `r q` with `q` the least prime
`≥ A`). Earlier batches kept them here, for Jay's grid of width `r^2 A`.
-/

namespace CoefficientTwoPrecision.Asym35

/-! ## The density for the packing degree `192 r^7` -/

theorem betaPolynomial_upper7 (x : ℚ) (hx : 6 ≤ x) :
    betaPolynomial x ≤ 1 / (384 * x ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hxsub1 : 0 < x - 1 := by linarith
  have hxsub2 : 0 < x - 2 := by linarith
  have h2upper : (x - 2) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hxsub2) (by linarith) 2
  have hprodUpper := mul_le_mul_of_nonneg_left
    (mul_le_mul (show x - 1 ≤ x by linarith) h2upper (sq_nonneg _) (le_of_lt hx0))
    (le_of_lt hx0)
  have hNupper : x * (x - 1) * (x - 2) ^ 2 ≤ x ^ 4 := by
    calc
      x * (x - 1) * (x - 2) ^ 2 = x * ((x - 1) * (x - 2) ^ 2) := by ring
      _ ≤ x * (x * x ^ 2) := hprodUpper
      _ = x ^ 4 := by ring
  unfold betaPolynomial
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_right hNupper (show (0 : ℚ) ≤ 384 * x ^ 3 by positivity)
  have e : x ^ 4 * (384 * x ^ 3) = 384 * x ^ 7 := by ring
  rw [e] at h
  linarith

theorem betaPolynomial_lower7 (x : ℚ) (hx : 6 ≤ x) :
    1 / (1040 * x ^ 3) ≤ betaPolynomial x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℚ) ≤ x := by linarith
  have hxsub1 : 0 < x - 1 := by linarith
  have hxsub2 : 0 < x - 2 := by linarith
  have h1 : (5 / 6 : ℚ) * x ≤ x - 1 := by linarith
  have h2 : (2 / 3 : ℚ) * x ≤ x - 2 := by linarith
  have h2sq : ((2 / 3 : ℚ) * x) ^ 2 ≤ (x - 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have hprodLower := mul_le_mul_of_nonneg_left
    (mul_le_mul h1 h2sq (sq_nonneg _) (le_of_lt hxsub1)) (le_of_lt hx0)
  have hNlower : (10 / 27 : ℚ) * x ^ 4 ≤ x * (x - 1) * (x - 2) ^ 2 := by
    calc
      (10 / 27 : ℚ) * x ^ 4 =
          x * (((5 / 6 : ℚ) * x) * (((2 / 3 : ℚ) * x) ^ 2)) := by ring
      _ ≤ x * ((x - 1) * (x - 2) ^ 2) := hprodLower
      _ = x * (x - 1) * (x - 2) ^ 2 := by ring
  have h7 : x ≤ x ^ 7 := le_self_pow₀ hx1 (by decide)
  unfold betaPolynomial
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_right hNlower (show (0 : ℚ) ≤ 1040 * x ^ 3 by positivity)
  have e : (10 / 27 : ℚ) * x ^ 4 * (1040 * x ^ 3) = (10400 / 27) * x ^ 7 := by ring
  rw [e] at h
  linarith

/-! ## The new block count -/

/-- `⌊log₂ r⌋ + 2`. -/
def logFactor (r : ℕ) : ℕ := Nat.log 2 r + 2

/-- Blocks per letter: `⌈4 r^2 (log₂ r + 2) / β⌉`. -/
def sourceA35 (r : ℕ) : ℕ := ⌈4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r⌉₊

def sourceRho35 (r : ℕ) : ℚ := (sourceA35 r : ℚ) * sourceBeta r / (r : ℚ)

theorem logFactor_pos (r : ℕ) : 2 ≤ logFactor r := by
  unfold logFactor; omega

/-- `(log₂ r + 2)^3 ≤ 16 r` for every `r ≥ 1`. -/
theorem logFactor_cube_le (r : ℕ) (hr : 1 ≤ r) : logFactor r ^ 3 ≤ 16 * r := by
  have hpow : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 (by omega)
  have hkey : ∀ L : ℕ, (L + 2) ^ 3 ≤ 16 * 2 ^ L := by
    intro L
    induction L with
    | zero => norm_num
    | succ L ih =>
      rcases Nat.lt_or_ge L 2 with hL | hL
      · interval_cases L <;> norm_num
      · have hstep : (L + 1 + 2) ^ 3 ≤ 2 * (L + 2) ^ 3 := by
          have h3 : 3 * (L + 3) ≤ 4 * (L + 2) + (L - 2) * 1 + 3 := by omega
          nlinarith [sq_nonneg (L + 2), hL]
        calc
          (L + 1 + 2) ^ 3 ≤ 2 * (L + 2) ^ 3 := hstep
          _ ≤ 2 * (16 * 2 ^ L) := Nat.mul_le_mul_left 2 ih
          _ = 16 * 2 ^ (L + 1) := by ring
  unfold logFactor
  exact (hkey (Nat.log 2 r)).trans (Nat.mul_le_mul_left 16 hpow)

/-- `r < 2^(log₂ r + 1)`, so `(1/2)^(logFactor r - 1) ≤ 1/r`. -/
theorem lt_two_pow_log (r : ℕ) : r < 2 ^ (logFactor r - 1) := by
  unfold logFactor
  simpa using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r

theorem sourceA35_pos (r : ℕ) (hr : 6 ≤ r) : 0 < sourceA35 r := by
  have hr0 : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hL : (0 : ℚ) < logFactor r := by
    exact_mod_cast (show 0 < logFactor r by have := logFactor_pos r; omega)
  exact Nat.ceil_pos.mpr (div_pos (by positivity) (sourceBeta_bounds r hr).1)

theorem sourceA35_ceil (r : ℕ) (hr : 6 ≤ r) :
    4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) ≤ (sourceA35 r : ℚ) * sourceBeta r := by
  have hbeta := (sourceBeta_bounds r hr).1
  exact (div_le_iff₀ hbeta).1 (Nat.le_ceil _)

theorem sourceA35_lower (r : ℕ) (hr : 6 ≤ r) : 1536 * r ^ 5 * logFactor r ≤ sourceA35 r := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  have hL : (0 : ℚ) ≤ logFactor r := Nat.cast_nonneg _
  have hbeta := (sourceBeta_bounds r hr).1
  have hupper : sourceBeta r ≤ 1 / (384 * (r : ℚ) ^ 3) := by
    rw [sourceBeta_closed_form r (by omega)]
    exact betaPolynomial_upper7 (r : ℚ) hrQ
  have hquot : 1536 * (r : ℚ) ^ 5 * logFactor r ≤
      4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r := by
    rw [le_div_iff₀ hbeta]
    calc
      1536 * (r : ℚ) ^ 5 * logFactor r * sourceBeta r ≤
          1536 * (r : ℚ) ^ 5 * logFactor r * (1 / (384 * (r : ℚ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = 4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) := by field_simp; ring
  have hceil : 4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r ≤ (sourceA35 r : ℚ) :=
    Nat.le_ceil _
  have h := hquot.trans hceil
  exact_mod_cast h

/-- `A < 4160 r^5 (log₂ r + 2) + 1` (from `β ≥ 1/(1040 r^3)`). -/
theorem sourceA35_upper (r : ℕ) (hr : 6 ≤ r) :
    (sourceA35 r : ℚ) < 4160 * (r : ℚ) ^ 5 * logFactor r + 1 := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  have hL1 : (1 : ℚ) ≤ logFactor r := by
    exact_mod_cast (show 1 ≤ logFactor r by have := logFactor_pos r; omega)
  have hL0 : (0 : ℚ) ≤ logFactor r := by linarith
  obtain ⟨hbeta, _, _⟩ := sourceBeta_bounds r hr
  have hbetalower : 1 / (1040 * (r : ℚ) ^ 3) ≤ sourceBeta r := by
    rw [sourceBeta_closed_form r (by omega)]
    exact betaPolynomial_lower7 (r : ℚ) hrQ
  have hquot : 4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r ≤
      4160 * (r : ℚ) ^ 5 * logFactor r := by
    calc
      4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r ≤
          4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / (1 / (1040 * (r : ℚ) ^ 3)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hbetalower
      _ = 4160 * (r : ℚ) ^ 5 * logFactor r := by field_simp; ring
  have hceil : (sourceA35 r : ℚ) < 4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) / sourceBeta r + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (div_pos (by positivity) hbeta))
  linarith

theorem sourceRho35_lower (r : ℕ) (hr : 6 ≤ r) :
    4 * (r : ℚ) * logFactor r ≤ sourceRho35 r := by
  have hr0 : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have h := sourceA35_ceil r hr
  unfold sourceRho35
  rw [le_div_iff₀ hr0]
  nlinarith

theorem sourceRho35_nonneg (r : ℕ) (hr : 6 ≤ r) : 0 ≤ sourceRho35 r := by
  have h := sourceRho35_lower r hr
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have hL : (0 : ℚ) ≤ logFactor r := Nat.cast_nonneg _
  have : 0 ≤ 4 * (r : ℚ) * logFactor r := by positivity
  linarith

end CoefficientTwoPrecision.Asym35

#print axioms CoefficientTwoPrecision.Asym35.logFactor_cube_le
#print axioms CoefficientTwoPrecision.Asym35.sourceA35_lower
#print axioms CoefficientTwoPrecision.Asym35.sourceA35_upper
#print axioms CoefficientTwoPrecision.Asym35.sourceRho35_lower
