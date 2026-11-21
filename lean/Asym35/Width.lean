import Quantitative.CandidatePositivity
import Quantitative.SourceSelection

/-!
# The smaller block count and the width-dependent definitions

Addition to Jay Pantone's quantitative development (release 9ccbe66).
His source family has `A = ⌈r^3/β⌉` blocks per letter, so that the
normalised density is `ρ = Aβ/r ≥ r^2`; this is used only to make the
pending mass after the sparse blocks at most `4/r`
(`ScheduleArithmetic.sparse_densitySum_ge`). With the blockwise estimate of
`Asym35.Pending` the density `ρ ≥ 4 r (log₂ r + 2)` already gives a
pending mass of at most `1/r`. So here
`A = ⌈4 r^2 (log₂ r + 2)/β⌉` and `ρ ≥ 4 r (log₂ r + 2)`. With the packing
degree `192 r^7` of `Asym29.Degree` the density is `β ≥ 1/(1040 r^3)`, so the
width is `W = r^2 A ≤ 4161 r^7 (log₂ r + 2)` (with the degree `64 r^8` it was
`1405 r^8 (log₂ r + 2)`, and `352 r^9` with Jay's `A`).

The rest of this file repeats, for the new `A`, the definitions and lemmas
of Jay's `CandidateFactorization`, `ConstructionSize`, `CandidateSpace`,
`SourceSelection` and `ElementaryCountFactors` that mention `sourceA` or
`sourceWidth`. The proofs are his, with the names changed (suffix `35`);
the geometry they rely on (`GuardCatalogue`, `CandidateSpace.candidates`,
`CatalogueBounds.width`, ...) is generic in `A` and is used unchanged.
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

def sourceWidth35 (r : ℕ) : ℕ := r ^ 2 * sourceA35 r

def sourceRho35 (r : ℕ) : ℚ := (sourceA35 r : ℚ) * sourceBeta r / (r : ℚ)

def sourceGridCount35 (r : ℕ) : ℕ := r * sourceA35 r ^ 2

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

theorem sourceWidth35_lower7 (r : ℕ) (hr : 6 ≤ r) :
    1536 * r ^ 7 * logFactor r ≤ sourceWidth35 r := by
  have h := Nat.mul_le_mul_left (r ^ 2) (sourceA35_lower r hr)
  calc
    1536 * r ^ 7 * logFactor r = r ^ 2 * (1536 * r ^ 5 * logFactor r) := by ring
    _ ≤ r ^ 2 * sourceA35 r := h
    _ = sourceWidth35 r := rfl

theorem sourceWidth35_lower (r : ℕ) (hr : 6 ≤ r) : r ^ 2 ≤ sourceWidth35 r := by
  have hA : 1 ≤ sourceA35 r := sourceA35_pos r hr
  simpa only [Nat.mul_one, sourceWidth35] using Nat.mul_le_mul_left (r ^ 2) hA

theorem sourceWidth35_dvd (r : ℕ) : r ∣ sourceWidth35 r := by
  refine ⟨r * sourceA35 r, ?_⟩
  unfold sourceWidth35
  ring

theorem sourceWidth35_upper (r : ℕ) (hr : 6 ≤ r) :
    sourceWidth35 r ≤ 4161 * r ^ 7 * logFactor r := by
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
  have hA : (sourceA35 r : ℚ) < 4160 * (r : ℚ) ^ 5 * logFactor r + 1 := by linarith
  have hwidth : (sourceWidth35 r : ℚ) < 4160 * (r : ℚ) ^ 7 * logFactor r + (r : ℚ) ^ 2 := by
    calc
      (sourceWidth35 r : ℚ) = (r : ℚ) ^ 2 * (sourceA35 r : ℚ) := by
        simp only [sourceWidth35, Nat.cast_mul, Nat.cast_pow]
      _ < (r : ℚ) ^ 2 * (4160 * (r : ℚ) ^ 5 * logFactor r + 1) :=
        mul_lt_mul_of_pos_left hA (pow_pos hr0 2)
      _ = 4160 * (r : ℚ) ^ 7 * logFactor r + (r : ℚ) ^ 2 := by ring
  have h28 : (r : ℚ) ^ 2 ≤ (r : ℚ) ^ 7 :=
    pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ r) (by decide : 2 ≤ 7)
  have h28L : (r : ℚ) ^ 2 ≤ (r : ℚ) ^ 7 * logFactor r := by
    have := mul_le_mul_of_nonneg_left hL1 (pow_nonneg hr0.le 7)
    linarith
  have hwidthQ : (sourceWidth35 r : ℚ) ≤ 4161 * (r : ℚ) ^ 7 * logFactor r := by
    linarith only [hwidth, h28L]
  exact_mod_cast hwidthQ

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

/-- `CountingRatios`' coefficient identity for the new `A`. -/
theorem source_coefficient_identity35 (r : ℕ) (hr : 0 < r) :
    (sourceGridCount35 r : ℚ) * sourceBeta r = sourceRho35 r * (sourceWidth35 r : ℚ) := by
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  simp only [sourceGridCount35, sourceRho35, sourceWidth35, Nat.cast_mul, Nat.cast_pow]
  field_simp [hrQ]

/-- `ElementaryCountFactors.sourceEta_width` for the new `A`. -/
theorem sourceEta_width35 (r : ℕ) (hr : 6 ≤ r) :
    1 ≤ (sourceWidth35 r : ℚ) * sourceEta r := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  have heta : 0 ≤ sourceEta r := by unfold sourceEta; positivity
  have hA : (0 : ℚ) ≤ sourceA35 r := Nat.cast_nonneg _
  have hL : (2 : ℚ) ≤ logFactor r := by exact_mod_cast logFactor_pos r
  have hceil := sourceA35_ceil r hr
  unfold sourceBeta at hceil
  -- A β = A (r-2) η ≤ r (A η), and A β ≥ 4 r^2 L ≥ r, so A η ≥ 1
  have hAeta : 1 ≤ (sourceA35 r : ℚ) * sourceEta r := by
    by_contra hsmall
    have hlt : (sourceA35 r : ℚ) * sourceEta r < 1 := lt_of_not_ge hsmall
    have h1 : (sourceA35 r : ℚ) * (((r : ℚ) - 2) * sourceEta r) ≤
        (r : ℚ) * ((sourceA35 r : ℚ) * sourceEta r) := by
      have hp : 0 ≤ (sourceA35 r : ℚ) * sourceEta r := mul_nonneg hA heta
      nlinarith
    have h2 : (r : ℚ) * ((sourceA35 r : ℚ) * sourceEta r) < r :=
      by nlinarith
    have h3 : (r : ℚ) ≤ 4 * (r : ℚ) ^ 2 * (logFactor r : ℚ) := by nlinarith
    linarith
  have hpower : (1 : ℚ) ≤ (r : ℚ) ^ 2 := by nlinarith
  have h := mul_le_mul hpower hAeta (by norm_num : (0 : ℚ) ≤ 1) (sq_nonneg (r : ℚ))
  simpa only [sourceWidth35, Nat.cast_mul, Nat.cast_pow, mul_assoc, one_mul] using h

/-! ## `CandidateFactorization` for the new `A` -/

def guardCount35 (r : Nat) : Nat := sourceWidth35 r - r

def backgroundSize35 (r m : Nat) : Nat := m + guardCount35 r

def candidateCount35 (r m : Nat) : Nat :=
  sourceGridCount35 r * m.descFactorial (guardCount35 r) *
    ⌊sourceEta r * (backgroundSize35 r m : ℚ) ^ (r - 3)⌋₊

def guardFactor35 (r m : Nat) : ℚ :=
  (m.descFactorial (guardCount35 r) : ℚ) / (m : ℚ) ^ guardCount35 r

def floorFactor35 (r m : Nat) : ℚ :=
  (⌊sourceEta r * (backgroundSize35 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize35 r m : ℚ) ^ (r - 3))

def backgroundFactor35 (r m : Nat) : ℚ := (backgroundSize35 r m : ℚ) / m

def insertionFactor35 (r m : Nat) : ℚ :=
  (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) / (m : ℚ) ^ sourceWidth35 r

theorem width_exponents35 (r : Nat) (hr : 6 ≤ r) :
    guardCount35 r + (r - 3) + 3 = sourceWidth35 r := by
  have hlower := sourceWidth35_lower r hr
  have hlinear : r ≤ r ^ 2 := by nlinarith
  unfold guardCount35
  omega

theorem actual_leading_rows35 (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount35 r m : ℚ) * ((r : ℚ) - 2) * (backgroundSize35 r m : ℚ) ^ 2 /
        (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) =
      (sourceRho35 r * sourceWidth35 r / m) *
        (guardFactor35 r m * floorFactor35 r m * backgroundFactor35 r m ^ (r - 3 + 2) /
          insertionFactor35 r m) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize35 r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize35 r m ≠ 0 by unfold backgroundSize35; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth35 r) hm)
  have h := CandidateFactorization.leading_row_identity (m : ℚ) (backgroundSize35 r m : ℚ)
    (sourceGridCount35 r : ℚ) (sourceEta r) (m.descFactorial (guardCount35 r) : ℚ)
    (⌊sourceEta r * (backgroundSize35 r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) ((r : ℚ) - 2)
    (guardCount35 r) (r - 3) hmQ hM (ne_of_gt (CandidateFactorization.eta_pos r hr)) hD
  rw [width_exponents35 r hr, ← sourceBeta,
    source_coefficient_identity35 r (by omega)] at h
  simpa only [candidateCount35, Nat.cast_mul, guardFactor35, floorFactor35,
    backgroundFactor35, insertionFactor35] using h

theorem actual_leading_charge35 (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount35 r m : ℚ) * (2 * ((r : ℚ) - 1)) * (backgroundSize35 r m : ℚ) /
        (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) =
      ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho35 r * sourceWidth35 r / m ^ 2) *
        (guardFactor35 r m * floorFactor35 r m * backgroundFactor35 r m ^ (r - 3 + 1) /
          insertionFactor35 r m) := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize35 r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize35 r m ≠ 0 by unfold backgroundSize35; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth35 r) hm)
  have hcoef : (sourceGridCount35 r : ℚ) * (2 * ((r : ℚ) - 1) * sourceEta r) =
      (2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho35 r * sourceWidth35 r := by
    rw [mul_assoc _ (sourceRho35 r), ← source_coefficient_identity35 r (by omega)]
    unfold sourceBeta
    field_simp [show (r : ℚ) - 2 ≠ 0 by linarith]
  have h := CandidateFactorization.leading_charge_identity (m : ℚ) (backgroundSize35 r m : ℚ)
    (sourceGridCount35 r : ℚ) (sourceEta r) (m.descFactorial (guardCount35 r) : ℚ)
    (⌊sourceEta r * (backgroundSize35 r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth35 r) : ℚ) (2 * ((r : ℚ) - 1))
    (guardCount35 r) (r - 3) hmQ hM (ne_of_gt (CandidateFactorization.eta_pos r hr)) hD
  rw [width_exponents35 r hr, hcoef] at h
  simpa only [candidateCount35, Nat.cast_mul, guardFactor35, floorFactor35,
    backgroundFactor35, insertionFactor35] using h

/-! ## `ConstructionSize`, `CandidateSpace`, `SourceSelection` for the new `A` -/

theorem width_positive35 (r : Nat) (hr : 6 ≤ r) : 1 ≤ sourceWidth35 r := by
  have h := sourceWidth35_lower r hr
  nlinarith

theorem width_linear35 (r : Nat) (hr : 6 ≤ r) : r ≤ sourceWidth35 r := by
  have h := sourceWidth35_lower r hr
  nlinarith

theorem guard_number_eq35 (d : Nat) :
    GuardCatalogue.guardNumber d (sourceA35 (d + 3)) = guardCount35 (d + 3) := by
  unfold GuardCatalogue.guardNumber guardCount35 sourceWidth35
  congr 1
  ring

theorem prescribed_card35 (m d : Nat)
    (S : Finset (LabelledReconstruction.Labelled
      (m + GuardCatalogue.guardNumber d (sourceA35 (d + 3))) d))
    (hS : S.card = ⌊sourceEta (d + 3) *
      ((m + GuardCatalogue.guardNumber d (sourceA35 (d + 3)) : Nat) : ℚ) ^ d⌋₊) :
    (CandidateSpace.candidates m d (sourceA35 (d + 3)) S).card =
      candidateCount35 (d + 3) m := by
  rw [CandidateSpace.candidates_card, hS, guard_number_eq35]
  unfold candidateCount35 backgroundSize35
  simp only [Nat.add_sub_cancel, sourceGridCount35]
  ring

theorem background_divisible35 (d m : Nat) (_hd : 3 ≤ d) (hm : d + 3 ∣ m) :
    d + 3 ∣ m + GuardCatalogue.guardNumber d (sourceA35 (d + 3)) := by
  apply dvd_add hm
  unfold GuardCatalogue.guardNumber
  exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_refl _)

theorem contour_height35 (d m : Nat) (hd : 3 ≤ d) :
    m + GuardCatalogue.guardNumber d (sourceA35 (d + 3)) + (d + 2) - 1 =
      m + sourceWidth35 (d + 3) - 2 := by
  rw [guard_number_eq35]
  have hwidth := width_linear35 (d + 3) (by omega)
  unfold guardCount35
  omega

theorem control_width35 (d : Nat) :
    sourceWidth35 (d + 3) = (d + 3) * ((d + 3) * sourceA35 (d + 3)) := by
  unfold sourceWidth35
  ring

end CoefficientTwoPrecision.Asym35

#print axioms CoefficientTwoPrecision.Asym35.logFactor_cube_le
#print axioms CoefficientTwoPrecision.Asym35.sourceWidth35_upper
#print axioms CoefficientTwoPrecision.Asym35.sourceWidth35_lower7
#print axioms CoefficientTwoPrecision.Asym35.sourceRho35_lower
#print axioms CoefficientTwoPrecision.Asym35.actual_leading_rows35
#print axioms CoefficientTwoPrecision.Asym35.prescribed_card35
