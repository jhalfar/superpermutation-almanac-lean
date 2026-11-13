import Quantitative.CandidatePositivity

/-!
# Exponent 37: the new threshold and the size conditions

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The proof is his; this file only replaces the single size hypothesis
`4 * errorNumerator r W ≤ m` (with `errorNumerator = 10^12 r^22 W^4`) by
`threshold37 r ≤ m` with `threshold37 r = 2960 r^10 W^3`, and re-proves
the elementary size and factor estimates that depended on it. The
statements are those of `ConstructionSize`, `SourceCountFactors` and
`CandidatePositivity`, with the new hypothesis.
-/

namespace CoefficientTwoPrecision.Asym37

open CandidateFactorization ConstructionSize

/-- The new size threshold for one sparse block of source size `m`. -/
def threshold37 (r : Nat) : Nat := 2960 * r ^ 10 * sourceWidth r ^ 3

/-- The absolute constant of the exponent-37 threshold `n ≥ C r^37`. -/
def transferConstant37 : Nat := 5920 * 352 ^ 3

/-- The new deletion numerator: the unchanged guard-only deletion plus the
proximity deletion counted by (type pair, constant) keys. -/
def deletionNumerator37 (r W : ℚ) : ℚ := 18 * r ^ 2 * W ^ 3 + 128 * r ^ 10 * W ^ 3

theorem betaPolynomial_upper (x : ℚ) (hx : 6 ≤ x) :
    betaPolynomial x ≤ 1 / (128 * x ^ 4) := by
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
  have hN0 : 0 ≤ x * (x - 1) * (x - 2) ^ 2 := by positivity
  unfold betaPolynomial
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hx0 4, pow_pos hx0 8]

theorem sourceA_lower (r : Nat) (hr : 6 ≤ r) : 128 * r ^ 7 ≤ sourceA r := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith
  have hbeta := (sourceBeta_bounds r hr).1
  have hupper : sourceBeta r ≤ 1 / (128 * (r : ℚ) ^ 4) := by
    rw [sourceBeta_closed_form r (by omega)]
    exact betaPolynomial_upper (r : ℚ) hrQ
  have hquot : 128 * (r : ℚ) ^ 7 ≤ (r : ℚ) ^ 3 / sourceBeta r := by
    rw [le_div_iff₀ hbeta]
    calc
      128 * (r : ℚ) ^ 7 * sourceBeta r ≤ 128 * (r : ℚ) ^ 7 * (1 / (128 * (r : ℚ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = (r : ℚ) ^ 3 := by field_simp
  have hceil : (r : ℚ) ^ 3 / sourceBeta r ≤ (sourceA r : ℚ) := Nat.le_ceil _
  have h := hquot.trans hceil
  exact_mod_cast h

theorem sourceWidth_lower37 (r : Nat) (hr : 6 ≤ r) : 128 * r ^ 9 ≤ sourceWidth r := by
  have h := Nat.mul_le_mul_left (r ^ 2) (sourceA_lower r hr)
  calc
    128 * r ^ 9 = r ^ 2 * (128 * r ^ 7) := by ring
    _ ≤ r ^ 2 * sourceA r := h
    _ = sourceWidth r := rfl

theorem monomial_bound37 (r W c a b : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hc : c ≤ 2960) (ha : a ≤ 10) (hb : b ≤ 3) :
    c * r ^ a * W ^ b ≤ 2960 * r ^ 10 * W ^ 3 := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (pow_le_pow_right₀ hr ha))
    (pow_le_pow_right₀ hW hb)

theorem threshold_monomial (r c a b : Nat) (hr : 6 ≤ r)
    (hc : c ≤ 2960) (ha : a ≤ 10) (hb : b ≤ 3) :
    c * r ^ a * sourceWidth r ^ b ≤ threshold37 r :=
  monomial_bound37 r (sourceWidth r) c a b (by omega) (width_positive r hr) hc ha hb

/-- The statement of `ConstructionSize.threshold_conditions` from the new threshold. -/
theorem threshold_conditions37 (r m : Nat) (hr : 6 ≤ r)
    (hm : threshold37 r ≤ m) :
    0 < m ∧ guardCount r < m ∧ backgroundSize r m < 2 * m ∧
      38 * r ^ 4 ≤ backgroundSize r m ∧ sourceWidth r ^ 2 ≤ m ∧
      2 * r * guardCount r ≤ m ∧
      (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) < backgroundSize r m := by
  have hW := width_positive r hr
  have hrW := width_linear r hr
  have hW2 : sourceWidth r ^ 2 ≤ threshold37 r := by
    simpa using threshold_monomial r 1 0 2 hr (by norm_num) (by decide) (by decide)
  have hWsq : sourceWidth r ≤ sourceWidth r ^ 2 := by nlinarith
  have hG : guardCount r ≤ sourceWidth r := Nat.sub_le _ _
  have hW2' : 2 * sourceWidth r ^ 2 ≤ threshold37 r := by
    simpa using threshold_monomial r 2 0 2 hr (by norm_num) (by decide) (by decide)
  have h0 : 0 < m := by omega
  have hGm : guardCount r < m := by omega
  have hM2 : backgroundSize r m < 2 * m := by unfold backgroundSize; omega
  have h38 : 38 * r ^ 4 ≤ threshold37 r := by
    simpa using threshold_monomial r 38 4 0 hr (by norm_num) (by decide) (by decide)
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hrG : r * guardCount r ≤ sourceWidth r ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hrW hG
  have htworG : 2 * r * guardCount r ≤ m := by
    calc
      2 * r * guardCount r = 2 * (r * guardCount r) := by ring
      _ ≤ 2 * sourceWidth r ^ 2 := Nat.mul_le_mul_left 2 hrG
      _ ≤ m := by omega
  have hmon : r ^ 5 * sourceWidth r ^ 2 ≤ r ^ 10 * sourceWidth r ^ 3 :=
    Nat.mul_le_mul (pow_le_pow_right₀ (show 1 ≤ r by omega) (by decide : 5 ≤ 10))
      (pow_le_pow_right₀ hW (by decide : 2 ≤ 3))
  have hp : 0 < r ^ 10 * sourceWidth r ^ 3 := by positivity
  have hstrict : 260 * r ^ 5 * sourceWidth r ^ 2 < threshold37 r := by
    unfold threshold37
    nlinarith
  have hcover : (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) ≤
      260 * r ^ 5 * sourceWidth r ^ 2 := by
    calc
      (4 * r + 3) * (52 * r ^ 4 * sourceWidth r ^ 2) ≤
          (5 * r) * (52 * r ^ 4 * sourceWidth r ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 260 * r ^ 5 * sourceWidth r ^ 2 := by ring
  exact ⟨h0, hGm, hM2, by omega, by omega, htworG, by omega⟩

section Factors

variable (r m : Nat) (hr : 6 ≤ r) (hm : threshold37 r ≤ m)

include hr hm

theorem guard_error37 :
    |guardFactor r m - 1| ≤ (sourceWidth r : ℚ) ^ 2 / (2 * m) := by
  obtain ⟨hm0, hGm, _, _, _, _, _⟩ := threshold_conditions37 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have h := CountingRatios.falling_bounds m (guardCount r) hm0 (by omega)
  have hG : (guardCount r : ℚ) ≤ sourceWidth r := by
    exact_mod_cast (Nat.sub_le (sourceWidth r) r)
  have hG0 : (0 : ℚ) ≤ guardCount r := by positivity
  have hW0 : (0 : ℚ) ≤ sourceWidth r := by positivity
  have hsq := pow_le_pow_left₀ hG0 hG 2
  have he : (guardCount r : ℚ) * ((guardCount r : ℚ) - 1) / (2 * m) ≤
      (sourceWidth r : ℚ) ^ 2 / (2 * m) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  change |(m.descFactorial (guardCount r) : ℚ) / (m : ℚ) ^ guardCount r - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem floor_error37 :
    |floorFactor r m - 1| ≤ (sourceWidth r : ℚ) / m := by
  have hsize := threshold_conditions37 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hsize.1
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize r m := by
    exact_mod_cast (show 1 ≤ backgroundSize r m by omega)
  have hpower : (m : ℚ) ≤ (backgroundSize r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hW : (0 : ℚ) < sourceWidth r := by
    exact_mod_cast (show 0 < sourceWidth r from width_positive r hr)
  have h := ElementaryCountFactors.rounded_factor (sourceEta r)
    ((backgroundSize r m : ℚ) ^ (r - 3)) m (sourceWidth r)
    (eta_pos r hr) hmQ hW hpower (ElementaryCountFactors.sourceEta_width r hr)
  change |(⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)) - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem background_ge_one37 (exponent : Nat) :
    1 ≤ backgroundFactor r m ^ exponent := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions37 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have hM : (m : ℚ) ≤ backgroundSize r m := by
    exact_mod_cast (show m ≤ backgroundSize r m by unfold backgroundSize; omega)
  have h1 : 1 ≤ backgroundFactor r m := by
    unfold backgroundFactor
    rw [le_div_iff₀ hmQ]
    linarith
  exact one_le_pow₀ h1

theorem insertion_error37 :
    |insertionFactor r m - 1| ≤ (sourceWidth r : ℚ) ^ 2 / m := by
  obtain ⟨hm0, _, _, _, hW, _, _⟩ := threshold_conditions37 r m hr hm
  have h := CountingRatios.rising_bounds m (sourceWidth r) hm0 hW
  unfold insertionFactor
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem insertion_pos37 : 0 < insertionFactor r m := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions37 r m hr hm
  unfold insertionFactor
  have hD : (0 : ℚ) < (SourceUniverse.risingCount m (sourceWidth r) : ℚ) := by
    exact_mod_cast risingCount_pos m (sourceWidth r) hm0
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  positivity

theorem floor_argument37 :
    4 ≤ sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3) := by
  have hm0 := (threshold_conditions37 r m hr hm).1
  have hM : m ≤ backgroundSize r m := by unfold backgroundSize; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize r m := by
    exact_mod_cast (show 1 ≤ backgroundSize r m by omega)
  have hX : (m : ℚ) ≤ (backgroundSize r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hEW : 4 * sourceWidth r ≤ threshold37 r := by
    simpa using threshold_monomial r 4 0 1 hr (by norm_num) (by decide) (by decide)
  have h4W : (4 : ℚ) * sourceWidth r ≤ m := by
    exact_mod_cast (show 4 * sourceWidth r ≤ m by omega)
  have heta := eta_pos r hr
  have hscale := ElementaryCountFactors.sourceEta_width r hr
  have hfirst := mul_le_mul_of_nonneg_left h4W heta.le
  have hsecond := mul_le_mul_of_nonneg_left hX heta.le
  nlinarith

theorem selected_floor_half37 :
    sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3) / 2 ≤
      (⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ : ℚ) :=
  CandidatePositivity.floor_half _ (by have := floor_argument37 r m hr hm; linarith)

theorem candidate_positive37 : 0 < candidateCount r m := by
  have hsize := threshold_conditions37 r m hr hm
  have hguards : 0 < m.descFactorial (guardCount r) := Nat.descFactorial_pos.mpr (by omega)
  have hfloor : 0 < ⌊sourceEta r * (backgroundSize r m : ℚ) ^ (r - 3)⌋₊ :=
    Nat.floor_pos.mpr (by have := floor_argument37 r m hr hm; linarith)
  have hA := sourceA_pos r hr
  have hr0 : 0 < r := by omega
  unfold candidateCount sourceGridCount
  positivity

end Factors

/-- Natural-number size facts used for the ratio and the density lower bound. -/
theorem small_errors37 (r m : Nat) (hr : 6 ≤ r) (hm : threshold37 r ≤ m) :
    100 * sourceWidth r ^ 2 ≤ m ∧
      8 * (18 * r ^ 2 * sourceWidth r ^ 3 + 128 * r ^ 10 * sourceWidth r ^ 3) ≤ m ∧
      100 * (2 * r + 1040 * r ^ 5 * sourceWidth r ^ 2) ≤ m ∧
      4 * r * (2 * r + 1040 * r ^ 5 * sourceWidth r ^ 2) ≤ m ∧
      4 * r * r ≤ m := by
  have hW := width_positive r hr
  have hrW := width_linear r hr
  have hr1 : 1 ≤ r := by omega
  have h1 : 100 * sourceWidth r ^ 2 ≤ threshold37 r := by
    simpa using threshold_monomial r 100 0 2 hr (by norm_num) (by decide) (by decide)
  have hmon : ∀ a b : Nat, a ≤ 10 → b ≤ 3 → r ^ a * sourceWidth r ^ b ≤ r ^ 10 * sourceWidth r ^ 3 :=
    fun a b ha hb => Nat.mul_le_mul (pow_le_pow_right₀ hr1 ha) (pow_le_pow_right₀ hW hb)
  have h23 := hmon 2 3 (by decide) (by decide)
  have h52 := hmon 5 2 (by decide) (by decide)
  have h62 := hmon 6 2 (by decide) (by decide)
  have h10 := hmon 1 0 (by decide) (by decide)
  have h20 := hmon 2 0 (by decide) (by decide)
  simp only [pow_zero, pow_one, mul_one] at h10 h20
  have hT : threshold37 r = 2960 * (r ^ 10 * sourceWidth r ^ 3) := by unfold threshold37; ring
  have hsq : r * r = r ^ 2 := by ring
  have hr4 : 1296 ≤ r ^ 4 := by
    calc 1296 = 6 ^ 4 := by norm_num
      _ ≤ r ^ 4 := Nat.pow_le_pow_left hr 4
  have hr5 : 7776 ≤ r ^ 5 := by
    calc 7776 = 6 ^ 5 := by norm_num
      _ ≤ r ^ 5 := Nat.pow_le_pow_left hr 5
  have hWW : sourceWidth r ^ 2 ≤ sourceWidth r ^ 3 := pow_le_pow_right₀ hW (by decide)
  have h5 : 7776 * (r ^ 5 * sourceWidth r ^ 2) ≤ r ^ 10 * sourceWidth r ^ 3 := by
    calc
      7776 * (r ^ 5 * sourceWidth r ^ 2) ≤ r ^ 5 * (r ^ 5 * sourceWidth r ^ 3) :=
        Nat.mul_le_mul hr5 (Nat.mul_le_mul_left _ hWW)
      _ = r ^ 10 * sourceWidth r ^ 3 := by ring
  have h6 : 1296 * (r ^ 6 * sourceWidth r ^ 2) ≤ r ^ 10 * sourceWidth r ^ 3 := by
    calc
      1296 * (r ^ 6 * sourceWidth r ^ 2) ≤ r ^ 4 * (r ^ 6 * sourceWidth r ^ 3) :=
        Nat.mul_le_mul hr4 (Nat.mul_le_mul_left _ hWW)
      _ = r ^ 10 * sourceWidth r ^ 3 := by ring
  refine ⟨h1.trans hm, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have e1 : 100 * (2 * r + 1040 * r ^ 5 * sourceWidth r ^ 2) =
        200 * r + 104000 * (r ^ 5 * sourceWidth r ^ 2) := by ring
    omega
  · have e1 : 4 * r * (2 * r + 1040 * r ^ 5 * sourceWidth r ^ 2) =
        8 * r ^ 2 + 4160 * (r ^ 6 * sourceWidth r ^ 2) := by ring
    omega
  · nlinarith

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.sourceA_lower
#print axioms CoefficientTwoPrecision.Asym37.threshold_conditions37
#print axioms CoefficientTwoPrecision.Asym37.candidate_positive37
#print axioms CoefficientTwoPrecision.Asym37.small_errors37
