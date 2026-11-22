import Asym22.Width

/-!
# The new threshold and the size conditions

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The proof is his; this file only replaces the single size hypothesis
`4 * errorNumerator r W ≤ m` (with `errorNumerator = 10^12 r^20 W^4`) by
`threshold22 r ≤ m` with `threshold22 r = 1452 r^10 W^2` (the proximity deletion of
`IntervalKeys`, counted in local positions, is `181 r^10 W^2 / m`; the width `W = r q` is
that of `Asym22.Width`), and re-proves the elementary size and factor estimates that
depended on it. The statements are those of `ConstructionSize`, `SourceCountFactors` and
`CandidatePositivity`, with the new hypothesis.
-/

namespace CoefficientTwoPrecision.Asym22

open CoefficientTwoPrecision.Asym35

open CandidateFactorization ConstructionSize

/-- The new size threshold for one sparse block of source size `m`. -/
def threshold22 (r : Nat) : Nat := 1452 * r ^ 10 * sourceWidth22 r ^ 2

/-- The absolute constant of the clean threshold `n ≥ C r^21`:
`2 · 1452 · 10400^2 · 16`, from `W ≤ 10400 r^5 (log₂ r + 2)` and `(log₂ r + 2)^2 ≤ 16 r`. -/
def transferConstant22 : Nat := 46464 * 10400 ^ 2

/-- The finite threshold of the chain: `n ≥ 2904 · 10400^2 · r^20 · (log₂ r + 2)^2`.
It follows from `n ≥ transferConstant22 · r^21` (`logThreshold_le`) and gives the
logarithmic rate of `Asym22.LogRate`. -/
def logThreshold (r : Nat) : Nat := 2904 * 10400 ^ 2 * r ^ 20 * logFactor r ^ 2

theorem logFactor_sq_le (r : Nat) (hr : 1 ≤ r) : logFactor r ^ 2 ≤ 16 * r := by
  have h3 := logFactor_cube_le r hr
  have hL := logFactor_pos r
  have h22 : logFactor r ^ 2 ≤ logFactor r ^ 3 := pow_le_pow_right₀ (by omega) (by decide)
  omega

theorem logThreshold_le (r : Nat) (hr : 1 ≤ r) : logThreshold r ≤ transferConstant22 * r ^ 21 := by
  have h := Nat.mul_le_mul_left (2904 * 10400 ^ 2 * r ^ 20) (logFactor_sq_le r hr)
  unfold logThreshold transferConstant22
  calc
    2904 * 10400 ^ 2 * r ^ 20 * logFactor r ^ 2 ≤ 2904 * 10400 ^ 2 * r ^ 20 * (16 * r) := h
    _ = 46464 * 10400 ^ 2 * r ^ 21 := by ring

/-- The new deletion numerator: the guard-only deletion and the proximity deletion, both
counted in local positions. -/
def deletionNumerator22 (r W : ℚ) : ℚ := 20 * r ^ 4 * W ^ 2 + 181 * r ^ 10 * W ^ 2


theorem monomial_bound22 (r W c a b : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hc : c ≤ 1452) (ha : a ≤ 10) (hb : b ≤ 2) :
    c * r ^ a * W ^ b ≤ 1452 * r ^ 10 * W ^ 2 := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (pow_le_pow_right₀ hr ha))
    (pow_le_pow_right₀ hW hb)

theorem threshold_monomial (r c a b : Nat) (hr : 6 ≤ r)
    (hc : c ≤ 1452) (ha : a ≤ 10) (hb : b ≤ 2) :
    c * r ^ a * sourceWidth22 r ^ b ≤ threshold22 r :=
  monomial_bound22 r (sourceWidth22 r) c a b (by omega) (width_positive22 r hr) hc ha hb

/-- The statement of `ConstructionSize.threshold_conditions` from the new threshold. -/
theorem threshold_conditions22 (r m : Nat) (hr : 6 ≤ r)
    (hm : threshold22 r ≤ m) :
    0 < m ∧ guardCount22 r < m ∧ backgroundSize22 r m < 2 * m ∧
      38 * r ^ 4 ≤ backgroundSize22 r m ∧ 2 * sourceWidth22 r ^ 2 ≤ m ∧
      2 * r * guardCount22 r ≤ m ∧
      r * ((4 * r + 3) * (52 * r ^ 5 * sourceWidth22 r ^ 2)) < backgroundSize22 r m := by
  have hW := width_positive22 r hr
  have hrW := width_linear22 r hr
  have hW2 : sourceWidth22 r ^ 2 ≤ threshold22 r := by
    simpa using threshold_monomial r 1 0 2 hr (by norm_num) (by decide) (by decide)
  have hWsq : sourceWidth22 r ≤ sourceWidth22 r ^ 2 := by nlinarith
  have hG : guardCount22 r ≤ sourceWidth22 r := Nat.sub_le _ _
  have hW2' : 2 * sourceWidth22 r ^ 2 ≤ threshold22 r := by
    simpa using threshold_monomial r 2 0 2 hr (by norm_num) (by decide) (by decide)
  have h0 : 0 < m := by omega
  have hGm : guardCount22 r < m := by omega
  have hM2 : backgroundSize22 r m < 2 * m := by unfold backgroundSize22; omega
  have h38 : 38 * r ^ 4 ≤ threshold22 r := by
    simpa using threshold_monomial r 38 4 0 hr (by norm_num) (by decide) (by decide)
  have hM : m ≤ backgroundSize22 r m := by unfold backgroundSize22; omega
  have hrG : r * guardCount22 r ≤ sourceWidth22 r ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hrW hG
  have htworG : 2 * r * guardCount22 r ≤ m := by
    calc
      2 * r * guardCount22 r = 2 * (r * guardCount22 r) := by ring
      _ ≤ 2 * sourceWidth22 r ^ 2 := Nat.mul_le_mul_left 2 hrG
      _ ≤ m := by omega
  have hmon : r ^ 7 * sourceWidth22 r ^ 2 ≤ r ^ 10 * sourceWidth22 r ^ 2 :=
    Nat.mul_le_mul_right _ (pow_le_pow_right₀ (show 1 ≤ r by omega) (by decide : 7 ≤ 10))
  have hp : 0 < r ^ 10 * sourceWidth22 r ^ 2 := by positivity
  have hstrict : 260 * r ^ 7 * sourceWidth22 r ^ 2 < threshold22 r := by
    unfold threshold22
    nlinarith
  have hcover : r * ((4 * r + 3) * (52 * r ^ 5 * sourceWidth22 r ^ 2)) ≤
      260 * r ^ 7 * sourceWidth22 r ^ 2 := by
    calc
      r * ((4 * r + 3) * (52 * r ^ 5 * sourceWidth22 r ^ 2)) ≤
          r * ((5 * r) * (52 * r ^ 5 * sourceWidth22 r ^ 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 260 * r ^ 7 * sourceWidth22 r ^ 2 := by ring
  exact ⟨h0, hGm, hM2, by omega, by omega, htworG, by omega⟩

section Factors

variable (r m : Nat) (hr : 6 ≤ r) (hm : threshold22 r ≤ m)

include hr hm

theorem guard_error22 :
    |guardFactor22 r m - 1| ≤ (sourceWidth22 r : ℚ) ^ 2 / (2 * m) := by
  obtain ⟨hm0, hGm, _, _, _, _, _⟩ := threshold_conditions22 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have h := CountingRatios.falling_bounds m (guardCount22 r) hm0 (by omega)
  have hG : (guardCount22 r : ℚ) ≤ sourceWidth22 r := by
    exact_mod_cast (Nat.sub_le (sourceWidth22 r) r)
  have hG0 : (0 : ℚ) ≤ guardCount22 r := by positivity
  have hW0 : (0 : ℚ) ≤ sourceWidth22 r := by positivity
  have hsq := pow_le_pow_left₀ hG0 hG 2
  have he : (guardCount22 r : ℚ) * ((guardCount22 r : ℚ) - 1) / (2 * m) ≤
      (sourceWidth22 r : ℚ) ^ 2 / (2 * m) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  change |(m.descFactorial (guardCount22 r) : ℚ) / (m : ℚ) ^ guardCount22 r - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem floor_error22 :
    |floorFactor22 r m - 1| ≤ (sourceWidth22 r : ℚ) / m := by
  have hsize := threshold_conditions22 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hsize.1
  have hM : m ≤ backgroundSize22 r m := by unfold backgroundSize22; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize22 r m := by
    exact_mod_cast (show 1 ≤ backgroundSize22 r m by omega)
  have hpower : (m : ℚ) ≤ (backgroundSize22 r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize22 r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hW : (0 : ℚ) < sourceWidth22 r := by
    exact_mod_cast (show 0 < sourceWidth22 r from width_positive22 r hr)
  have h := ElementaryCountFactors.rounded_factor (sourceEta25 r)
    ((backgroundSize22 r m : ℚ) ^ (r - 3)) m (sourceWidth22 r)
    (sourceEta25_pos r hr) hmQ hW hpower (sourceEta_width22 r hr)
  change |(⌊sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3)) - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem background_ge_one22 (exponent : Nat) :
    1 ≤ backgroundFactor22 r m ^ exponent := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions22 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have hM : (m : ℚ) ≤ backgroundSize22 r m := by
    exact_mod_cast (show m ≤ backgroundSize22 r m by unfold backgroundSize22; omega)
  have h1 : 1 ≤ backgroundFactor22 r m := by
    unfold backgroundFactor22
    rw [le_div_iff₀ hmQ]
    linarith
  exact one_le_pow₀ h1

theorem insertion_error22 :
    |insertionFactor22 r m - 1| ≤ (sourceWidth22 r : ℚ) ^ 2 / m := by
  obtain ⟨hm0, _, _, _, hW, _, _⟩ := threshold_conditions22 r m hr hm
  have h := CountingRatios.rising_bounds m (sourceWidth22 r) hm0 (by omega)
  unfold insertionFactor22
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem insertion_pos22 : 0 < insertionFactor22 r m := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions22 r m hr hm
  unfold insertionFactor22
  have hD : (0 : ℚ) < (SourceUniverse.risingCount m (sourceWidth22 r) : ℚ) := by
    exact_mod_cast risingCount_pos m (sourceWidth22 r) hm0
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  positivity

theorem floor_argument22 :
    4 ≤ sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3) := by
  have hm0 := (threshold_conditions22 r m hr hm).1
  have hM : m ≤ backgroundSize22 r m := by unfold backgroundSize22; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize22 r m := by
    exact_mod_cast (show 1 ≤ backgroundSize22 r m by omega)
  have hX : (m : ℚ) ≤ (backgroundSize22 r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize22 r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hEW : 4 * sourceWidth22 r ≤ threshold22 r := by
    simpa using threshold_monomial r 4 0 1 hr (by norm_num) (by decide) (by decide)
  have h4W : (4 : ℚ) * sourceWidth22 r ≤ m := by
    exact_mod_cast (show 4 * sourceWidth22 r ≤ m by omega)
  have heta := sourceEta25_pos r hr
  have hscale := sourceEta_width22 r hr
  have hfirst := mul_le_mul_of_nonneg_left h4W heta.le
  have hsecond := mul_le_mul_of_nonneg_left hX heta.le
  nlinarith

theorem selected_floor_half22 :
    sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3) / 2 ≤
      (⌊sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) :=
  CandidatePositivity.floor_half _ (by have := floor_argument22 r m hr hm; linarith)

theorem candidate_positive22 : 0 < candidateCount22 r m := by
  have hsize := threshold_conditions22 r m hr hm
  have hguards : 0 < m.descFactorial (guardCount22 r) := Nat.descFactorial_pos.mpr (by omega)
  have hfloor : 0 < ⌊sourceEta25 r * (backgroundSize22 r m : ℚ) ^ (r - 3)⌋₊ :=
    Nat.floor_pos.mpr (by have := floor_argument22 r m hr hm; linarith)
  have hA := sourceA35_pos r hr
  have hq : 0 < sourceQ22 r := TD.tdQ_pos _ _
  unfold candidateCount22 sourceGridCount22
  positivity

end Factors

/-- Natural-number size facts used for the ratio and the density lower bound. -/
theorem small_errors22 (r m : Nat) (hr : 6 ≤ r) (hm : threshold22 r ≤ m) :
    100 * sourceWidth22 r ^ 2 ≤ m ∧
      8 * (20 * r ^ 4 * sourceWidth22 r ^ 2 + 181 * r ^ 10 * sourceWidth22 r ^ 2) ≤ m ∧
      100 * (2 * r + 1040 * r ^ 7 * sourceWidth22 r ^ 2) ≤ m ∧
      4 * r * (2 * r + 1040 * r ^ 7 * sourceWidth22 r ^ 2) ≤ m ∧
      4 * r * r ≤ m := by
  have hW := width_positive22 r hr
  have hr1 : 1 ≤ r := by omega
  have h1 : 100 * sourceWidth22 r ^ 2 ≤ threshold22 r := by
    simpa using threshold_monomial r 100 0 2 hr (by norm_num) (by decide) (by decide)
  have hmon : ∀ a b : Nat, a ≤ 10 → b ≤ 2 →
      r ^ a * sourceWidth22 r ^ b ≤ r ^ 10 * sourceWidth22 r ^ 2 :=
    fun a b ha hb => Nat.mul_le_mul (pow_le_pow_right₀ hr1 ha) (pow_le_pow_right₀ hW hb)
  have h10 := hmon 1 0 (by decide) (by decide)
  have h20 := hmon 2 0 (by decide) (by decide)
  simp only [pow_zero, pow_one, mul_one] at h10 h20
  have hT : threshold22 r = 1452 * (r ^ 10 * sourceWidth22 r ^ 2) := by unfold threshold22; ring
  have hr2 : 36 ≤ r ^ 2 := by
    calc 36 = 6 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
  have hr3 : 216 ≤ r ^ 3 := by
    calc 216 = 6 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have hr6 : 80 ≤ r ^ 6 := by
    calc 80 ≤ 6 ^ 6 := by norm_num
      _ ≤ r ^ 6 := Nat.pow_le_pow_left hr 6
  have h4 : 80 * (r ^ 4 * sourceWidth22 r ^ 2) ≤ r ^ 10 * sourceWidth22 r ^ 2 := by
    calc
      80 * (r ^ 4 * sourceWidth22 r ^ 2) ≤ r ^ 6 * (r ^ 4 * sourceWidth22 r ^ 2) :=
        Nat.mul_le_mul_right _ hr6
      _ = r ^ 10 * sourceWidth22 r ^ 2 := by ring
  have h5 : 216 * (r ^ 7 * sourceWidth22 r ^ 2) ≤ r ^ 10 * sourceWidth22 r ^ 2 := by
    calc
      216 * (r ^ 7 * sourceWidth22 r ^ 2) ≤ r ^ 3 * (r ^ 7 * sourceWidth22 r ^ 2) :=
        Nat.mul_le_mul_right _ hr3
      _ = r ^ 10 * sourceWidth22 r ^ 2 := by ring
  have h6 : 36 * (r ^ 8 * sourceWidth22 r ^ 2) ≤ r ^ 10 * sourceWidth22 r ^ 2 := by
    calc
      36 * (r ^ 8 * sourceWidth22 r ^ 2) ≤ r ^ 2 * (r ^ 8 * sourceWidth22 r ^ 2) :=
        Nat.mul_le_mul_right _ hr2
      _ = r ^ 10 * sourceWidth22 r ^ 2 := by ring
  refine ⟨h1.trans hm, ?_, ?_, ?_, ?_⟩
  · have e1 : 8 * (20 * r ^ 4 * sourceWidth22 r ^ 2 + 181 * r ^ 10 * sourceWidth22 r ^ 2) =
        160 * (r ^ 4 * sourceWidth22 r ^ 2) + 1448 * (r ^ 10 * sourceWidth22 r ^ 2) := by ring
    omega
  · have e1 : 100 * (2 * r + 1040 * r ^ 7 * sourceWidth22 r ^ 2) =
        200 * r + 104000 * (r ^ 7 * sourceWidth22 r ^ 2) := by ring
    omega
  · have e1 : 4 * r * (2 * r + 1040 * r ^ 7 * sourceWidth22 r ^ 2) =
        8 * r ^ 2 + 4160 * (r ^ 8 * sourceWidth22 r ^ 2) := by ring
    omega
  · have e1 : 4 * r * r = 4 * r ^ 2 := by ring
    omega

end CoefficientTwoPrecision.Asym22


#print axioms CoefficientTwoPrecision.Asym22.threshold_conditions22
#print axioms CoefficientTwoPrecision.Asym22.candidate_positive22
#print axioms CoefficientTwoPrecision.Asym22.small_errors22
