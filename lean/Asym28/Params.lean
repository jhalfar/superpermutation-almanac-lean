import Asym28.Width

/-!
# Exponent 28: the new threshold and the size conditions

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The proof is his; this file only replaces the single size hypothesis
`4 * errorNumerator r W ≤ m` (with `errorNumerator = 10^12 r^22 W^4`) by
`threshold28 r ≤ m` with `threshold28 r = 2960 r^10 W^3` (the proximity deletion of
`IntervalKeys` is `128 r^10 W^3 / m`; the width `W = r q` is that of `Asym28.Width`), and re-proves
the elementary size and factor estimates that depended on it. The
statements are those of `ConstructionSize`, `SourceCountFactors` and
`CandidatePositivity`, with the new hypothesis.
-/

namespace CoefficientTwoPrecision.Asym28

open CoefficientTwoPrecision.Asym35

open CandidateFactorization ConstructionSize

/-- The new size threshold for one sparse block of source size `m`. -/
def threshold28 (r : Nat) : Nat := 2960 * r ^ 10 * sourceWidth28 r ^ 3

/-- The absolute constant of the exponent-28 threshold `n ≥ C r^29`:
`2 · 2960 · 8320^3 · 16`, from `W ≤ 8320 r^6 (log₂ r + 2)` and `(log₂ r + 2)^3 ≤ 16 r`. -/
def transferConstant28 : Nat := 94720 * 8320 ^ 3

/-- The finite threshold of the exponent-28 chain: `n ≥ 5920 · 8320^3 · r^28 · (log₂ r + 2)^3`.
It follows from `n ≥ transferConstant28 · r^29` (`logThreshold_le`) and gives the
logarithmic rate of `Asym28.LogRate`. -/
def logThreshold (r : Nat) : Nat := 5920 * 8320 ^ 3 * r ^ 28 * logFactor r ^ 3

theorem logThreshold_le (r : Nat) (hr : 1 ≤ r) : logThreshold r ≤ transferConstant28 * r ^ 29 := by
  have h := Nat.mul_le_mul_left (5920 * 8320 ^ 3 * r ^ 28) (logFactor_cube_le r hr)
  unfold logThreshold transferConstant28
  calc
    5920 * 8320 ^ 3 * r ^ 28 * logFactor r ^ 3 ≤ 5920 * 8320 ^ 3 * r ^ 28 * (16 * r) := h
    _ = 94720 * 8320 ^ 3 * r ^ 29 := by ring

/-- The new deletion numerator: the unchanged guard-only deletion plus the
proximity deletion counted by (type pair, constant) keys. -/
def deletionNumerator28 (r W : ℚ) : ℚ := 18 * r ^ 3 * W ^ 3 + 128 * r ^ 10 * W ^ 3


theorem monomial_bound28 (r W c a b : Nat) (hr : 1 ≤ r) (hW : 1 ≤ W)
    (hc : c ≤ 2960) (ha : a ≤ 10) (hb : b ≤ 3) :
    c * r ^ a * W ^ b ≤ 2960 * r ^ 10 * W ^ 3 := by
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (pow_le_pow_right₀ hr ha))
    (pow_le_pow_right₀ hW hb)

theorem threshold_monomial (r c a b : Nat) (hr : 6 ≤ r)
    (hc : c ≤ 2960) (ha : a ≤ 10) (hb : b ≤ 3) :
    c * r ^ a * sourceWidth28 r ^ b ≤ threshold28 r :=
  monomial_bound28 r (sourceWidth28 r) c a b (by omega) (width_positive28 r hr) hc ha hb

/-- The statement of `ConstructionSize.threshold_conditions` from the new threshold. -/
theorem threshold_conditions28 (r m : Nat) (hr : 6 ≤ r)
    (hm : threshold28 r ≤ m) :
    0 < m ∧ guardCount28 r < m ∧ backgroundSize28 r m < 2 * m ∧
      38 * r ^ 4 ≤ backgroundSize28 r m ∧ sourceWidth28 r ^ 2 ≤ m ∧
      2 * r * guardCount28 r ≤ m ∧
      (4 * r + 3) * (52 * r ^ 5 * sourceWidth28 r ^ 2) < backgroundSize28 r m := by
  have hW := width_positive28 r hr
  have hrW := width_linear28 r hr
  have hW2 : sourceWidth28 r ^ 2 ≤ threshold28 r := by
    simpa using threshold_monomial r 1 0 2 hr (by norm_num) (by decide) (by decide)
  have hWsq : sourceWidth28 r ≤ sourceWidth28 r ^ 2 := by nlinarith
  have hG : guardCount28 r ≤ sourceWidth28 r := Nat.sub_le _ _
  have hW2' : 2 * sourceWidth28 r ^ 2 ≤ threshold28 r := by
    simpa using threshold_monomial r 2 0 2 hr (by norm_num) (by decide) (by decide)
  have h0 : 0 < m := by omega
  have hGm : guardCount28 r < m := by omega
  have hM2 : backgroundSize28 r m < 2 * m := by unfold backgroundSize28; omega
  have h38 : 38 * r ^ 4 ≤ threshold28 r := by
    simpa using threshold_monomial r 38 4 0 hr (by norm_num) (by decide) (by decide)
  have hM : m ≤ backgroundSize28 r m := by unfold backgroundSize28; omega
  have hrG : r * guardCount28 r ≤ sourceWidth28 r ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hrW hG
  have htworG : 2 * r * guardCount28 r ≤ m := by
    calc
      2 * r * guardCount28 r = 2 * (r * guardCount28 r) := by ring
      _ ≤ 2 * sourceWidth28 r ^ 2 := Nat.mul_le_mul_left 2 hrG
      _ ≤ m := by omega
  have hmon : r ^ 6 * sourceWidth28 r ^ 2 ≤ r ^ 10 * sourceWidth28 r ^ 3 :=
    Nat.mul_le_mul (pow_le_pow_right₀ (show 1 ≤ r by omega) (by decide : 6 ≤ 10))
      (pow_le_pow_right₀ hW (by decide : 2 ≤ 3))
  have hp : 0 < r ^ 10 * sourceWidth28 r ^ 3 := by positivity
  have hstrict : 260 * r ^ 6 * sourceWidth28 r ^ 2 < threshold28 r := by
    unfold threshold28
    nlinarith
  have hcover : (4 * r + 3) * (52 * r ^ 5 * sourceWidth28 r ^ 2) ≤
      260 * r ^ 6 * sourceWidth28 r ^ 2 := by
    calc
      (4 * r + 3) * (52 * r ^ 5 * sourceWidth28 r ^ 2) ≤
          (5 * r) * (52 * r ^ 5 * sourceWidth28 r ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 260 * r ^ 6 * sourceWidth28 r ^ 2 := by ring
  exact ⟨h0, hGm, hM2, by omega, by omega, htworG, by omega⟩

section Factors

variable (r m : Nat) (hr : 6 ≤ r) (hm : threshold28 r ≤ m)

include hr hm

theorem guard_error28 :
    |guardFactor28 r m - 1| ≤ (sourceWidth28 r : ℚ) ^ 2 / (2 * m) := by
  obtain ⟨hm0, hGm, _, _, _, _, _⟩ := threshold_conditions28 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have h := CountingRatios.falling_bounds m (guardCount28 r) hm0 (by omega)
  have hG : (guardCount28 r : ℚ) ≤ sourceWidth28 r := by
    exact_mod_cast (Nat.sub_le (sourceWidth28 r) r)
  have hG0 : (0 : ℚ) ≤ guardCount28 r := by positivity
  have hW0 : (0 : ℚ) ≤ sourceWidth28 r := by positivity
  have hsq := pow_le_pow_left₀ hG0 hG 2
  have he : (guardCount28 r : ℚ) * ((guardCount28 r : ℚ) - 1) / (2 * m) ≤
      (sourceWidth28 r : ℚ) ^ 2 / (2 * m) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  change |(m.descFactorial (guardCount28 r) : ℚ) / (m : ℚ) ^ guardCount28 r - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem floor_error28 :
    |floorFactor28 r m - 1| ≤ (sourceWidth28 r : ℚ) / m := by
  have hsize := threshold_conditions28 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hsize.1
  have hM : m ≤ backgroundSize28 r m := by unfold backgroundSize28; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize28 r m := by
    exact_mod_cast (show 1 ≤ backgroundSize28 r m by omega)
  have hpower : (m : ℚ) ≤ (backgroundSize28 r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize28 r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hW : (0 : ℚ) < sourceWidth28 r := by
    exact_mod_cast (show 0 < sourceWidth28 r from width_positive28 r hr)
  have h := ElementaryCountFactors.rounded_factor (sourceEta r)
    ((backgroundSize28 r m : ℚ) ^ (r - 3)) m (sourceWidth28 r)
    (eta_pos r hr) hmQ hW hpower (sourceEta_width28 r hr)
  change |(⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)) - 1| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem background_ge_one28 (exponent : Nat) :
    1 ≤ backgroundFactor28 r m ^ exponent := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions28 r m hr hm
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have hM : (m : ℚ) ≤ backgroundSize28 r m := by
    exact_mod_cast (show m ≤ backgroundSize28 r m by unfold backgroundSize28; omega)
  have h1 : 1 ≤ backgroundFactor28 r m := by
    unfold backgroundFactor28
    rw [le_div_iff₀ hmQ]
    linarith
  exact one_le_pow₀ h1

theorem insertion_error28 :
    |insertionFactor28 r m - 1| ≤ (sourceWidth28 r : ℚ) ^ 2 / m := by
  obtain ⟨hm0, _, _, _, hW, _, _⟩ := threshold_conditions28 r m hr hm
  have h := CountingRatios.rising_bounds m (sourceWidth28 r) hm0 hW
  unfold insertionFactor28
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

theorem insertion_pos28 : 0 < insertionFactor28 r m := by
  obtain ⟨hm0, _, _, _, _, _, _⟩ := threshold_conditions28 r m hr hm
  unfold insertionFactor28
  have hD : (0 : ℚ) < (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) := by
    exact_mod_cast risingCount_pos m (sourceWidth28 r) hm0
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  positivity

theorem floor_argument28 :
    4 ≤ sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3) := by
  have hm0 := (threshold_conditions28 r m hr hm).1
  have hM : m ≤ backgroundSize28 r m := by unfold backgroundSize28; omega
  have hM1 : (1 : ℚ) ≤ backgroundSize28 r m := by
    exact_mod_cast (show 1 ≤ backgroundSize28 r m by omega)
  have hX : (m : ℚ) ≤ (backgroundSize28 r m : ℚ) ^ (r - 3) :=
    (show (m : ℚ) ≤ backgroundSize28 r m by exact_mod_cast hM).trans
      (le_self_pow₀ hM1 (by omega))
  have hEW : 4 * sourceWidth28 r ≤ threshold28 r := by
    simpa using threshold_monomial r 4 0 1 hr (by norm_num) (by decide) (by decide)
  have h4W : (4 : ℚ) * sourceWidth28 r ≤ m := by
    exact_mod_cast (show 4 * sourceWidth28 r ≤ m by omega)
  have heta := eta_pos r hr
  have hscale := sourceEta_width28 r hr
  have hfirst := mul_le_mul_of_nonneg_left h4W heta.le
  have hsecond := mul_le_mul_of_nonneg_left hX heta.le
  nlinarith

theorem selected_floor_half28 :
    sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3) / 2 ≤
      (⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) :=
  CandidatePositivity.floor_half _ (by have := floor_argument28 r m hr hm; linarith)

theorem candidate_positive28 : 0 < candidateCount28 r m := by
  have hsize := threshold_conditions28 r m hr hm
  have hguards : 0 < m.descFactorial (guardCount28 r) := Nat.descFactorial_pos.mpr (by omega)
  have hfloor : 0 < ⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ :=
    Nat.floor_pos.mpr (by have := floor_argument28 r m hr hm; linarith)
  have hA := sourceA35_pos r hr
  have hq : 0 < sourceQ28 r := TD.tdQ_pos _ _
  unfold candidateCount28 sourceGridCount28
  positivity

end Factors

/-- Natural-number size facts used for the ratio and the density lower bound. -/
theorem small_errors28 (r m : Nat) (hr : 6 ≤ r) (hm : threshold28 r ≤ m) :
    100 * sourceWidth28 r ^ 2 ≤ m ∧
      8 * (18 * r ^ 3 * sourceWidth28 r ^ 3 + 128 * r ^ 10 * sourceWidth28 r ^ 3) ≤ m ∧
      100 * (2 * r + 1040 * r ^ 7 * sourceWidth28 r ^ 2) ≤ m ∧
      4 * r * (2 * r + 1040 * r ^ 7 * sourceWidth28 r ^ 2) ≤ m ∧
      4 * r * r ≤ m := by
  have hW := width_positive28 r hr
  have hrW := width_linear28 r hr
  have hr1 : 1 ≤ r := by omega
  have h1 : 100 * sourceWidth28 r ^ 2 ≤ threshold28 r := by
    simpa using threshold_monomial r 100 0 2 hr (by norm_num) (by decide) (by decide)
  have hmon : ∀ a b : Nat, a ≤ 10 → b ≤ 3 → r ^ a * sourceWidth28 r ^ b ≤ r ^ 10 * sourceWidth28 r ^ 3 :=
    fun a b ha hb => Nat.mul_le_mul (pow_le_pow_right₀ hr1 ha) (pow_le_pow_right₀ hW hb)
  have h23 := hmon 3 3 (by decide) (by decide)
  have h52 := hmon 7 2 (by decide) (by decide)
  have h62 := hmon 8 2 (by decide) (by decide)
  have h10 := hmon 1 0 (by decide) (by decide)
  have h20 := hmon 2 0 (by decide) (by decide)
  simp only [pow_zero, pow_one, mul_one] at h10 h20
  have hT : threshold28 r = 2960 * (r ^ 10 * sourceWidth28 r ^ 3) := by unfold threshold28; ring
  have hsq : r * r = r ^ 2 := by ring
  have hr4 : 36 ≤ r ^ 2 := by
    calc 36 = 6 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
  have hr5 : 216 ≤ r ^ 3 := by
    calc 216 = 6 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have hr6 : 1296 ≤ r ^ 4 := by
    calc 1296 = 6 ^ 4 := by norm_num
      _ ≤ r ^ 4 := Nat.pow_le_pow_left hr 4
  have hWW : sourceWidth28 r ^ 2 ≤ sourceWidth28 r ^ 3 := pow_le_pow_right₀ hW (by decide)
  have h5 : 216 * (r ^ 7 * sourceWidth28 r ^ 2) ≤ r ^ 10 * sourceWidth28 r ^ 3 := by
    calc
      216 * (r ^ 7 * sourceWidth28 r ^ 2) ≤ r ^ 3 * (r ^ 7 * sourceWidth28 r ^ 3) :=
        Nat.mul_le_mul hr5 (Nat.mul_le_mul_left _ hWW)
      _ = r ^ 10 * sourceWidth28 r ^ 3 := by ring
  have h6 : 36 * (r ^ 8 * sourceWidth28 r ^ 2) ≤ r ^ 10 * sourceWidth28 r ^ 3 := by
    calc
      36 * (r ^ 8 * sourceWidth28 r ^ 2) ≤ r ^ 2 * (r ^ 8 * sourceWidth28 r ^ 3) :=
        Nat.mul_le_mul hr4 (Nat.mul_le_mul_left _ hWW)
      _ = r ^ 10 * sourceWidth28 r ^ 3 := by ring
  refine ⟨h1.trans hm, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have e1 : 100 * (2 * r + 1040 * r ^ 7 * sourceWidth28 r ^ 2) =
        200 * r + 104000 * (r ^ 7 * sourceWidth28 r ^ 2) := by ring
    omega
  · have e1 : 4 * r * (2 * r + 1040 * r ^ 7 * sourceWidth28 r ^ 2) =
        8 * r ^ 2 + 4160 * (r ^ 8 * sourceWidth28 r ^ 2) := by ring
    omega
  · nlinarith

end CoefficientTwoPrecision.Asym28


#print axioms CoefficientTwoPrecision.Asym28.threshold_conditions28
#print axioms CoefficientTwoPrecision.Asym28.candidate_positive28
#print axioms CoefficientTwoPrecision.Asym28.small_errors28
