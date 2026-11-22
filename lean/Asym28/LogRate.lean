import Asym28.Main
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponent 1/28 up to a logarithm

Addition to Jay Pantone's quantitative development (release 9ccbe66).
The finite theorem of `Asym28` holds for `n ≥ logThreshold r =
5920 · 8320^3 · r^28 · (log₂ r + 2)^3` (`finite_covering_word_log`). The
clean power `n^(-1/29)` of `Main` spends one factor `r` on `(log₂ r + 2)^3`.
Here the parameter is chosen from `logThreshold` itself, as in Jay's
`CompletionEstimates.largestSixParameter`, which gives

  `|S(n) - F3(n) - 2(n-4)!| ≤ 205 (n-4)! (log n)^(3/28) n^(-1/28)`

for `n ≥ logThreshold 6` (about `1.34 · 10^39`). The lower side is the same
as in Jay's `RealRate` (our Theorem B, `ConstAsym.lower2_ratio`).
-/

namespace CoefficientTwoPrecision.Asym28

open CoefficientTwoPrecision.Asym35

open Filter Asymptotics

/-- The finite bound for an actual covering word, threshold `logThreshold r`. -/
theorem finite_covering_word_log (n r : Nat) (hr : 6 ≤ r) (hn : logThreshold r ≤ n) :
    ∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      r * w.length ≤ r * SuperpermutationUpperBound.F3 n +
        (2 * r + 26) * (n - 4).factorial :=
  finite_word28 n r hr hn (supplier28 r hr)

theorem logThreshold_mono {r s : ℕ} (h : r ≤ s) : logThreshold r ≤ logThreshold s := by
  unfold logThreshold logFactor
  have h1 := Nat.pow_le_pow_left h 28
  have h2 : Nat.log 2 r ≤ Nat.log 2 s := Nat.log_mono_right h
  have h3 := Nat.pow_le_pow_left (show Nat.log 2 r + 2 ≤ Nat.log 2 s + 2 by omega) 3
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h3

theorem self_le_logThreshold (r : ℕ) : r ≤ logThreshold r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Nat.zero_le _
  have hL : 1 ≤ logFactor r ^ 3 :=
    Nat.one_le_pow _ _ (by have := logFactor_pos r; omega)
  unfold logThreshold
  calc
    r ≤ r ^ 28 := Nat.le_self_pow (by norm_num) r
    _ ≤ 5920 * 8320 ^ 3 * r ^ 28 := Nat.le_mul_of_pos_left _ (by norm_num)
    _ ≤ 5920 * 8320 ^ 3 * r ^ 28 * logFactor r ^ 3 := Nat.le_mul_of_pos_right _ hL

/-- The largest multiple of six whose threshold is at most `n`. -/
def logParameter (n : ℕ) : ℕ := 6 * Nat.findGreatest (fun k => logThreshold (6 * k) ≤ n) n

theorem logParameter_bounds (n : ℕ) (hn : logThreshold 6 ≤ n) :
    6 ≤ logParameter n ∧ 6 ∣ logParameter n ∧ logThreshold (logParameter n) ≤ n ∧
      n < logThreshold (2 * logParameter n) ∧ logParameter n ≤ n := by
  let P : ℕ → Prop := fun k => logThreshold (6 * k) ≤ n
  let k := Nat.findGreatest P n
  have hindex : ∀ j, P j → j ≤ n := fun j hj =>
    (show j ≤ 6 * j by omega).trans ((self_le_logThreshold _).trans hj)
  have hOne : P 1 := by simpa only [P, Nat.mul_one] using hn
  have hn1 : 1 ≤ n := hindex 1 hOne
  have hk1 : 1 ≤ k := Nat.le_findGreatest hn1 hOne
  have hk : P k := Nat.findGreatest_spec hn1 hOne
  have hnext : ¬ P (k + 1) := by
    intro hnext
    have hb : k + 1 ≤ n := hindex (k + 1) hnext
    exact (Nat.findGreatest_is_greatest (P := P) (n := n)
      (show Nat.findGreatest P n < k + 1 by dsimp [k]; omega) hb) hnext
  have hupper : n < logThreshold (6 * (k + 1)) := Nat.lt_of_not_ge hnext
  have hdef : logParameter n = 6 * k := rfl
  rw [hdef]
  refine ⟨by omega, ⟨k, rfl⟩, hk, hupper.trans_le (logThreshold_mono (by omega)),
    (self_le_logThreshold _).trans hk⟩

/-- `log₂ (2r) + 2 ≤ 2 log n` when `r ≤ n` and `n ≥ 256`. -/
theorem logFactor_double_le (n r : ℕ) (hrn : r ≤ n) (hn : 256 ≤ n) :
    (logFactor (2 * r) : ℝ) ≤ 2 * Real.log n := by
  have hk8 : 8 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlog2 : Nat.log 2 (2 * r) ≤ Nat.log 2 n + 1 := by
    have h := Nat.log_mono_right (b := 2) (show 2 * r ≤ n * 2 by omega)
    rwa [Nat.log_mul_base (by norm_num) (by omega)] at h
  have hnat : logFactor (2 * r) ≤ Nat.log 2 n + 3 := by unfold logFactor; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hl2 := Real.log_two_gt_d9
  have hk8R : (8 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hk8
  have hcast : (logFactor (2 * r) : ℝ) ≤ (Nat.log 2 n : ℝ) + 3 := by exact_mod_cast hnat
  nlinarith

theorem log_ge_one (n : ℕ) (hn : 256 ≤ n) : 1 ≤ Real.log n := by
  have h := logFactor_double_le n 0 (by omega) hn
  have h2 : (2 : ℝ) ≤ logFactor (2 * 0) := by exact_mod_cast logFactor_pos (2 * 0)
  linarith

theorem logThreshold_six_ge (n : ℕ) (hn : logThreshold 6 ≤ n) : 256 ≤ n := by
  have hL : 1 ≤ logFactor 6 ^ 3 := Nat.one_le_pow _ _ (by have := logFactor_pos 6; omega)
  have h : 256 ≤ logThreshold 6 := by
    unfold logThreshold
    calc
      256 ≤ 5920 * 8320 ^ 3 * 6 ^ 28 := by norm_num
      _ ≤ 5920 * 8320 ^ 3 * 6 ^ 28 * logFactor 6 ^ 3 := Nat.le_mul_of_pos_right _ hL
  omega

/-- The absolute constant `8 · 5920 · 8320^3` of the logarithmic rate. -/
def logConstant : ℕ := 8 * (5920 * 8320 ^ 3)

theorem logParameter_inverse_bound (n : ℕ) (hn : logThreshold 6 ≤ n) :
    (26 : ℝ) / (logParameter n : ℝ) ≤
      52 * (logConstant : ℝ) ^ (1 / 28 : ℝ) * Real.log n ^ (3 / 28 : ℝ) *
        (n : ℝ) ^ (-1 / 28 : ℝ) := by
  obtain ⟨hr6, _, _, hupper, hrn⟩ := logParameter_bounds n hn
  have h256 := logThreshold_six_ge n hn
  set r := logParameter n with hrdef
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl1 := log_ge_one n h256
  have hl0 : (0 : ℝ) ≤ Real.log n := by linarith
  have hΛ := logFactor_double_le n r hrn h256
  have hΛ0 : (0 : ℝ) ≤ logFactor (2 * r) := Nat.cast_nonneg _
  have hcast : (n : ℝ) ≤ (5920 * 8320 ^ 3 : ℝ) * (2 * (r : ℝ)) ^ 28 *
      (logFactor (2 * r) : ℝ) ^ 3 := by
    have h : (n : ℝ) ≤ (logThreshold (2 * r) : ℝ) := by exact_mod_cast hupper.le
    simpa only [logThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hcube : (logFactor (2 * r) : ℝ) ^ 3 ≤ 8 * Real.log n ^ 3 := by
    have := pow_le_pow_left₀ hΛ0 hΛ 3
    linarith [show (2 * Real.log n) ^ 3 = 8 * Real.log n ^ 3 by ring]
  have hbound : (n : ℝ) ≤ ((logConstant : ℝ) * Real.log n ^ 3) * (2 * (r : ℝ)) ^ 28 := by
    have hp : (0 : ℝ) ≤ (5920 * 8320 ^ 3 : ℝ) * (2 * (r : ℝ)) ^ 28 := by positivity
    have := mul_le_mul_of_nonneg_left hcube hp
    have hC : (logConstant : ℝ) = 8 * (5920 * 8320 ^ 3 : ℝ) := by
      simp only [logConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hC]
    nlinarith
  have hC0 : (0 : ℝ) ≤ logConstant := Nat.cast_nonneg _
  have hroot := Real.rpow_le_rpow hn0.le hbound (by norm_num : (0 : ℝ) ≤ 1 / 28)
  have hpow2 : ((2 * (r : ℝ)) ^ 28) ^ (1 / 28 : ℝ) = 2 * (r : ℝ) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ 2 * (r : ℝ) by positivity)
        (by decide : (28 : ℕ) ≠ 0))
  have hpowL : (Real.log n ^ 3) ^ (1 / 28 : ℝ) = Real.log n ^ (3 / 28 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
    norm_num
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC0 (by positivity),
    hpow2, hpowL] at hroot
  have hroot0 : (0 : ℝ) < (n : ℝ) ^ (1 / 28 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hneg : (n : ℝ) ^ (-1 / 28 : ℝ) = 1 / (n : ℝ) ^ (1 / 28 : ℝ) := by
    rw [show (-1 / 28 : ℝ) = -(1 / 28 : ℝ) by ring, Real.rpow_neg hn0.le, ← one_div]
  rw [hneg, mul_one_div, div_le_div_iff₀ hr0 hroot0]
  have h26 := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 26)
  linarith

theorem lower_error_log_bound (n : ℕ) (hn : 256 ≤ n) :
    (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) := by
  have hn8 : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn8]
  have hn4 : (0 : ℝ) < (n : ℝ) - 4 := by linarith only [hn8]
  have hfirst : (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 / (n : ℝ) := by
    apply (div_le_div_iff₀ hn4 hn0).2
    linarith only [hn8]
  have hpower := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ n by linarith only [hn8])
    (by norm_num : (-1 : ℝ) ≤ -1 / 28)
  rw [Real.rpow_neg_one] at hpower
  have hl1 := log_ge_one n hn
  have hL1 : (1 : ℝ) ≤ Real.log n ^ (3 / 28 : ℝ) := Real.one_le_rpow hl1 (by norm_num)
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 28 : ℝ) := Real.rpow_nonneg hn0.le _
  calc
    (2 : ℝ) / ((n : ℝ) - 4) ≤ 4 / (n : ℝ) := hfirst
    _ = 4 * (n : ℝ)⁻¹ := by rfl
    _ ≤ 4 * (n : ℝ) ^ (-1 / 28 : ℝ) := mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ ≤ 4 * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) := by nlinarith

noncomputable def logRemainderConstant : ℝ := 52 * (logConstant : ℝ) ^ (1 / 28 : ℝ) + 4

theorem logRemainderConstant_le : logRemainderConstant ≤ 205 := by
  have h : ((logConstant : ℕ) : ℝ) ^ (1 / 28 : ℝ) ≤ 201 / 52 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by norm_num) (by norm_num),
      show (28 : ℝ) = ((28 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num [logConstant]
  unfold logRemainderConstant
  linarith

/-- The normalised two-sided error with the logarithmic rate. -/
theorem shortest_length_error_log (n : ℕ) (hn : logThreshold 6 ≤ n) :
    |((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) - 2| ≤
      logRemainderConstant * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) := by
  obtain ⟨hr, _, hsize, _, _⟩ := logParameter_bounds n hn
  have h256 := logThreshold_six_ge n hn
  have hr0 : 0 < logParameter n := lt_of_lt_of_le (by decide : (0 : ℕ) < 6) hr
  obtain ⟨w, hw, hlength⟩ := finite_covering_word_log n (logParameter n) hr hsize
  have hword := (integer_bound_iff35 n (logParameter n) hr0 w).1 hlength
  have hminimum : (ConstAsym.L n : ℚ) ≤ (w.length : ℚ) := by
    exact_mod_cast ConstAsym.L_le_length hw
  have hfacQ : (0 : ℚ) < ((n - 4).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos (n - 4)
  have hupperQ : ((ConstAsym.L n : ℚ) - SuperpermutationBounds.F3 n) /
      ((n - 4).factorial : ℚ) ≤ 2 + 26 / (logParameter n : ℚ) := by
    apply (div_le_iff₀ hfacQ).2
    linarith only [hminimum, hword]
  have hupper : ((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
      ((n - 4).factorial : ℝ) ≤ 2 + 26 / (logParameter n : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hupperQ
    push_cast at hcast
    exact hcast
  have hlowerQ := ConstAsym.lower2_ratio (show 7 ≤ n by omega)
  have hlower : 2 - 2 / ((n : ℝ) - 4) ≤
      ((ConstAsym.L n : ℝ) - (SuperpermutationBounds.F3 n : ℝ)) /
        ((n - 4).factorial : ℝ) := by
    exact_mod_cast hlowerQ
  have hp : (0 : ℝ) ≤ Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [log_ge_one n h256]) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hupperRate := logParameter_inverse_bound n hn
  have hlowerRate := lower_error_log_bound n h256
  have hc0 : (0 : ℝ) ≤ (logConstant : ℝ) ^ (1 / 28 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hK1 : 4 * (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) ≤
      logRemainderConstant * (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hp
    unfold logRemainderConstant; linarith
  have hK2 : 52 * (logConstant : ℝ) ^ (1 / 28 : ℝ) *
      (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) ≤
      logRemainderConstant * (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hp
    unfold logRemainderConstant; linarith
  have e1 : logRemainderConstant * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) =
      logRemainderConstant * (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) := by ring
  have e2 : 52 * (logConstant : ℝ) ^ (1 / 28 : ℝ) * Real.log n ^ (3 / 28 : ℝ) *
      (n : ℝ) ^ (-1 / 28 : ℝ) = 52 * (logConstant : ℝ) ^ (1 / 28 : ℝ) *
      (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) := by ring
  have e3 : 4 * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) =
      4 * (Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ)) := by ring
  rw [e1]
  rw [e2] at hupperRate
  rw [e3] at hlowerRate
  apply abs_le.2
  constructor
  · linarith only [hlower, hlowerRate, hK1]
  · linarith only [hupper, hupperRate, hK2]

/-- The statement shape of Jay Pantone's `AlmanacAdapter.ExplicitError`, with the
project's own `Covers` and `Nat.factorial`: for every `n ≥ logThreshold 6`
(`5920 · 8320^3 · 6^28 · 4^3`, about `1.34 · 10^39`) the shortest superpermutation
length `S(n)` satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 205 (n-4)! (log n)^(3/28) n^(-1/28)`. -/
def ExplicitErrorLog28 : Prop :=
  ∀ n : Nat, 5920 * 8320 ^ 3 * 6 ^ 28 * 4 ^ 3 ≤ n →
    (∃ w : List (Fin n), SuperpermutationBounds.Covers w ∧
      (w.length : Real) ≤ (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) +
        205 * ((n - 4).factorial : Real) * Real.log n ^ (3 / 28 : Real) *
          (n : Real) ^ (-1 / 28 : Real)) ∧
    ∀ w : List (Fin n), SuperpermutationBounds.Covers w →
      (n.factorial : Real) + ((n - 1).factorial : Real) +
        ((n - 2).factorial : Real) + 2 * ((n - 4).factorial : Real) -
        205 * ((n - 4).factorial : Real) * Real.log n ^ (3 / 28 : Real) *
          (n : Real) ^ (-1 / 28 : Real) ≤ (w.length : Real)

theorem logThreshold_six : logThreshold 6 = 5920 * 8320 ^ 3 * 6 ^ 28 * 4 ^ 3 := by
  have h : logFactor 6 = 4 := by
    unfold logFactor
    have : Nat.log 2 6 = 2 := by
      apply Nat.log_eq_of_pow_le_of_lt_pow <;> norm_num
    omega
  unfold logThreshold
  rw [h]

/-- The explicit two-sided error bound with the logarithmic rate. -/
theorem explicit_error_log28 : ExplicitErrorLog28 := by
  intro n hn
  rw [← logThreshold_six] at hn
  have herr := shortest_length_error_log n hn
  have h256 := logThreshold_six_ge n hn
  have hf : (0 : ℝ) < ((n - 4).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hp : (0 : ℝ) ≤ Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [log_ge_one n h256]) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hK := logRemainderConstant_le
  have hF3 : ((SuperpermutationBounds.F3 n : ℚ) : ℝ) =
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) := by
    simp [SuperpermutationBounds.F3]
  rw [hF3] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  rw [le_sub_iff_add_le, le_div_iff₀ hf] at hlo
  rw [sub_le_iff_le_add, div_le_iff₀ hf] at hhi
  have hslack : logRemainderConstant * Real.log n ^ (3 / 28 : ℝ) * (n : ℝ) ^ (-1 / 28 : ℝ) *
      ((n - 4).factorial : ℝ) ≤ 205 * ((n - 4).factorial : ℝ) * Real.log n ^ (3 / 28 : ℝ) *
        (n : ℝ) ^ (-1 / 28 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hp hf.le)
    nlinarith
  constructor
  · obtain ⟨w, hw, hwl⟩ := ConstAsym.L_spec n
    refine ⟨w, hw, ?_⟩
    rw [hwl]
    nlinarith
  · intro w hw
    have hmin : (ConstAsym.L n : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast ConstAsym.L_le_length hw
    nlinarith

end CoefficientTwoPrecision.Asym28

#print axioms CoefficientTwoPrecision.Asym28.finite_covering_word_log
#print axioms CoefficientTwoPrecision.Asym28.logParameter_inverse_bound
#print axioms CoefficientTwoPrecision.Asym28.shortest_length_error_log
#print axioms CoefficientTwoPrecision.Asym28.logRemainderConstant_le
#print axioms CoefficientTwoPrecision.Asym28.explicit_error_log28
