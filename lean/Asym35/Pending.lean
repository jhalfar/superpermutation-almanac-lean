import Asym35.Width
import Quantitative.ScheduleArithmetic

/-!
# Exponent 35: the pending mass halves on every group of sparse blocks

Addition to Jay Pantone's quantitative development (release 9ccbe66).
His sparse transfer bounds the pending mass `p_J = ∏ (1 - f_i)` through the
invariant `p_J (1 + Σ f_i) ≤ 1` (`RationalTransfer.pending_invariant`) and
needs `Σ f_i ≥ r/4` for `p_J ≤ 4/r`, i.e. the density `ρ ≥ r^2`
(`ScheduleArithmetic.pending_after_sparse`). Applied to consecutive groups
of `g = ⌈1/b⌉` blocks (each `f_i ≥ b`), the same invariant halves the
pending mass on every group, so `log₂ r + 1` groups give `p_J ≤ 1/r`. With
`J ≥ n/(2rW)` blocks of density `f_i ≥ ρW/(2n)` this needs only
`ρ ≥ 4 r (log₂ r + 2)` (and `n ≥ 2 r W (log₂ r + 2)^2`).
Everything here is exact rational arithmetic; no logarithm or exponential
of real numbers is used.
-/

namespace CoefficientTwoPrecision.Asym35

/-- The pending mass of a concatenation of two runs of blocks. -/
theorem pending_add (f : ℕ → ℚ) (a k : ℕ) :
    pending f (a + k) = pending f a * pending (fun i => f (a + i)) k := by
  induction k with
  | zero => simp [pending]
  | succ k ih =>
    have h1 : pending f (a + (k + 1)) = pending f (a + k) * (1 - f (a + k)) := rfl
    have h2 : pending (fun i => f (a + i)) (k + 1) =
        pending (fun i => f (a + i)) k * (1 - f (a + k)) := rfl
    rw [h1, h2, ih]
    ring

theorem pending_le_one' (f : ℕ → ℚ) (j : ℕ) (hf : ∀ i < j, 0 ≤ f i ∧ f i ≤ 1) :
    pending f j ≤ 1 := by
  have hp := pending_nonneg f j (fun i hi => (hf i hi).2)
  have hs := densitySum_nonneg f j (fun i hi => (hf i hi).1)
  have hi := pending_invariant f j hf
  nlinarith

/-- More blocks never increase the pending mass. -/
theorem pending_antitone (f : ℕ → ℚ) (j J : ℕ) (hjJ : j ≤ J)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1) : pending f J ≤ pending f j := by
  obtain ⟨k, rfl⟩ : ∃ k, J = j + k := ⟨J - j, by omega⟩
  rw [pending_add]
  have hp := pending_nonneg f j (fun i hi => (hf i (by omega)).2)
  have hq := pending_le_one' (fun i => f (j + i)) k (fun i hi => hf (j + i) (by omega))
  nlinarith

/-- One group of `g` blocks, each of density at least `b`, with `g b ≥ 1`,
halves the pending mass. -/
theorem pending_group_half (f : ℕ → ℚ) (g : ℕ) (b : ℚ)
    (hf : ∀ i < g, 0 ≤ f i ∧ f i ≤ 1) (hb : ∀ i < g, b ≤ f i)
    (hgb : 1 ≤ (g : ℚ) * b) : pending f g ≤ 1 / 2 := by
  have hp := pending_nonneg f g (fun i hi => (hf i hi).2)
  have hi := pending_invariant f g hf
  have hs := densitySum_lower f g b hb
  nlinarith

/-- `k` consecutive groups: the pending mass is at most `(1/2)^k`. -/
theorem pending_groups (f : ℕ → ℚ) (g : ℕ) (b : ℚ) (hgb : 1 ≤ (g : ℚ) * b) :
    ∀ k : ℕ, (∀ i < k * g, 0 ≤ f i ∧ f i ≤ 1) → (∀ i < k * g, b ≤ f i) →
      pending f (k * g) ≤ (1 / 2 : ℚ) ^ k := by
  intro k
  induction k with
  | zero => intro _ _; simp [pending]
  | succ k ih =>
    intro hf hb
    have hsplit : (k + 1) * g = k * g + g := by ring
    rw [hsplit, pending_add]
    have hprev := ih (fun i hi => hf i (by rw [hsplit]; omega))
      (fun i hi => hb i (by rw [hsplit]; omega))
    have hgroup := pending_group_half (fun i => f (k * g + i)) g b
      (fun i hi => hf (k * g + i) (by rw [hsplit]; omega))
      (fun i hi => hb (k * g + i) (by rw [hsplit]; omega)) hgb
    have hp := pending_nonneg f (k * g) (fun i hi => (hf i (by rw [hsplit]; omega)).2)
    have hq := pending_nonneg (fun i => f (k * g + i)) g
      (fun i hi => (hf (k * g + i) (by rw [hsplit]; omega)).2)
    calc
      pending f (k * g) * pending (fun i => f (k * g + i)) g ≤
          (1 / 2 : ℚ) ^ k * (1 / 2) := mul_le_mul hprev hgroup hq (by positivity)
      _ = (1 / 2 : ℚ) ^ (k + 1) := by rw [pow_succ]

/-- The pending mass after the sparse blocks is at most `1/r`, from the
density `ρ ≥ 4 r (log₂ r + 2)` (in place of Jay's `ρ ≥ r^2` and `4/r`). -/
theorem sparse_pending_le_inv (f : ℕ → ℚ) (J r : ℕ) (n rho W : ℚ)
    (hn : 0 < n) (hr : 1 ≤ r) (hW : 0 < W)
    (hrho : 4 * (r : ℚ) * logFactor r ≤ rho)
    (hJ : n / (2 * r * W) ≤ (J : ℚ))
    (hroom : 2 * (r : ℚ) * W * (logFactor r : ℚ) ^ 2 ≤ n)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1)
    (hlower : ∀ i < J, rho * W / (2 * n) ≤ f i) :
    pending f J ≤ 1 / (r : ℚ) := by
  set L : ℕ := logFactor r with hLdef
  have hL2 : 2 ≤ L := logFactor_pos r
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hLQ : (2 : ℚ) ≤ L := by exact_mod_cast hL2
  have hrho0 : 0 < rho := by
    have : 0 < 4 * (r : ℚ) * L := by positivity
    linarith
  set b : ℚ := rho * W / (2 * n) with hbdef
  have hb0 : 0 < b := by positivity
  set g : ℕ := ⌈1 / b⌉₊ with hgdef
  have hgb : 1 ≤ (g : ℚ) * b := by
    have h := Nat.le_ceil (1 / b)
    rw [← hgdef] at h
    have := mul_le_mul_of_nonneg_right h hb0.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hb0)] at this
  have hg : (g : ℚ) < 1 / b + 1 := Nat.ceil_lt_add_one (by positivity)
  -- 1/b = 2n/(ρW) ≤ N/L with N = n/(2rW)
  set N : ℚ := n / (2 * r * W) with hNdef
  have hN0 : 0 ≤ N := by positivity
  have hinvb : 1 / b ≤ N / L := by
    rw [hbdef, hNdef, one_div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left hrho (show (0 : ℚ) ≤ 2 * n * W by positivity)
    nlinarith
  set k : ℕ := L - 1 with hkdef
  have hkQ : (k : ℚ) = (L : ℚ) - 1 := by
    rw [hkdef, Nat.cast_sub (by omega), Nat.cast_one]
  -- k g ≤ J
  have hroomN : (L : ℚ) * L ≤ N := by
    rw [hNdef, le_div_iff₀ (by positivity)]
    nlinarith
  have hkg : ((k * g : ℕ) : ℚ) ≤ J := by
    have hgN : (g : ℚ) ≤ N / L + 1 := by linarith
    have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
    have hstep : (k : ℚ) * g ≤ (k : ℚ) * (N / L + 1) := mul_le_mul_of_nonneg_left hgN hk0
    have hLpos : (0 : ℚ) < L := by linarith
    have hfrac : (k : ℚ) * (N / L + 1) ≤ N := by
      rw [hkQ]
      have e : ((L : ℚ) - 1) * (N / L + 1) = N - N / L + L - 1 := by field_simp; ring
      rw [e]
      have hNL : (L : ℚ) ≤ N / L := by rw [le_div_iff₀ hLpos]; linarith
      linarith
    push_cast
    linarith
  have hkgJ : k * g ≤ J := by exact_mod_cast hkg
  have hmono := pending_antitone f (k * g) J hkgJ hf
  have hgroups := pending_groups f g b hgb k (fun i hi => hf i (by omega))
    (fun i hi => hlower i (by omega))
  have hpow : (1 / 2 : ℚ) ^ k ≤ 1 / (r : ℚ) := by
    have hlt : r < 2 ^ k := lt_two_pow_log r
    have hlt' : (r : ℚ) < (2 : ℚ) ^ k := by exact_mod_cast hlt
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hrQ]
    linarith
  exact hmono.trans (hgroups.trans hpow)

/-- `FiniteTransfer.finite_transfer_coefficient` with the pending bound `1/r`:
the coefficient `2 + 9/r + 16/r + 1/r = 2 + 26/r`. -/
theorem finite_transfer_coefficient35 (f g : ℕ → ℚ) (J : ℕ)
    (n r dense joining : ℚ) (hr : 0 < r)
    (hf : ∀ i < J, 0 ≤ f i ∧ f i ≤ 1)
    (hps : pending f J ≤ 1 / r)
    (hcost : ∀ i < J, n * g i ≤ (2 + 9 / r) * f i)
    (hdense : dense ≤ 16 * pending f J) (hjoining : joining ≤ 1 / r) :
    n * accumulatedCost f g J + dense + joining ≤ 2 + 26 / r := by
  have hp := pending_nonneg f J (fun i hi => (hf i hi).2)
  have hK : 0 ≤ 2 + 9 / r := by
    have : 0 ≤ (9 : ℚ) / r := div_nonneg (by norm_num) (le_of_lt hr)
    linarith
  have hI := cost_invariant f g J n (2 + 9 / r)
    (fun i hi => (hf i hi).2) hcost
  have hnonneg : 0 ≤ (2 + 9 / r) * pending f J := mul_nonneg hK hp
  have hsparse : n * accumulatedCost f g J ≤ 2 + 9 / r := by
    linarith only [hI, hnonneg]
  have hmult := mul_le_mul_of_nonneg_left hps (by norm_num : (0 : ℚ) ≤ 16)
  have htail : dense ≤ 16 / r := by
    calc
      dense ≤ 16 * pending f J := hdense
      _ ≤ 16 * (1 / r) := hmult
      _ = 16 / r := by ring
  have heq : (2 + 9 / r) + 16 / r + 1 / r = 2 + 26 / r := by ring
  linarith only [hsparse, htail, hjoining, heq]

end CoefficientTwoPrecision.Asym35

#print axioms CoefficientTwoPrecision.Asym35.pending_groups
#print axioms CoefficientTwoPrecision.Asym35.sparse_pending_le_inv
#print axioms CoefficientTwoPrecision.Asym35.finite_transfer_coefficient35
