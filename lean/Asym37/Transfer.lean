import Asym37.CountRatio
import Quantitative.SparseStageIteration

/-!
# Exponent 37: the ratio-based sparse interface and the numerical transfer

Addition to Jay Pantone's quantitative development (release 9ccbe66).
`SparseStageIteration.SparseBlockCertificate` asks for exact formulas with
two relative errors `|theta|, |epsilon| ≤ E/m`. The transfer
(`ScheduledTransfer.scheduled_sparse_estimates`) only uses the local cost
ratio `n g ≤ (2 + 9/r) f` and the density lower bound `f ≥ ρW/(2n)`.
`SparseBlockCertificate37` asks for exactly these two facts (at the block
size `m`), plus the unchanged circle ratio. The numerical assembly is
`NumericalAssembly.scheduled_numerical_bound` with this interface and the
threshold `n ≥ transferConstant37 * r^37`.
-/

namespace CoefficientTwoPrecision.Asym37

open SuperpermutationUpperBound SuperpermutationUpperBound43586371
open StageState SourceUniverse

/-- The geometric input at one scheduled source size, in ratio form. -/
structure SparseBlockCertificate37 (r : ℕ) {m : ℕ} (S : BuiltStage m) where
  family : Block S (sourceWidth r)
  density_lower : sourceRho r * (sourceWidth r : ℚ) / (2 * (m : ℚ)) ≤
    (family.sourceRows : ℚ) / (risingCount m (sourceWidth r) : ℚ)
  cost_ratio : (m : ℚ) * (((family.sourceCharge : ℚ) + (family.advancedCircles : ℚ)) /
      (risingCount m (sourceWidth r) : ℚ)) ≤
    costCoefficient r * ratioAllowance r *
      ((family.sourceRows : ℚ) / (risingCount m (sourceWidth r) : ℚ))
  circle_ratio : (family.advancedCircles : ℚ) ≤
    ((r : ℚ) - 1) * (family.sourceCharge : ℚ) / (m : ℚ)

/-- The source-family interface of the exponent-37 assembly. -/
def SparseFamilySupplier37 (r : ℕ) : Prop :=
  ∀ (m : ℕ) (S : BuiltStage m), r ∣ m →
    threshold37 r ≤ m → Nonempty (SparseBlockCertificate37 r S)

/-! ## Size conditions for `n ≥ transferConstant37 * r^37` -/

theorem polynomial_threshold_conditions37 (r W n : ℕ) (hr : 6 ≤ r)
    (hWlower : r ^ 2 ≤ W) (hWupper : W ≤ 352 * r ^ 9)
    (hn : transferConstant37 * r ^ 37 ≤ n) :
    2 * (2960 * r ^ 10 * W ^ 3) ≤ n ∧
      96 * r ^ 2 ≤ n ∧
      2 * r * (r + W + (3 + 36 * binaryLength n)) ≤ n := by
  have hrpos : 1 ≤ r := by omega
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
  have hWpos : 1 ≤ W := hrpow.trans hWlower
  have hmul := Nat.mul_le_mul_left r hr
  have hroomW : r + 3 ≤ W := by nlinarith only [hr, hmul, hWlower]
  have hW3 : W ^ 3 ≤ (352 * r ^ 9) ^ 3 := Nat.pow_le_pow_left hWupper 3
  have hprimitive : 2 * (2960 * r ^ 10 * W ^ 3) ≤ n := by
    calc
      2 * (2960 * r ^ 10 * W ^ 3) = 5920 * r ^ 10 * W ^ 3 := by ring
      _ ≤ 5920 * r ^ 10 * (352 * r ^ 9) ^ 3 := Nat.mul_le_mul_left _ hW3
      _ = transferConstant37 * r ^ 37 := by unfold transferConstant37; ring
      _ ≤ n := hn
  have hE8 : 8 * r * (740 * r ^ 9 * W ^ 3) = 2 * (2960 * r ^ 10 * W ^ 3) := by ring
  have hWE : W ≤ 740 * r ^ 9 * W ^ 3 := by
    have h1 : W ≤ W ^ 3 := Nat.le_self_pow (by decide) W
    have h2 : 1 ≤ 740 * r ^ 9 := by
      have := Nat.one_le_pow 9 r (by omega)
      omega
    calc
      W ≤ W ^ 3 := h1
      _ = 1 * W ^ 3 := by ring
      _ ≤ 740 * r ^ 9 * W ^ 3 := Nat.mul_le_mul_right _ h2
  have hE : 2592 * r ≤ 740 * r ^ 9 * W ^ 3 := by
    have h1 : r ≤ r ^ 9 := Nat.le_self_pow (by decide) r
    have h3 : 1 ≤ W ^ 3 := Nat.one_le_pow 3 W (by omega)
    have h4 : 6 ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hr 8
    have h5 : r ^ 9 = r * r ^ 8 := by ring
    have h6 : 2592 * r ≤ 740 * r ^ 9 := by
      rw [h5]
      have := Nat.mul_le_mul_left r h4
      norm_num at this
      nlinarith
    calc
      2592 * r ≤ 740 * r ^ 9 := h6
      _ = 740 * r ^ 9 * 1 := by ring
      _ ≤ 740 * r ^ 9 * W ^ 3 := Nat.mul_le_mul_left _ h3
  exact ⟨hprimitive,
    room_of_primitive_threshold r W (740 * r ^ 9 * W ^ 3) n hr hroomW hWE hE
      (by rw [hE8]; exact hprimitive)⟩

theorem construction_threshold_conditions37 (r n : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant37 * r ^ 37 ≤ n) :
    2 * threshold37 r ≤ n ∧
      96 * r ^ 2 ≤ n ∧
      2 * r * (r + sourceWidth r + (3 + 36 * binaryLength n)) ≤ n := by
  exact polynomial_threshold_conditions37 r (sourceWidth r) n hr
    (sourceWidth_lower r hr) (sourceWidth_upper r hr) hn

theorem source_schedule_valid37 (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant37 * r ^ 37 ≤ n) :
    0 < n ∧ 0 < sourceWidth r ∧
      0 < sparseBlocks n r (sourceWidth r) ∧
      (n : ℚ) / (2 * (r : ℚ) * (sourceWidth r : ℚ)) ≤
        (sparseBlocks n r (sourceWidth r) : ℚ) ∧
      49 ≤ tailStart n ∧
      (∀ i < sparseBlocks n r (sourceWidth r),
        r ∣ sparseStart n r (sourceWidth r) i ∧
        threshold37 r ≤ sparseStart n r (sourceWidth r) i ∧
        n ≤ 2 * sparseStart n r (sourceWidth r) i ∧
        sparseStart n r (sourceWidth r) i ≤ n) := by
  obtain ⟨hprimitive, hsize, hroom⟩ := construction_threshold_conditions37 r n hr hn
  have hr0 : 0 < r := by omega
  have hrpow : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r hr0
  have hn0 : 0 < n := by nlinarith only [hsize, hrpow]
  have hW0 : 0 < sourceWidth r := lt_of_lt_of_le (by omega : 0 < r ^ 2)
    (sourceWidth_lower r hr)
  have hroom' : 2 * r * (r + sourceWidth r + tailLength n) ≤ n := hroom
  obtain ⟨hJ, hcount, hend, _, _, hstarts⟩ := schedule_bounds n r (sourceWidth r)
    hr hn0 hW0 (sourceWidth_dvd r) hroom'
  have hzero := hstarts 0 hJ
  have hstartHalf : n ≤ 2 * scheduleStart n r := by simpa [sparseStart] using hzero.2.1
  have hstartEnd : scheduleStart n r ≤ sparseEnd n r (sourceWidth r) := by
    unfold sparseEnd
    omega
  have htailHalf : n ≤ 2 * tailStart n := by omega
  have htail49 : 49 ≤ tailStart n := by nlinarith only [hsize, hrpow, htailHalf, hr]
  refine ⟨hn0, hW0, hJ, sparse_count_rational n r (sourceWidth r)
    (sparseBlocks n r (sourceWidth r)) hr0 hW0 hcount, htail49, ?_⟩
  intro i hi
  obtain ⟨hdiv, hhalf, hle⟩ := hstarts i hi
  exact ⟨hdiv, by omega, hhalf, hle⟩

/-! ## The local cost coefficient -/

theorem coefficient37_bound (r : ℚ) (hr : 6 ≤ r) :
    r * (costCoefficient r * ratioAllowance r) ≤ (2 + 9 / r) * (r - 1) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have hr4 : 0 < 4 * r - 1 := by linarith
  have hlhs : r * (costCoefficient r * ratioAllowance r) =
      (2 * r * (r - 1) * (4 * r + 1)) / ((r - 2) * (4 * r - 1)) := by
    unfold costCoefficient ratioAllowance
    field_simp
  have hrhs : (2 + 9 / r) * (r - 1) = ((2 * r + 9) * (r - 1)) / r := by
    field_simp
  rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) hr0]
  have hq : 0 ≤ 16 * r ^ 2 - 77 * r + 18 := by nlinarith
  have hp := mul_nonneg (show (0 : ℚ) ≤ r - 1 by linarith) hq
  nlinarith [hp]

/-- `ScheduledTransfer.scheduled_sparse_estimates` from the ratio interface. -/
theorem scheduled_sparse_estimates37 (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant37 * r ^ 37 ≤ n) (f g : ℕ → ℚ)
    (hf : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ f i ∧ f i ≤ 1)
    (hg0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ g i)
    (hlower : ∀ i < sparseBlocks n r (sourceWidth r),
      sourceRho r * (sourceWidth r : ℚ) / (2 * (sparseStart n r (sourceWidth r) i : ℚ)) ≤ f i)
    (hratio : ∀ i < sparseBlocks n r (sourceWidth r),
      (sparseStart n r (sourceWidth r) i : ℚ) * g i ≤
        costCoefficient r * ratioAllowance r * f i) :
    (∀ i < sparseBlocks n r (sourceWidth r),
      (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i) ∧
      (r : ℚ) / 4 ≤ densitySum f (sparseBlocks n r (sourceWidth r)) ∧
      pending f (sparseBlocks n r (sourceWidth r)) ≤ 4 / (r : ℚ) := by
  obtain ⟨hn0, hW0, _, hJ, _, hstarts⟩ := source_schedule_valid37 n r hr hn
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith only [hrQ]
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
  have hWQ : (0 : ℚ) < sourceWidth r := by exact_mod_cast hW0
  obtain ⟨hrho, _⟩ := sourceRho_bounds r hr
  have hrho0 : 0 ≤ sourceRho r := (sq_nonneg (r : ℚ)).trans hrho
  have hstartLower : (((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) ≤
      (scheduleStart n r : ℚ) :=
    (roundUpMultiple_bounds r ((((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ))
      (by omega)
      (mul_nonneg (div_nonneg (by linarith only [hrQ]) (le_of_lt hr0))
        (le_of_lt hnQ))).1
  have hcoef := coefficient37_bound (r : ℚ) hrQ
  have hlocal : ∀ i < sparseBlocks n r (sourceWidth r),
      (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i ∧
      sourceRho r * (sourceWidth r : ℚ) / (2 * (n : ℚ)) ≤ f i := by
    intro i hi
    obtain ⟨_, _, hhalfN, hleN⟩ := hstarts i hi
    have hhalf : (n : ℚ) ≤ 2 * (sparseStart n r (sourceWidth r) i : ℚ) := by
      exact_mod_cast hhalfN
    have hm0 : (0 : ℚ) < sparseStart n r (sourceWidth r) i := by linarith only [hhalf, hnQ]
    have hle : (sparseStart n r (sourceWidth r) i : ℚ) ≤ n := by exact_mod_cast hleN
    have hm : (((r : ℚ) - 1) / (r : ℚ)) * (n : ℚ) ≤
        (sparseStart n r (sourceWidth r) i : ℚ) := by
      apply hstartLower.trans
      exact_mod_cast (show scheduleStart n r ≤ sparseStart n r (sourceWidth r) i by
        unfold sparseStart
        omega)
    set mi : ℚ := (sparseStart n r (sourceWidth r) i : ℚ) with hmi
    have hmMul : ((r : ℚ) - 1) * n ≤ r * mi := by
      have h := (div_mul_eq_mul_div ((r : ℚ) - 1) (r : ℚ) (n : ℚ)) ▸ hm
      rw [div_le_iff₀ hr0] at h
      linarith only [h]
    have hfi := (hf i hi).1
    have hgi := hg0 i hi
    have hcost : (n : ℚ) * g i ≤ (2 + 9 / (r : ℚ)) * f i := by
      have hr1 : (0 : ℚ) < (r : ℚ) - 1 := by linarith only [hrQ]
      have h1 : ((r : ℚ) - 1) * ((n : ℚ) * g i) ≤ r * (mi * g i) := by
        have := mul_le_mul_of_nonneg_right hmMul hgi
        linarith only [this]
      have h2 : r * (mi * g i) ≤ r * (costCoefficient r * ratioAllowance r * f i) :=
        mul_le_mul_of_nonneg_left (hratio i hi) hr0.le
      have h3 : r * (costCoefficient r * ratioAllowance r * f i) ≤
          ((2 + 9 / (r : ℚ)) * ((r : ℚ) - 1)) * f i := by
        have := mul_le_mul_of_nonneg_right hcoef hfi
        linarith only [this]
      have h4 : ((r : ℚ) - 1) * ((n : ℚ) * g i) ≤ ((r : ℚ) - 1) * ((2 + 9 / (r : ℚ)) * f i) := by
        linarith only [h1, h2, h3]
      exact le_of_mul_le_mul_left h4 hr1
    have hdens : sourceRho r * (sourceWidth r : ℚ) / (2 * (n : ℚ)) ≤ f i := by
      refine le_trans ?_ (hlower i hi)
      apply div_le_div_of_nonneg_left (mul_nonneg hrho0 hWQ.le) (by positivity)
      linarith only [hle]
    exact ⟨hcost, hdens⟩
  have hsum := sparse_densitySum_ge f (sparseBlocks n r (sourceWidth r))
    (n : ℚ) (r : ℚ) (sourceRho r) (sourceWidth r : ℚ) hnQ hr0 hWQ hrho hJ
    (fun i hi => (hlocal i hi).2)
  exact ⟨fun i hi => (hlocal i hi).1, hsum,
    pending_le_four_div f (sparseBlocks n r (sourceWidth r)) (r : ℚ) hr0 hf hsum⟩

/-! ## Numerical data and the complete scheduled bound -/

structure SparseNumericalData37 (n r : ℕ) where
  rows : ℕ → ℕ
  charge : ℕ → ℕ
  circles : ℕ → ℕ
  rows_le : ∀ i < sparseBlocks n r (sourceWidth r), rows i ≤ scheduledDenominator n r i
  density_lower : ∀ i < sparseBlocks n r (sourceWidth r),
    sourceRho r * (sourceWidth r : ℚ) / (2 * (sparseStart n r (sourceWidth r) i : ℚ)) ≤
      (rows i : ℚ) / (scheduledDenominator n r i : ℚ)
  cost_ratio : ∀ i < sparseBlocks n r (sourceWidth r),
    (sparseStart n r (sourceWidth r) i : ℚ) *
        (((charge i : ℚ) + (circles i : ℚ)) / (scheduledDenominator n r i : ℚ)) ≤
      costCoefficient r * ratioAllowance r * ((rows i : ℚ) / (scheduledDenominator n r i : ℚ))
  circle_ratio : ∀ i < sparseBlocks n r (sourceWidth r),
    (circles i : ℚ) ≤ ((r : ℚ) - 1) * (charge i : ℚ) /
      (sparseStart n r (sourceWidth r) i : ℚ)

def SparseNumericalData37.density {n r : ℕ} (S : SparseNumericalData37 n r) (i : ℕ) : ℚ :=
  (S.rows i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData37.chargeRate {n r : ℕ} (S : SparseNumericalData37 n r) (i : ℕ) : ℚ :=
  (S.charge i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData37.circleRate {n r : ℕ} (S : SparseNumericalData37 n r) (i : ℕ) : ℚ :=
  (S.circles i : ℚ) / (scheduledDenominator n r i : ℚ)

def SparseNumericalData37.totalRate {n r : ℕ} (S : SparseNumericalData37 n r) (i : ℕ) : ℚ :=
  ((S.charge i : ℚ) + (S.circles i : ℚ)) / (scheduledDenominator n r i : ℚ)

/-- `NumericalAssembly.scheduled_numerical_bound` for the exponent-37 data. -/
theorem scheduled_numerical_bound37 (n r : ℕ) (hr : 6 ≤ r)
    (hn : transferConstant37 * r ^ 37 ≤ n) (S : SparseNumericalData37 n r)
    (T : DenseNumericalTrace n (pending S.density (sparseBlocks n r (sourceWidth r)))) :
    (n : ℚ) * accumulatedCost S.density S.totalRate (sparseBlocks n r (sourceWidth r)) +
      (n : ℚ) * T.X (denseBlocks n) +
      ((n : ℚ) * (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) +
        T.z (denseBlocks n)) + 2 * (n : ℚ) * T.p (denseBlocks n)) ≤ 2 + 74 / (r : ℚ) := by
  obtain ⟨hn0, hW0, hJpos, _, htail49, hstarts⟩ := source_schedule_valid37 n r hr hn
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℚ) < r := by linarith only [hrQ]
  have hr1 : (1 : ℚ) ≤ r := by linarith only [hrQ]
  have htail0 : (0 : ℚ) < tailStart n := by exact_mod_cast (show 0 < tailStart n by omega)
  have hstart0 := hstarts 0 hJpos
  have hm0half : (n : ℚ) ≤ 2 * (scheduleStart n r : ℚ) := by
    have h : n ≤ 2 * scheduleStart n r := by simpa [sparseStart] using hstart0.2.2.1
    exact_mod_cast h
  have hm0 : (0 : ℚ) < scheduleStart n r := by linarith only [hm0half, hnQ]
  have hm0n : (scheduleStart n r : ℚ) ≤ n := by
    have h : scheduleStart n r ≤ n := by simpa [sparseStart] using hstart0.2.2.2
    exact_mod_cast h
  have hroom : 2 * r * (r + sourceWidth r + tailLength n) ≤ n :=
    (construction_threshold_conditions37 r n hr hn).2.2
  have hend := (schedule_bounds n r (sourceWidth r) hr hn0 hW0 (sourceWidth_dvd r) hroom).2.2.1
  have hm0End : scheduleStart n r ≤ sparseEnd n r (sourceWidth r) := by unfold sparseEnd; omega
  have htailhalf : (n : ℚ) ≤ 2 * (tailStart n : ℚ) := by
    have h : (scheduleStart n r : ℚ) ≤ tailStart n := by exact_mod_cast hm0End.trans hend
    linarith only [hm0half, h]
  have hD : ∀ i < sparseBlocks n r (sourceWidth r), (0 : ℚ) < scheduledDenominator n r i := by
    intro i hi
    have hhalf := (hstarts i hi).2.2.1
    have hm : 0 < sparseStart n r (sourceWidth r) i := by omega
    exact_mod_cast risingCount_pos _ _ hm
  have hf : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.density i ∧ S.density i ≤ 1 := by
    intro i hi
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
    · apply (div_le_iff₀ (hD i hi)).2
      simpa only [one_mul] using (show (S.rows i : ℚ) ≤ scheduledDenominator n r i by
        exact_mod_cast S.rows_le i hi)
  have hg0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.totalRate i := by
    intro i hi
    exact div_nonneg (by positivity) (le_of_lt (hD i hi))
  obtain ⟨hcost, hsum, _⟩ := scheduled_sparse_estimates37 n r hr hn S.density S.totalRate
    hf hg0 S.density_lower S.cost_ratio
  have hRate : ∀ i, S.totalRate i = S.chargeRate i + S.circleRate i := by
    intro i
    exact add_div _ _ _
  have hq0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.chargeRate i := by
    intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
  have hc0 : ∀ i < sparseBlocks n r (sourceWidth r), 0 ≤ S.circleRate i := by
    intro i hi
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (hD i hi))
  have hratio : ∀ i < sparseBlocks n r (sourceWidth r), S.circleRate i ≤
      (((r : ℚ) - 1) / (scheduleStart n r : ℚ)) * S.chargeRate i := by
    intro i hi
    apply normalized_circle_ratio (S.charge i : ℚ) (S.circles i : ℚ)
      (scheduledDenominator n r i : ℚ) (sparseStart n r (sourceWidth r) i : ℚ)
      (scheduleStart n r : ℚ) (r : ℚ) (Nat.cast_nonneg _) (hD i hi) hm0 _ hr1 (S.circle_ratio i hi)
    exact_mod_cast (show scheduleStart n r ≤ sparseStart n r (sourceWidth r) i by
      unfold sparseStart
      omega)
  have hcoeff : 2 + 9 / (r : ℚ) ≤ 8 := by
    have h : 9 / (r : ℚ) ≤ 6 := (div_le_iff₀ hr0).2 (by linarith only [hrQ])
    linarith only [h]
  have hcost8 : ∀ i < sparseBlocks n r (sourceWidth r),
      (scheduleStart n r : ℚ) * (S.chargeRate i + S.circleRate i) ≤ 8 * S.density i := by
    intro i hi
    rw [← hRate i]
    exact (mul_le_mul_of_nonneg_right hm0n (by rw [hRate i]; exact add_nonneg (hq0 i hi) (hc0 i hi))).trans
      ((hcost i hi).trans (mul_le_mul_of_nonneg_right hcoeff (hf i hi).1))
  have hsparse := sparse_circle_bound S.density S.chargeRate S.circleRate
    (sparseBlocks n r (sourceWidth r)) (scheduleStart n r : ℚ) (r : ℚ) hm0 hr1
    (fun i hi => (hf i hi).2) hc0 hratio hcost8
  have hp0 := pending_nonneg S.density (sparseBlocks n r (sourceWidth r)) (fun i hi => (hf i hi).2)
  have hp1 := pending_le_one S.density (sparseBlocks n r (sourceWidth r)) hf
  have htailCost := dense_trace_cost n _ T htail0
  have hdense := dense_cost_scaling (n : ℚ) (tailStart n : ℚ)
    (pending S.density (sparseBlocks n r (sourceWidth r))) (T.X (denseBlocks n))
    htail0 hp0 (le_of_lt hnQ) htailhalf htailCost
  have htailCircles := dense_trace_circles n _ T htail0 hp1
  have hz := circle_mass_uniform (n : ℚ) (scheduleStart n r : ℚ) (tailStart n : ℚ)
    (r : ℚ) (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)))
    (T.z (denseBlocks n)) hnQ hm0 htail0 hr1 hm0half htailhalf hsparse htailCircles
  have hp := dense_pending_lt_inverse_cube n hn0 T.p
    (by rw [T.p_zero]; exact hp1) T.contraction
  have hnSize : 96 * (r : ℚ) ^ 2 ≤ n := by
    exact_mod_cast (construction_threshold_conditions37 r n hr hn).2.1
  have hj := completion_mass_error_bound (n : ℚ) (r : ℚ)
    (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) + T.z (denseBlocks n))
    (T.p (denseBlocks n)) hrQ hnSize hz (le_of_lt hp)
  exact finite_transfer_coefficient S.density S.totalRate (sparseBlocks n r (sourceWidth r))
    (n : ℚ) (r : ℚ) ((n : ℚ) * T.X (denseBlocks n))
    ((n : ℚ) * (accumulatedCost S.density S.circleRate (sparseBlocks n r (sourceWidth r)) +
      T.z (denseBlocks n)) + 2 * (n : ℚ) * T.p (denseBlocks n))
    hr0 hf hsum hcost hdense hj

end CoefficientTwoPrecision.Asym37

#print axioms CoefficientTwoPrecision.Asym37.construction_threshold_conditions37
#print axioms CoefficientTwoPrecision.Asym37.source_schedule_valid37
#print axioms CoefficientTwoPrecision.Asym37.scheduled_sparse_estimates37
#print axioms CoefficientTwoPrecision.Asym37.scheduled_numerical_bound37
