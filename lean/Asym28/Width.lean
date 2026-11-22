import Asym35.Width
import Asym28.TD.CandidateSpace
import Asym28.TD.CatalogueBounds

/-!
# The width of the transversal design and the width-dependent definitions

Addition to Jay Pantone's quantitative development (release 9ccbe66).
Jay's controls form a grid of `r` rows and `r A` columns, so a stage has
`W = r^2 A` controls. On the transversal design of `Asym28.TD.ActiveGrid`
the columns are the residues modulo `q = tdQ r A`, the least prime `≥ A`
(for `r ≤ A`), so `W = r q`, with `A ≤ q ≤ 2A` (Bertrand) and `A q` blocks.
With `A = ⌈4 r^2 (log₂ r + 2)/β⌉` of `Asym35.Width` this gives
`1536 r^6 (log₂ r + 2) ≤ W ≤ 8320 r^6 (log₂ r + 2)`
(the grid had `W ≤ 4161 r^7 (log₂ r + 2)`).

The rest repeats, for this width, the definitions and lemmas of Jay's
`CandidateFactorization`, `ConstructionSize`, `CandidateSpace`,
`SourceSelection` and `ElementaryCountFactors` that mention his `sourceA`
or `sourceWidth`, as the earlier `Asym35.Width` did for the grid. The
proofs are his, with the names changed (suffix `28`); where `W = r^2 A`
was used, `W = r q` and `A ≤ q` are used instead.
-/

namespace CoefficientTwoPrecision.Asym28

open CoefficientTwoPrecision.Asym35

/-- The column modulus of the source family: the least prime `≥ max r A`. -/
def sourceQ28 (r : ℕ) : ℕ := TD.tdQ r (sourceA35 r)

def sourceWidth28 (r : ℕ) : ℕ := r * sourceQ28 r

def sourceGridCount28 (r : ℕ) : ℕ := sourceA35 r * sourceQ28 r

theorem rA_le (r : ℕ) (hr : 6 ≤ r) : r ≤ sourceA35 r := by
  have h := sourceA35_lower r hr
  have hL := logFactor_pos r
  have h1 : r ≤ 1536 * r ^ 5 * logFactor r := by
    calc
      r ≤ r ^ 5 := Nat.le_self_pow (by norm_num) r
      _ ≤ 1536 * r ^ 5 := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ 1536 * r ^ 5 * logFactor r := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem sourceQ28_ge (r : ℕ) : sourceA35 r ≤ sourceQ28 r := TD.le_tdQ_right _ _

theorem sourceQ28_ge_r (r : ℕ) : r ≤ sourceQ28 r := TD.le_tdQ_left _ _

theorem sourceA35_ge513 (r : ℕ) (hr : 6 ≤ r) : 513 ≤ sourceA35 r := by
  have h := sourceA35_lower r hr
  have hL := logFactor_pos r
  have h5 : 6 ^ 5 ≤ r ^ 5 := Nat.pow_le_pow_left hr 5
  have h1 : 513 ≤ 1536 * r ^ 5 * logFactor r := by
    calc
      513 ≤ 1536 * 6 ^ 5 * 1 := by norm_num
      _ ≤ 1536 * r ^ 5 * logFactor r :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h5) (by omega)
  omega

theorem sourceQ28_le (r : ℕ) (hr : 6 ≤ r) : sourceQ28 r ≤ 2 * sourceA35 r :=
  TD.tdQ_le_two r (sourceA35 r) (rA_le r hr) (sourceA35_ge513 r hr)

theorem sourceWidth28_lower6 (r : ℕ) (hr : 6 ≤ r) :
    1536 * r ^ 6 * logFactor r ≤ sourceWidth28 r := by
  have h := Nat.mul_le_mul_left r ((sourceA35_lower r hr).trans (sourceQ28_ge r))
  calc
    1536 * r ^ 6 * logFactor r = r * (1536 * r ^ 5 * logFactor r) := by ring
    _ ≤ r * sourceQ28 r := h
    _ = sourceWidth28 r := rfl

theorem sourceWidth28_lower (r : ℕ) (_hr : 6 ≤ r) : r ^ 2 ≤ sourceWidth28 r := by
  rw [pow_two]
  exact Nat.mul_le_mul_left r (sourceQ28_ge_r r)

theorem sourceWidth28_dvd (r : ℕ) : r ∣ sourceWidth28 r := ⟨sourceQ28 r, rfl⟩

theorem sourceWidth28_upper (r : ℕ) (hr : 6 ≤ r) :
    sourceWidth28 r ≤ 8320 * r ^ 6 * logFactor r := by
  have hAQ := sourceA35_upper r hr
  have hA : sourceA35 r ≤ 4160 * r ^ 5 * logFactor r := by
    have h : sourceA35 r < 4160 * r ^ 5 * logFactor r + 1 := by exact_mod_cast hAQ
    omega
  calc
    sourceWidth28 r = r * sourceQ28 r := rfl
    _ ≤ r * (2 * sourceA35 r) := Nat.mul_le_mul_left r (sourceQ28_le r hr)
    _ ≤ r * (2 * (4160 * r ^ 5 * logFactor r)) := Nat.mul_le_mul_left r (Nat.mul_le_mul_left 2 hA)
    _ = 8320 * r ^ 6 * logFactor r := by ring

/-- `CountingRatios`' coefficient identity for the new width. -/
theorem source_coefficient_identity28 (r : ℕ) (hr : 0 < r) :
    (sourceGridCount28 r : ℚ) * sourceBeta r = sourceRho35 r * (sourceWidth28 r : ℚ) := by
  have hrQ : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  simp only [sourceGridCount28, sourceRho35, sourceWidth28, Nat.cast_mul]
  field_simp [hrQ]

/-- `ElementaryCountFactors.sourceEta_width` for the new width. -/
theorem sourceEta_width28 (r : ℕ) (hr : 6 ≤ r) :
    1 ≤ (sourceWidth28 r : ℚ) * sourceEta r := by
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
  -- W = r q ≥ q ≥ A
  have hAW : (sourceA35 r : ℚ) ≤ sourceWidth28 r := by
    have h : sourceA35 r ≤ sourceWidth28 r :=
      (sourceQ28_ge r).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact_mod_cast h
  nlinarith

/-! ## `CandidateFactorization` for the new `A` -/

def guardCount28 (r : Nat) : Nat := sourceWidth28 r - r

def backgroundSize28 (r m : Nat) : Nat := m + guardCount28 r

def candidateCount28 (r m : Nat) : Nat :=
  sourceGridCount28 r * m.descFactorial (guardCount28 r) *
    ⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊

def guardFactor28 (r m : Nat) : ℚ :=
  (m.descFactorial (guardCount28 r) : ℚ) / (m : ℚ) ^ guardCount28 r

def floorFactor28 (r m : Nat) : ℚ :=
  (⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ : ℚ) /
    (sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3))

def backgroundFactor28 (r m : Nat) : ℚ := (backgroundSize28 r m : ℚ) / m

def insertionFactor28 (r m : Nat) : ℚ :=
  (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) / (m : ℚ) ^ sourceWidth28 r

theorem width_exponents28 (r : Nat) (hr : 6 ≤ r) :
    guardCount28 r + (r - 3) + 3 = sourceWidth28 r := by
  have hlower := sourceWidth28_lower r hr
  have hlinear : r ≤ r ^ 2 := by nlinarith
  unfold guardCount28
  omega

theorem actual_leading_rows28 (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount28 r m : ℚ) * ((r : ℚ) - 2) * (backgroundSize28 r m : ℚ) ^ 2 /
        (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) =
      (sourceRho35 r * sourceWidth28 r / m) *
        (guardFactor28 r m * floorFactor28 r m * backgroundFactor28 r m ^ (r - 3 + 2) /
          insertionFactor28 r m) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize28 r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize28 r m ≠ 0 by unfold backgroundSize28; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth28 r) hm)
  have h := CandidateFactorization.leading_row_identity (m : ℚ) (backgroundSize28 r m : ℚ)
    (sourceGridCount28 r : ℚ) (sourceEta r) (m.descFactorial (guardCount28 r) : ℚ)
    (⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) ((r : ℚ) - 2)
    (guardCount28 r) (r - 3) hmQ hM (ne_of_gt (CandidateFactorization.eta_pos r hr)) hD
  rw [width_exponents28 r hr, ← sourceBeta,
    source_coefficient_identity28 r (by omega)] at h
  simpa only [candidateCount28, Nat.cast_mul, guardFactor28, floorFactor28,
    backgroundFactor28, insertionFactor28] using h

theorem actual_leading_charge28 (r m : Nat) (hr : 6 ≤ r) (hm : 0 < m) :
    (candidateCount28 r m : ℚ) * (2 * ((r : ℚ) - 1)) * (backgroundSize28 r m : ℚ) /
        (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) =
      ((2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho35 r * sourceWidth28 r / m ^ 2) *
        (guardFactor28 r m * floorFactor28 r m * backgroundFactor28 r m ^ (r - 3 + 1) /
          insertionFactor28 r m) := by
  have hrQ : (6 : ℚ) ≤ r := by exact_mod_cast hr
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hM : (backgroundSize28 r m : ℚ) ≠ 0 := by
    exact_mod_cast (show backgroundSize28 r m ≠ 0 by unfold backgroundSize28; omega)
  have hD : (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingCount_pos m (sourceWidth28 r) hm)
  have hcoef : (sourceGridCount28 r : ℚ) * (2 * ((r : ℚ) - 1) * sourceEta r) =
      (2 * ((r : ℚ) - 1) / ((r : ℚ) - 2)) * sourceRho35 r * sourceWidth28 r := by
    rw [mul_assoc _ (sourceRho35 r), ← source_coefficient_identity28 r (by omega)]
    unfold sourceBeta
    field_simp [show (r : ℚ) - 2 ≠ 0 by linarith]
  have h := CandidateFactorization.leading_charge_identity (m : ℚ) (backgroundSize28 r m : ℚ)
    (sourceGridCount28 r : ℚ) (sourceEta r) (m.descFactorial (guardCount28 r) : ℚ)
    (⌊sourceEta r * (backgroundSize28 r m : ℚ) ^ (r - 3)⌋₊ : ℚ)
    (SourceUniverse.risingCount m (sourceWidth28 r) : ℚ) (2 * ((r : ℚ) - 1))
    (guardCount28 r) (r - 3) hmQ hM (ne_of_gt (CandidateFactorization.eta_pos r hr)) hD
  rw [width_exponents28 r hr, hcoef] at h
  simpa only [candidateCount28, Nat.cast_mul, guardFactor28, floorFactor28,
    backgroundFactor28, insertionFactor28] using h

/-! ## `ConstructionSize`, `CandidateSpace`, `SourceSelection` for the new `A` -/

theorem width_positive28 (r : Nat) (hr : 6 ≤ r) : 1 ≤ sourceWidth28 r := by
  have h := sourceWidth28_lower r hr
  nlinarith

theorem width_linear28 (r : Nat) (hr : 6 ≤ r) : r ≤ sourceWidth28 r := by
  have h := sourceWidth28_lower r hr
  nlinarith

theorem guard_number_eq28 (d : Nat) :
    TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)) = guardCount28 (d + 3) := rfl

theorem prescribed_card28 (m d : Nat)
    (S : Finset (LabelledReconstruction.Labelled
      (m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3))) d))
    (hS : S.card = ⌊sourceEta (d + 3) *
      ((m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)) : Nat) : ℚ) ^ d⌋₊) :
    (TD.CandidateSpace.candidates m d (sourceA35 (d + 3)) S).card =
      candidateCount28 (d + 3) m := by
  rw [TD.CandidateSpace.candidates_card, hS, guard_number_eq28]
  unfold candidateCount28 backgroundSize28
  simp only [Nat.add_sub_cancel, sourceGridCount28, sourceQ28]

theorem background_divisible28 (d m : Nat) (_hd : 3 ≤ d) (hm : d + 3 ∣ m) :
    d + 3 ∣ m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)) := by
  apply dvd_add hm
  unfold TD.GuardCatalogue.guardNumber
  exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_refl _)

theorem contour_height28 (d m : Nat) (hd : 3 ≤ d) :
    m + TD.GuardCatalogue.guardNumber d (sourceA35 (d + 3)) + (d + 2) - 1 =
      m + sourceWidth28 (d + 3) - 2 := by
  rw [guard_number_eq28]
  have hwidth := width_linear28 (d + 3) (by omega)
  unfold guardCount28
  omega

theorem control_width28 (d : Nat) :
    sourceWidth28 (d + 3) = (d + 3) * TD.tdQ (d + 3) (sourceA35 (d + 3)) := rfl

theorem width_eq28 (d : Nat) :
    TD.CatalogueBounds.width d (sourceA35 (d + 3)) = sourceWidth28 (d + 3) := rfl

end CoefficientTwoPrecision.Asym28

#print axioms CoefficientTwoPrecision.Asym28.sourceWidth28_upper
#print axioms CoefficientTwoPrecision.Asym28.sourceWidth28_lower6
#print axioms CoefficientTwoPrecision.Asym28.actual_leading_rows28
#print axioms CoefficientTwoPrecision.Asym28.prescribed_card28
