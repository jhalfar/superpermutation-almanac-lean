/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey, Yury Kudryashov, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum.Prime

/-!
# Bertrand's postulate for `n ≥ 512` (copied from Mathlib)

Copy of the parts of Mathlib's `Mathlib/NumberTheory/Primorial.lean` and
`Mathlib/NumberTheory/Bertrand.lean` (Mathlib commit 56a0058, Apache License
2.0, authors as above) that prove Bertrand's postulate for `n ≥ 512`, in the
namespace `CoefficientTwoPrecision.TD.Bertrand` (J. Halfar, November 2026).

Why a copy: Mathlib's `Primorial` imports `NumberTheory.PrimeCounting`, which
imports `Mathlib.Data.List.GetD`; that module and the inherited
`Lean435Compatibility` (imported by the Hunter word files of the construction)
both declare `List.getD_eq_getElem`, so the two cannot be imported together.
The proofs below are Mathlib's, unchanged except for the namespace and the
removal of the `module`/`public section` markers; the small cases `n < 512`
(proved in Mathlib by a list of primes) are not needed and not copied.
-/

namespace CoefficientTwoPrecision.TD.Bertrand

section Primorial

open Finset Nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`. -/
def primorial (n : ℕ) : ℕ := ∏ p ∈ range (n + 1) with p.Prime, p

local notation x "#" => primorial x

theorem primorial_pos (n : ℕ) : 0 < n# :=
  prod_pos fun _p hp ↦ (mem_filter.1 hp).2.pos

theorem primorial_succ {n : ℕ} (hn1 : n ≠ 1) (hn : Odd n) : (n + 1)# = n# := by
  refine prod_congr ?_ fun _ _ ↦ rfl
  rw [range_add_one, filter_insert, ite_eq_right fun h ↦ not_even_iff_odd.2 hn _]
  exact fun h ↦ h.even_sub_one <| mt succ.inj hn1

theorem primorial_add (m n : ℕ) :
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union, ← filter_union, Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]

theorem primorial_add_dvd {m n : ℕ} (h : n ≤ m) : (m + n)# ∣ m# * choose (m + n) m :=
  calc
    (m + n)# = m# * ∏ p ∈ Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
      mul_dvd_mul_left _ <|
        prod_primes_dvd _ (fun _ hk ↦ (mem_filter.1 hk).2.prime) fun p hp ↦ by
          rw [mem_filter, mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)

theorem primorial_add_le {m n : ℕ} (h : n ≤ m) : (m + n)# ≤ m# * choose (m + n) m :=
  le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)

theorem primorial_lt_four_pow (n : ℕ) (hn : n ≠ 0) : n# < 4 ^ n := by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ ≤ (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ ≤ 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ ≤ 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ

theorem primorial_le_four_pow (n : ℕ) : n# ≤ 4 ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

end Primorial

section Real

open Real

/-- A refined version of `bertrand_main_inequality` below. -/
theorem real_main_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert!
        ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : ℝ) • LinearMap.id)))
        using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : ℝ) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), this, one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, this,
        div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast, ← pow_mul, ← pow_add]
    conv in 4 => equals 2 ^ (2 : ℝ) => rw [rpow_two]; norm_num1
    rw [← rpow_mul, ← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

end Real

section NatPart

open Nat

open scoped Finset


/-- The inequality which contradicts Bertrand's postulate, for large enough `n`. -/
theorem bertrand_main_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @cast_le ℝ]
  simp only [cast_mul, cast_pow, ← Real.rpow_natCast, cast_ofNat]
  refine _root_.trans ?_ (real_main_inequality (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact cast_div_le.trans (by norm_cast)

/-- Without a Bertrand prime, the central binomial coefficient has only factors at most
`2 * n / 3 + 1`. -/
theorem centralBinom_factorization_small (n : ℕ) (n_large : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    centralBinom n = ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · grw [Nat.div_le_self]
  intro x hx h2x
  rw [Finset.mem_range, Nat.lt_succ_iff] at hx h2x
  rw [not_le, div_lt_iff_lt_mul three_pos, mul_comm x] at h2x
  obtain h | h : ¬ x.Prime ∨ x ≤ n := by simpa [imp_iff_not_or, hx.not_gt] using no_prime x
  · rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

/-- The upper bound on the central binomial coefficient without a Bertrand prime. -/
theorem centralBinom_le_of_no_bertrand_prime (n : ℕ) (n_large : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [centralBinom_factorization_small n n_large no_prime, ← this, ←
    Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : #(Finset.Icc 1 (sqrt (2 * n))) = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- **Bertrand's postulate** for `n ≥ 512`. -/
theorem exists_prime_lt_and_le_two_mul_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  have no_prime : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_large)
  contrapose! no_prime
  have : n.centralBinom ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_large) no_prime
  grw [this, ← mul_assoc, bertrand_main_inequality n_large]

end NatPart

end CoefficientTwoPrecision.TD.Bertrand

#print axioms CoefficientTwoPrecision.TD.Bertrand.exists_prime_lt_and_le_two_mul_eventually
