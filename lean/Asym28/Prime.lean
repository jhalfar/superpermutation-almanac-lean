import IntegerControlGrid
import Asym28.Bertrand
import Mathlib.Data.Nat.Prime.Int

/-!
# The column modulus of the transversal design

Addition to Jay Pantone's quantitative development (release 9ccbe66).
His control grid (`IntegerControlGrid`, `Quantitative.ActiveGrid`) has `r`
rows and `Q = r A` columns; block `(a, b)` takes column `(a i + b) mod Q` in
row `i`. Two distinct blocks share at most one control because
`|(a - a') (i - j)| < Q`. The same holds for a prime modulus `q` with
`r ≤ q` and `A ≤ q`: then `q` divides neither `a - a'` nor `i - j`. This is
the transversal design `TD(r, q)` restricted to `A` parallel classes. Its
width is `r q ≤ 2 r max(r, A)` once `max(r, A) ≥ 513` (Bertrand's postulate,
`Asym28.Bertrand`, a copy of Mathlib's proof for `n ≥ 512`) instead of `r^2 A`.

`tdQ r A` is the least prime `≥ max r A`.
-/

namespace CoefficientTwoPrecision.TD

/-- The least prime that is at least `max r A`. -/
def tdQ (r A : Nat) : Nat := Nat.find (Nat.exists_infinite_primes (max r A))

theorem tdQ_spec (r A : Nat) : max r A ≤ tdQ r A ∧ (tdQ r A).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (max r A))

theorem tdQ_prime (r A : Nat) : (tdQ r A).Prime := (tdQ_spec r A).2

theorem tdQ_pos (r A : Nat) : 0 < tdQ r A := (tdQ_prime r A).pos

theorem le_tdQ_left (r A : Nat) : r ≤ tdQ r A := le_trans (le_max_left r A) (tdQ_spec r A).1

theorem le_tdQ_right (r A : Nat) : A ≤ tdQ r A := le_trans (le_max_right r A) (tdQ_spec r A).1

/-- Bertrand's postulate: `tdQ r A ≤ 2 max r A` once `max r A ≥ 513`. -/
theorem tdQ_le_two_max (r A : Nat) (h : 513 ≤ max r A) : tdQ r A ≤ 2 * max r A := by
  obtain ⟨p, hp, hlt, hle⟩ := Bertrand.exists_prime_lt_and_le_two_mul_eventually (max r A - 1)
    (by omega)
  have hmin := Nat.find_min' (Nat.exists_infinite_primes (max r A))
    (show max r A ≤ p ∧ p.Prime from ⟨by omega, hp⟩)
  change tdQ r A ≤ p at hmin
  omega

-- Only the lemmas above are used downstream; `Nat.find` is never unfolded.
attribute [irreducible] tdQ

/-- For `r ≤ A`, `A ≥ 513`: `tdQ r A ≤ 2 A`. -/
theorem tdQ_le_two (r A : Nat) (hrA : r ≤ A) (hA : 513 ≤ A) : tdQ r A ≤ 2 * A := by
  have hmax : max r A = A := max_eq_right hrA
  have h := tdQ_le_two_max r A (by omega)
  rwa [hmax] at h

/-- The column of block `(a, b)` in row `i`, modulo `q`. -/
def column (q a b i : Nat) : Nat := (a * i + b) % q

/-- Two shared distinct rows determine slope and intercept, for a prime
modulus that is at least the number of rows and the number of slopes. -/
theorem two_shared_rows (q A r a a' b b' i j : Nat) (hq : q.Prime)
    (hAq : A ≤ q) (hrq : r ≤ q)
    (ha : a < A) (ha' : a' < A) (hb : b < q) (hb' : b' < q)
    (hi : i < r) (hj : j < r) (hij : i ≠ j)
    (hci : column q a b i = column q a' b' i)
    (hcj : column q a b j = column q a' b' j) :
    a = a' ∧ b = b' := by
  have hdi : ((q : Nat) : Int) ∣
      ((a : Int) * (i : Int) + (b : Int)) - ((a' : Int) * (i : Int) + (b' : Int)) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using
      IntegerControlGrid.equal_remainders_dvd (a * i + b) (a' * i + b') q hci
  have hdj : ((q : Nat) : Int) ∣
      ((a : Int) * (j : Int) + (b : Int)) - ((a' : Int) * (j : Int) + (b' : Int)) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using
      IntegerControlGrid.equal_remainders_dvd (a * j + b) (a' * j + b') q hcj
  have hd := Int.dvd_sub hdi hdj
  have hdet :
      (((a : Int) * (i : Int) + (b : Int)) - ((a' : Int) * (i : Int) + (b' : Int))) -
      (((a : Int) * (j : Int) + (b : Int)) - ((a' : Int) * (j : Int) + (b' : Int))) =
      ((a : Int) - (a' : Int)) * ((i : Int) - (j : Int)) := by
    simp only [Int.sub_mul, Int.mul_sub]
    omega
  rw [hdet] at hd
  have hslope : a = a' := by
    rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hd with hs | hrows
    · have hsmall : ((a : Int) - (a' : Int)).natAbs < ((q : Nat) : Int).natAbs := by
        simpa using IntegerControlGrid.difference_natAbs_lt a a' q (by omega) (by omega)
      have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hs hsmall
      omega
    · have hsmall : ((i : Int) - (j : Int)).natAbs < ((q : Nat) : Int).natAbs := by
        simpa using IntegerControlGrid.difference_natAbs_lt i j q (by omega) (by omega)
      have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hrows hsmall
      omega
  subst a'
  have hbexpr :
      ((a : Int) * (i : Int) + (b : Int)) - ((a : Int) * (i : Int) + (b' : Int)) =
        (b : Int) - (b' : Int) := by omega
  rw [hbexpr] at hdi
  have hbsmall : ((b : Int) - (b' : Int)).natAbs < ((q : Nat) : Int).natAbs := by
    simpa using IntegerControlGrid.difference_natAbs_lt b b' q hb hb'
  have hbzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdi hbsmall
  exact ⟨rfl, by omega⟩

/-- Distinct blocks share at most one control (natural-number coordinates). -/
theorem intersection_at_most_one (q A r a a' b b' : Nat) (hq : q.Prime)
    (hAq : A ≤ q) (hrq : r ≤ q)
    (ha : a < A) (ha' : a' < A) (hb : b < q) (hb' : b' < q)
    (hdistinct : (a, b) ≠ (a', b')) (p p' : Nat × Nat)
    (hp : p.1 < r ∧ p.2 = column q a b p.1) (hpc : p.1 < r ∧ p.2 = column q a' b' p.1)
    (hp' : p'.1 < r ∧ p'.2 = column q a b p'.1) (hpc' : p'.1 < r ∧ p'.2 = column q a' b' p'.1) :
    p = p' := by
  have hci : column q a b p.1 = column q a' b' p.1 := hp.2.symm.trans hpc.2
  have hcj : column q a b p'.1 = column q a' b' p'.1 := hp'.2.symm.trans hpc'.2
  have hrow : p.1 = p'.1 := by
    by_contra hij
    obtain ⟨hs, hb⟩ := two_shared_rows q A r a a' b b' p.1 p'.1 hq hAq hrq ha ha' hb hb'
      hp.1 hp'.1 hij hci hcj
    exact hdistinct (Prod.ext hs hb)
  apply Prod.ext hrow
  rw [hp.2, hp'.2, hrow]

end CoefficientTwoPrecision.TD

#print axioms CoefficientTwoPrecision.TD.tdQ_le_two_max
#print axioms CoefficientTwoPrecision.TD.two_shared_rows
