import AlmanacDefs
import SuperpermutationUpperBound43586371.Uniform.Main
import SuperpermutationUpperBound43586371.UniR.RRate8

/-!
# Linking lemmas: the Almanac templates from the theorems of `SuperpermutationUpperBound43586371`

The development states its bounds with Pantone's `SuperpermutationBounds.Covers` and
`SuperpermutationBounds.F3` (`Challenge.lean` of github.com/jaypantone/superperm-upper-43-80) and Mathlib's
`Nat.factorial`. A word is a `List (Fin n)` in both vocabularies and its length is `List.length` in both.
This file proves that the two notions of superpermutation agree (`covers_iff_isSuperpermutation`), that
the Almanac's factorial is `Nat.factorial` (`fact_eq_factorial`), and that the Almanac's
`asymptoticFormAt k n c` is `F3 n + c (n-k)!` (`asymptoticFormAt_eq`), and then proves the templates:

* `upper_coeff3_zero : Almanac.AsymptoticUpperAt 3 0`, from `Uniform.coefficient_tends_to_zero`;
* `upper_coeff4 : Almanac.AsymptoticUpperAt 4 (41/5)`, from `UniR.rate_R8` (the bound for `n ≥ 2^14`);
* `upper_coeff4_eight : Almanac.AsymptoticUpperAt 4 8`, from `UniR.rate_R8_eventually`.
-/

namespace UpperLinks

/-- The Almanac's factorial is Mathlib's `Nat.factorial`. -/
theorem fact_eq_factorial (k : Nat) : Almanac.fact k = Nat.factorial k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.factorial_succ, ← ih]; rfl

/-- Pantone's `Covers` is the Almanac's `IsSuperpermutation`. -/
theorem covers_iff_isSuperpermutation {n : Nat} (w : List (Fin n)) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    show ∃ s t, s ++ p ++ t = w
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ : ∃ s t, s ++ p ++ t = w := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

/-- The Almanac's form at the scale `(n-k)!`, in the vocabulary of the development. -/
theorem asymptoticFormAt_eq (k n : Nat) (c : Rat) :
    Almanac.asymptoticFormAt k n c =
      SuperpermutationBounds.F3 n + c * ((Nat.factorial (n - k) : Nat) : Rat) := by
  simp only [Almanac.asymptoticFormAt, SuperpermutationBounds.F3, fact_eq_factorial]

/-- **The coefficient of `(n-3)!` tends to `0`**, as the Almanac template. -/
theorem upper_coeff3_zero : Almanac.AsymptoticUpperAt 3 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := SuperpermutationUpperBound43586371.Uniform.coefficient_tends_to_zero ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨w, hw, hl⟩ := hN n hn
  refine ⟨w, (covers_iff_isSuperpermutation w).mp hw, ?_⟩
  rw [asymptoticFormAt_eq, zero_add]
  exact hl

/-- **The coefficient of `(n-4)!` is at most `41/5`**, as the Almanac template: from `n = 2^14` on,
`UniR.rate_R8` gives a word of length at most `F3 n + (41/5) (n-4)!`, so for every `ε > 0` one with
length at most `F3 n + (41/5 + ε) (n-4)!`. -/
theorem upper_coeff4 : Almanac.AsymptoticUpperAt 4 (41/5) := by
  intro ε hε
  refine ⟨2 ^ 14, fun n hn => ?_⟩
  obtain ⟨w, hw, hl⟩ := SuperpermutationUpperBound43586371.UniR.rate_R8 n hn
  refine ⟨w, (covers_iff_isSuperpermutation w).mp hw, ?_⟩
  rw [asymptoticFormAt_eq]
  have hF : (0 : Rat) ≤ ((Nat.factorial (n - 4) : Nat) : Rat) := by positivity
  have hle : (41 / 5 : Rat) * ((Nat.factorial (n - 4) : Nat) : Rat) ≤
      (41 / 5 + ε) * ((Nat.factorial (n - 4) : Nat) : Rat) :=
    mul_le_mul_of_nonneg_right (by linarith) hF
  linarith

/-- **The coefficient of `(n-4)!` is at most `8`**, as the Almanac template, from
`UniR.rate_R8_eventually`. -/
theorem upper_coeff4_eight : Almanac.AsymptoticUpperAt 4 8 := by
  intro ε hε
  obtain ⟨N, hN⟩ := SuperpermutationUpperBound43586371.UniR.rate_R8_eventually ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨w, hw, hl⟩ := hN n hn
  refine ⟨w, (covers_iff_isSuperpermutation w).mp hw, ?_⟩
  rw [asymptoticFormAt_eq]
  exact hl

end UpperLinks
