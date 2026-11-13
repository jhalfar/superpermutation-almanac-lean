import AlmanacDefs
import Asym37.Main

/-!
# Links to the Superpermutation Almanac's definitions

This follows Jay Pantone's `AlmanacAdapter.lean` (github.com/jaypantone/2026-10-superpermutation-asymptotics,
branch almanac-submission, commit 882721e); `fact_eq` and `covers_iff` are his lemmas, unchanged. The batch
states one result, the explicit error bound with exponent 1/37 proved in `lean/Asym37` on top of his release.

`AlmanacSolution.lean` states the result with the Almanac's own definitions from `AlmanacDefs.lean`. This
module proves it from `CoefficientTwoPrecision.Asym37.explicit_error_37`, which is stated with the project's
covering predicate `SuperpermutationBounds.Covers` and `Nat.factorial`.
-/

namespace AlmanacAdapter

/-- The Almanac's factorial is `Nat.factorial`. -/
theorem fact_eq (k : Nat) : Almanac.fact k = Nat.factorial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Almanac.fact, Nat.factorial, ih]

/-- The project's covering predicate is the Almanac's superpermutation predicate. -/
theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    SuperpermutationBounds.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hp hl
    obtain ⟨u, v, huv⟩ := h p hl hp
    exact ⟨u, v, huv.symm⟩
  · intro h p hl hp
    obtain ⟨u, v, huv⟩ := h p hp hl
    exact ⟨u, v, huv.symm⟩

/-- For every `n ≥ 5920·352³·6³⁷` (about `1.6·10⁴⁰`), the shortest length `S(n)` of a
superpermutation on `n` symbols satisfies
`|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 306 (n-4)! n^(-1/37)`.
The first part gives a superpermutation no longer than the upper end; the
second says that no superpermutation is shorter than the lower end. -/
def ExplicitError37 : Prop :=
  ∀ n : Nat, 5920 * 352 ^ 3 * 6 ^ 37 ≤ n →
    (∃ w : Almanac.Word n, Almanac.IsSuperpermutation n w ∧
      (w.length : Real) ≤ (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) +
        306 * (Almanac.fact (n - 4) : Real) * (n : Real) ^ (-1 / 37 : Real)) ∧
    ∀ w : Almanac.Word n, Almanac.IsSuperpermutation n w →
      (Almanac.fact n : Real) + (Almanac.fact (n - 1) : Real) +
        (Almanac.fact (n - 2) : Real) + 2 * (Almanac.fact (n - 4) : Real) -
        306 * (Almanac.fact (n - 4) : Real) * (n : Real) ^ (-1 / 37 : Real) ≤
          (w.length : Real)

/-- The explicit two-sided error bound, from `CoefficientTwoPrecision.Asym37.explicit_error_37`. -/
theorem explicit_error_37 : ExplicitError37 := by
  intro n hn
  obtain ⟨⟨w, hw, hwl⟩, hlow⟩ := CoefficientTwoPrecision.Asym37.explicit_error_37 n hn
  simp only [fact_eq]
  exact ⟨⟨w, (covers_iff w).1 hw, hwl⟩, fun v hv => hlow v ((covers_iff v).2 hv)⟩

end AlmanacAdapter
