import K6.TE.T1F0
import K6.TE.T2F0
import K6.TE.T3F0

/-!
# All parts of the search of the tight case

`tightAll T`: for `T = 1, 2, 3` trails, the search answers `false` (one part each, `n0 = n1 = 1`).
Each search is cut into pieces by `tools/gen_te.py` (see `K6/Frontier.lean`); the files of the
pieces are in `K6/TE/`.
-/

namespace K6

theorem tightAll1 : ∀ p0, p0 < 1 → ∀ p1, p1 < 1 →
    part (famRules 1 2 1 p0 1 p1) 40 = false := by
  intro p0 h0 p1 h1
  obtain rfl : p0 = 0 := by omega
  obtain rfl : p1 = 0 := by omega
  exact TE.T1F0

theorem tightAll2 : ∀ p0, p0 < 1 → ∀ p1, p1 < 1 →
    part (famRules 2 2 1 p0 1 p1) 40 = false := by
  intro p0 h0 p1 h1
  obtain rfl : p0 = 0 := by omega
  obtain rfl : p1 = 0 := by omega
  exact TE.T2F0

theorem tightAll3 : ∀ p0, p0 < 1 → ∀ p1, p1 < 1 →
    part (famRules 3 2 1 p0 1 p1) 40 = false := by
  intro p0 h0 p1 h1
  obtain rfl : p0 = 0 := by omega
  obtain rfl : p1 = 0 := by omega
  exact TE.T3F0

end K6
