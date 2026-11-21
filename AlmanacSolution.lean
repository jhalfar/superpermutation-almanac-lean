-- Superpermutation Almanac batch: the explicit error after 2(n-4)!, exponent 1/32 up to a logarithm.
-- Jay Pantone's construction and proof (github.com/jaypantone/2026-10-superpermutation-asymptotics, 9ccbe66),
-- with the collision count of lean/Asym37 and the pending bound of lean/Asym35 and the type-pair count of lean/Asym33; see README.md.
import AlmanacDefs
import AlmanacAdapter

namespace AlmanacSubmission

/-- For every n ≥ 5920·1405³·6³²·4³,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 148 (n-4)! (log n)^(3/32) n^(-1/32). -/
theorem explicit_error_log32 : AlmanacAdapter.ExplicitErrorLog32 := AlmanacAdapter.explicit_error_log32

end AlmanacSubmission
