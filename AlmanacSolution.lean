-- Superpermutation Almanac batch: the explicit error after 2(n-4)!, exponent 1/29 up to a logarithm.
-- Jay Pantone's construction and proof (github.com/jaypantone/2026-10-superpermutation-asymptotics, 9ccbe66),
-- with the envelope degree of lean/Asym29 and the counts of lean/Asym33, lean/Asym35 and lean/Asym37; see README.md.
import AlmanacDefs
import AlmanacAdapter

namespace AlmanacSubmission

/-- For every n ≥ 5920·4161³·6²⁹·4³,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 183 (n-4)! (log n)^(3/29) n^(-1/29). -/
theorem explicit_error_log29 : AlmanacAdapter.ExplicitErrorLog29 := AlmanacAdapter.explicit_error_log29

end AlmanacSubmission
