-- Superpermutation Almanac batch: the explicit error after 2(n-4)!, exponent 1/28 up to a logarithm.
-- Jay Pantone's construction and proof (github.com/jaypantone/2026-10-superpermutation-asymptotics, 9ccbe66),
-- with the transversal design of lean/Asym28, the envelope degree of lean/Asym29 and the counts of lean/Asym33
-- and lean/Asym35; see README.md.
import AlmanacDefs
import AlmanacAdapter

namespace AlmanacSubmission

/-- For every n ≥ 5920·8320³·6²⁸·4³,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 205 (n-4)! (log n)^(3/28) n^(-1/28). -/
theorem explicit_error_log28 : AlmanacAdapter.ExplicitErrorLog28 := AlmanacAdapter.explicit_error_log28

end AlmanacSubmission
