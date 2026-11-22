-- Superpermutation Almanac batch: the explicit error after 2(n-4)!, exponent 1/20 up to a logarithm.
-- Jay Pantone's construction and proof (github.com/jaypantone/2026-10-superpermutation-asymptotics, 9ccbe66),
-- with the local positions and the transversal design of lean/Asym22, the envelope degree of lean/Asym29 and
-- the counts of lean/Asym33 and lean/Asym35; see README.md.
import AlmanacDefs
import AlmanacAdapter

namespace AlmanacSubmission

/-- For every n ≥ 2904·10400²·6²⁰·4²,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 214 (n-4)! (log n)^(1/10) n^(-1/20). -/
theorem explicit_error_log20 : AlmanacAdapter.ExplicitErrorLog20 := AlmanacAdapter.explicit_error_log20

end AlmanacSubmission
