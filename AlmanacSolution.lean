-- Superpermutation Almanac batch: the explicit error after 2(n-4)!, exponent 1/37.
-- Jay Pantone's construction and proof (github.com/jaypantone/2026-10-superpermutation-asymptotics, 9ccbe66),
-- with a new count of the collision deletions in lean/Asym37; see README.md.
import AlmanacDefs
import AlmanacAdapter

namespace AlmanacSubmission

/-- For every n ≥ 5920·352³·6³⁷,
|S(n) - (n! + (n-1)! + (n-2)! + 2(n-4)!)| ≤ 306 (n-4)! n^(-1/37). -/
theorem explicit_error_37 : AlmanacAdapter.ExplicitError37 := AlmanacAdapter.explicit_error_37

end AlmanacSubmission
