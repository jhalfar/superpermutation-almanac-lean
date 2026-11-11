-- Lower bounds from Theorem C (proofs/lean/lower of github.com/jhalfar/superpermutations) with re-tuned
-- constants; every finite search is evaluated by the kernel. The linking lemmas are in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 12 symbols has length at least 522,622,401. -/
theorem lower_twelve : Almanac.LowerBoundAt 12 522622401 := LowerLinks.lower_twelve

/-- Every superpermutation on 13 symbols has length at least 6,746,627,048. -/
theorem lower_thirteen : Almanac.LowerBoundAt 13 6746627048 := LowerLinks.lower_thirteen

end AlmanacSubmission
