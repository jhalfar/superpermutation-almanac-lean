-- A lower bound for 6 symbols, from proofs/lean/small of github.com/jhalfar/superpermutations, checked by
-- the kernel alone (no native_decide). The linking lemma is in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 6 symbols has length at least 872. -/
theorem lower_six_kernel : Almanac.LowerBoundAt 6 872 := LowerLinks.lower_six

end AlmanacSubmission
