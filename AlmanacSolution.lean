-- A lower bound for 8 symbols, from proofs/lean/n8_46134 of github.com/jhalfar/superpermutations
-- (Theorem D with three finite searches evaluated by native_decide). The linking lemma is in
-- LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 8 symbols has length at least 46,134. -/
theorem lower_eight : Almanac.LowerBoundAt 8 46134 := LowerLinks.lower_eight

end AlmanacSubmission
