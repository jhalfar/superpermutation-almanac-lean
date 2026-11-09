-- A lower bound for 7 symbols, from proofs/lean/n7 of github.com/jhalfar/superpermutations (the proof of
-- 5,899) with its six sequence searches run by the search engine of proofs/lean/n7_5901 (reversal cut and
-- Rule JS); twelve searches are evaluated by native_decide. The linking lemma is in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 7 symbols has length at least 5,899. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5899 := LowerLinks.lower_seven

end AlmanacSubmission
