-- A lower bound for 7 symbols: the proof of 5,900 of proofs/lean/n7_5900 of github.com/jhalfar/superpermutations,
-- on top of the proof of 5,899 of the earlier batch (its six sequence searches run by the search engine of
-- proofs/lean/n7_5901); 89 searches are evaluated by native_decide. The linking lemma is in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 7 symbols has length at least 5,900. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5900 := LowerLinks.lower_seven

end AlmanacSubmission
