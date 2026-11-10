-- A lower bound for 7 symbols, checked by the kernel: the coarse part of the accounting of the proof of 5,899
-- (proofs/lean/n7 of github.com/jhalfar/superpermutations) at cost 133, with the chain caps up to 78 holes and the
-- five profile statements evaluated by the kernel (K7). The linking lemma is in LowerLinks.lean.
import AlmanacDefs
import LowerLinks

namespace AlmanacSubmission

/-- Every superpermutation on 7 symbols has length at least 5,898. -/
theorem lower_seven : Almanac.LowerBoundAt 7 5898 := LowerLinks.lower_seven

end AlmanacSubmission
