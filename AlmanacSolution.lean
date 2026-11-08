-- Two upper bounds for the shortest superpermutation for large n, from the development
-- proofs/lean/constant43586371 of github.com/jhalfar/superpermutations (Pantone's construction
-- with nested block levels). The linking lemmas are in UpperLinks.lean.
import AlmanacDefs
import UpperLinks

namespace AlmanacSubmission

/-- The coefficient of (n-3)! tends to 0: for every ε > 0, for all large n, some superpermutation on
n symbols has length at most n! + (n-1)! + (n-2)! + ε (n-3)!. -/
theorem upper_coeff3_zero : Almanac.AsymptoticUpperAt 3 0 := UpperLinks.upper_coeff3_zero

/-- For every ε > 0, for all large n, some superpermutation on n symbols has length at most
n! + (n-1)! + (n-2)! + (8 + ε) (n-4)!. -/
theorem upper_coeff4 : Almanac.AsymptoticUpperAt 4 8 := UpperLinks.upper_coeff4_eight

end AlmanacSubmission
