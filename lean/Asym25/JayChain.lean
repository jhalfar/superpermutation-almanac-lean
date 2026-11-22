import Precision
import Quantitative.MainTheorems
import Quantitative.StatementAudit

/-!
# Jay Pantone's own final chain is part of the build

`Precision`, `Quantitative.MainTheorems` and `Quantitative.StatementAudit`
(with `SourceSelection`, `SparseFamilyConstruction`, `GlobalSourceFamily` and
`CandidateRowState`, which they import) are the end of his proof on his
control grid. The statement of this batch does not use them. This module
imports them from the batch's import closure, so that a build of
`AlmanacSolution` also checks that his chain compiles in this tree.
-/
