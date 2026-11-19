import Cert.AssembleN
import Cert.F5.M0

set_option maxRecDepth 100000
set_option linter.all false
set_option linter.unusedVariables false

namespace SuperpermLowerBounds
namespace Cert
namespace F5

/-- The whole search below a prefix does not find. -/
abbrev FC := FullC cd mk fN fS ct wrecT true

theorem hoff : ∀ t d, t < 6 → d < 55 → 16 * d + 2 * 30 * t + 30 ≤ offN := by
  intro t d ht hd
  simp only [offN]
  omega

theorem fx2230 : FC n2230 := fullS_of_cut_ok hoff x2230 (allC_cons (fullS_of_ok hoff g13898) (allC_cons (fullS_of_ok hoff g30095) (allC_cons (fullS_of_ok hoff g46815) (allC_nil _))))

/-- The whole search of F5 does not find. -/
theorem ok : searchC cd mk fN fS ct wrecT true wsT 400 [] ≠ none :=
  searchN_ok hoff top (allC_cons (fx2230) (allC_nil _))

end F5
end Cert
end SuperpermLowerBounds
