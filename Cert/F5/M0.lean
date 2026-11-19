import Cert.F5.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert
namespace F5

theorem g13898 : OK n13898 [] = true := by decide +kernel

theorem g30095 : OK n30095 [] = true := by decide +kernel

theorem g46815 : OK n46815 [] = true := by decide +kernel

theorem x2230 : OK n2230 [n13898, n30095, n46815] = true := by decide +kernel

theorem top : (SN wsT 400 [n2230]).isSome = true := by decide +kernel

end F5
end Cert
end SuperpermLowerBounds
