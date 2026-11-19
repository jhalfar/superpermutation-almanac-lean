import Cert.F2.S1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert
namespace F2

theorem x345563142 : OK n345563142 [n345571544] = true := by decide +kernel

theorem x345571544 : OK n345571544 [n345577678] = true := by decide +kernel

theorem x345577678 : OK n345577678 [n345589454, n345661984] = true := by decide +kernel

theorem x345589454 : OK n345589454 [n345602401, n345623691] = true := by decide +kernel

theorem x345623691 : OK n345623691 [n345628147] = true := by decide +kernel

theorem x345689849 : OK n345689849 [n345701491] = true := by decide +kernel

theorem top : (SN wsT 400 [n4, n13496082, n13525562, n13566157, n13797478, n15081686, n345161951]).isSome = true := by decide +kernel

end F2
end Cert
end SuperpermLowerBounds
