import Cert.RingT

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem rgc2 : allIdx (fun r => allIdx (fun d => ringChk r d) 0 78) 18 9 = true := by decide +kernel

end Cert
end SuperpermLowerBounds
