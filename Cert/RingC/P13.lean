import Cert.RingT

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem rgc13 : allIdx (fun r => allIdx (fun d => ringChk r d) 0 78) 117 9 = true := by decide +kernel

end Cert
end SuperpermLowerBounds
