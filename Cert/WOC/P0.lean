import Cert.RingT

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem po0 : allIdx pO 0 252 = true := by decide +kernel

end Cert
end SuperpermLowerBounds
