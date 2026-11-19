import Cert.WDefs
import Cert.RDefs
import Cert.Cap0

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem pw19 : allIdx pW 4788 252 = true := by decide +kernel

end Cert
end SuperpermLowerBounds
