import Cert.WDefs
import Cert.RDefs
import Cert.Cap0

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem wcodes : chkCodes (PS.permCodes 7 7) 0 = true := by decide +kernel

theorem winc : incB 0 (PS.permCodes 7 7) = true := by decide +kernel

theorem wlen : (PS.permCodes 7 7).length = 5040 := by decide +kernel

theorem wws : orbB 6 0 wsT = true := by decide +kernel

end Cert
end SuperpermLowerBounds
