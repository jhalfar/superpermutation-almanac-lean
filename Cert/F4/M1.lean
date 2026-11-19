import Cert.F4.S0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert
namespace F4

theorem x652625 : OK n652625 [n663891] = true := by decide +kernel

theorem x663891 : OK n663891 [n676308] = true := by decide +kernel

theorem x709109 : OK n709109 [n709781, n734142, n797260] = true := by decide +kernel

theorem x734142 : OK n734142 [n745959] = true := by decide +kernel

theorem x745959 : OK n745959 [n753994] = true := by decide +kernel

theorem x753994 : OK n753994 [n761957] = true := by decide +kernel

theorem x831534 : OK n831534 [n831983, n877250, n899575] = true := by decide +kernel

theorem x831983 : OK n831983 [n847904] = true := by decide +kernel

theorem x899575 : OK n899575 [n907686] = true := by decide +kernel

theorem x907686 : OK n907686 [n924322] = true := by decide +kernel

theorem x924322 : OK n924322 [n936400] = true := by decide +kernel

theorem x936400 : OK n936400 [n937767, n956075] = true := by decide +kernel

theorem x956075 : OK n956075 [n969053] = true := by decide +kernel

theorem x969053 : OK n969053 [n986260] = true := by decide +kernel

theorem x986260 : OK n986260 [n994921] = true := by decide +kernel

theorem x994921 : OK n994921 [n1003295] = true := by decide +kernel

theorem top : (SN wsT 400 [n13671, n37240]).isSome = true := by decide +kernel

end F4
end Cert
end SuperpermLowerBounds
