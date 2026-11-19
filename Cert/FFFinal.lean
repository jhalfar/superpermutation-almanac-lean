import Cert.FRFinal
import LowerBounds.PRules
import Cert.FF0.Comb
import Cert.FF1.Comb
import Cert.FF2.Comb
import Cert.FF3.Comb
import Cert.FF4.Comb

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem prof0_kernel (hM : PS.WCap 7 (fun x => T5899.Mtab.getD x 0) 36) : PS.NoProfileK 7 [(66, 36), (66, 36)] :=
  PS.noProfileK_of_stmt hM (by decide) (by decide)
    (PS.pstmt_of_psearchC (penc wfacts pO_all) FF0.ok)

theorem prof1_kernel (hM : PS.WCap 7 (fun x => T5899.Mtab.getD x 0) 36) : PS.NoProfileK 7 [(50, 26), (50, 26)] :=
  PS.noProfileK_of_stmt hM (by decide) (by decide)
    (PS.pstmt_of_psearchC (penc wfacts pO_all) FF1.ok)

theorem prof2_kernel (hM : PS.WCap 7 (fun x => T5899.Mtab.getD x 0) 36) : PS.NoProfileK 7 [(63, 34), (34, 16)] :=
  PS.noProfileK_of_stmt hM (by decide) (by decide)
    (PS.pstmt_of_psearchC (penc wfacts pO_all) FF2.ok)

theorem prof3_kernel (hM : PS.WCap 7 (fun x => T5899.Mtab.getD x 0) 36) : PS.NoProfileK 7 [(66, 36), (31, 14)] :=
  PS.noProfileK_of_stmt hM (by decide) (by decide)
    (PS.pstmt_of_psearchC (penc wfacts pO_all) FF3.ok)

theorem prof4_kernel (hM : PS.WCap 7 (fun x => T5899.Mtab.getD x 0) 36) : PS.NoProfileK 7 [(31, 14), (31, 14), (34, 16), (34, 16)] :=
  PS.noProfileK_of_stmt hM (by decide) (by decide)
    (PS.pstmt_of_psearchC (penc wfacts pO_all) FF4.ok)


end Cert
end SuperpermLowerBounds
