import Cert.RingSpec
import Cert.WCheck
import Cert.FR.Comb
import Cert.WOC.P0
import Cert.WOC.P1
import Cert.WOC.P2
import Cert.WOC.P3
import Cert.WOC.P4
import Cert.WOC.P5
import Cert.WOC.P6
import Cert.WOC.P7
import Cert.WOC.P8
import Cert.WOC.P9
import Cert.WOC.P10
import Cert.WOC.P11
import Cert.WOC.P12
import Cert.WOC.P13
import Cert.WOC.P14
import Cert.WOC.P15
import Cert.WOC.P16
import Cert.WOC.P17
import Cert.WOC.P18
import Cert.WOC.P19
import Cert.RingC.P0
import Cert.RingC.P1
import Cert.RingC.P2
import Cert.RingC.P3
import Cert.RingC.P4
import Cert.RingC.P5
import Cert.RingC.P6
import Cert.RingC.P7
import Cert.RingC.P8
import Cert.RingC.P9
import Cert.RingC.P10
import Cert.RingC.P11
import Cert.RingC.P12
import Cert.RingC.P13
import Cert.RingC.P14

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem pO_all : ∀ i, i < 5040 → pO i = true := by
  intro i hi
  by_cases h0 : i < 252
  · exact allIdx_spec 252 po0 i (by omega) (by omega)
  by_cases h1 : i < 504
  · exact allIdx_spec 252 po1 i (by omega) (by omega)
  by_cases h2 : i < 756
  · exact allIdx_spec 252 po2 i (by omega) (by omega)
  by_cases h3 : i < 1008
  · exact allIdx_spec 252 po3 i (by omega) (by omega)
  by_cases h4 : i < 1260
  · exact allIdx_spec 252 po4 i (by omega) (by omega)
  by_cases h5 : i < 1512
  · exact allIdx_spec 252 po5 i (by omega) (by omega)
  by_cases h6 : i < 1764
  · exact allIdx_spec 252 po6 i (by omega) (by omega)
  by_cases h7 : i < 2016
  · exact allIdx_spec 252 po7 i (by omega) (by omega)
  by_cases h8 : i < 2268
  · exact allIdx_spec 252 po8 i (by omega) (by omega)
  by_cases h9 : i < 2520
  · exact allIdx_spec 252 po9 i (by omega) (by omega)
  by_cases h10 : i < 2772
  · exact allIdx_spec 252 po10 i (by omega) (by omega)
  by_cases h11 : i < 3024
  · exact allIdx_spec 252 po11 i (by omega) (by omega)
  by_cases h12 : i < 3276
  · exact allIdx_spec 252 po12 i (by omega) (by omega)
  by_cases h13 : i < 3528
  · exact allIdx_spec 252 po13 i (by omega) (by omega)
  by_cases h14 : i < 3780
  · exact allIdx_spec 252 po14 i (by omega) (by omega)
  by_cases h15 : i < 4032
  · exact allIdx_spec 252 po15 i (by omega) (by omega)
  by_cases h16 : i < 4284
  · exact allIdx_spec 252 po16 i (by omega) (by omega)
  by_cases h17 : i < 4536
  · exact allIdx_spec 252 po17 i (by omega) (by omega)
  by_cases h18 : i < 4788
  · exact allIdx_spec 252 po18 i (by omega) (by omega)
  exact allIdx_spec 252 po19 i (by omega) (by omega)

theorem ringChk_all : ∀ r d, r < 135 → d ≤ 77 → ringChk r d = true := by
  intro r d hr hd
  by_cases h0 : r < 9
  · exact allIdx_spec 78 (allIdx_spec 9 rgc0 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h1 : r < 18
  · exact allIdx_spec 78 (allIdx_spec 9 rgc1 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h2 : r < 27
  · exact allIdx_spec 78 (allIdx_spec 9 rgc2 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h3 : r < 36
  · exact allIdx_spec 78 (allIdx_spec 9 rgc3 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h4 : r < 45
  · exact allIdx_spec 78 (allIdx_spec 9 rgc4 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h5 : r < 54
  · exact allIdx_spec 78 (allIdx_spec 9 rgc5 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h6 : r < 63
  · exact allIdx_spec 78 (allIdx_spec 9 rgc6 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h7 : r < 72
  · exact allIdx_spec 78 (allIdx_spec 9 rgc7 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h8 : r < 81
  · exact allIdx_spec 78 (allIdx_spec 9 rgc8 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h9 : r < 90
  · exact allIdx_spec 78 (allIdx_spec 9 rgc9 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h10 : r < 99
  · exact allIdx_spec 78 (allIdx_spec 9 rgc10 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h11 : r < 108
  · exact allIdx_spec 78 (allIdx_spec 9 rgc11 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h12 : r < 117
  · exact allIdx_spec 78 (allIdx_spec 9 rgc12 r (by omega) (by omega)) d (by omega) (by omega)
  by_cases h13 : r < 126
  · exact allIdx_spec 78 (allIdx_spec 9 rgc13 r (by omega) (by omega)) d (by omega) (by omega)
  exact allIdx_spec 78 (allIdx_spec 9 rgc14 r (by omega) (by omega)) d (by omega) (by omega)

/-- **FR: the ring cap**, by the kernel. -/
theorem ringCap_kernel (hM : PS.SeqCapLt 7 0 (fun x => T5899.Mtab.getD x 0) (77 + 1)) :
    PS.RingCapT 7 (fun x => T5899.PRtab.getD x 0) 77 :=
  ringCapT_of_psearchC wfacts pO_all ringChk_all hM FR.ok

end Cert
end SuperpermLowerBounds
