import Cert.WSpec
import Cert.WC.Misc
import Cert.WC.P0
import Cert.WC.P1
import Cert.WC.P2
import Cert.WC.P3
import Cert.WC.P4
import Cert.WC.P5
import Cert.WC.P6
import Cert.WC.P7
import Cert.WC.P8
import Cert.WC.P9
import Cert.WC.P10
import Cert.WC.P11
import Cert.WC.P12
import Cert.WC.P13
import Cert.WC.P14
import Cert.WC.P15
import Cert.WC.P16
import Cert.WC.P17
import Cert.WC.P18
import Cert.WC.P19

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

theorem wst : PS.encB 7 (List.range' 1 7) = 0 := by decide +kernel

theorem wpw : ∀ i, i < 5040 → pW i = true := by
  intro i hi
  by_cases h0 : i < 252
  · exact allIdx_spec 252 pw0 i (by omega) (by omega)
  by_cases h1 : i < 504
  · exact allIdx_spec 252 pw1 i (by omega) (by omega)
  by_cases h2 : i < 756
  · exact allIdx_spec 252 pw2 i (by omega) (by omega)
  by_cases h3 : i < 1008
  · exact allIdx_spec 252 pw3 i (by omega) (by omega)
  by_cases h4 : i < 1260
  · exact allIdx_spec 252 pw4 i (by omega) (by omega)
  by_cases h5 : i < 1512
  · exact allIdx_spec 252 pw5 i (by omega) (by omega)
  by_cases h6 : i < 1764
  · exact allIdx_spec 252 pw6 i (by omega) (by omega)
  by_cases h7 : i < 2016
  · exact allIdx_spec 252 pw7 i (by omega) (by omega)
  by_cases h8 : i < 2268
  · exact allIdx_spec 252 pw8 i (by omega) (by omega)
  by_cases h9 : i < 2520
  · exact allIdx_spec 252 pw9 i (by omega) (by omega)
  by_cases h10 : i < 2772
  · exact allIdx_spec 252 pw10 i (by omega) (by omega)
  by_cases h11 : i < 3024
  · exact allIdx_spec 252 pw11 i (by omega) (by omega)
  by_cases h12 : i < 3276
  · exact allIdx_spec 252 pw12 i (by omega) (by omega)
  by_cases h13 : i < 3528
  · exact allIdx_spec 252 pw13 i (by omega) (by omega)
  by_cases h14 : i < 3780
  · exact allIdx_spec 252 pw14 i (by omega) (by omega)
  by_cases h15 : i < 4032
  · exact allIdx_spec 252 pw15 i (by omega) (by omega)
  by_cases h16 : i < 4284
  · exact allIdx_spec 252 pw16 i (by omega) (by omega)
  by_cases h17 : i < 4536
  · exact allIdx_spec 252 pw17 i (by omega) (by omega)
  by_cases h18 : i < 4788
  · exact allIdx_spec 252 pw18 i (by omega) (by omega)
  exact allIdx_spec 252 pw19 i (by omega) (by omega)

/-- **The word tables satisfy `CEnc`.** -/
theorem wfacts : WFacts := ⟨wpw, wcodes, winc, wlen, wst, wws⟩

end Cert
end SuperpermLowerBounds
