import Cert.WCheck
import Cert.RSpec
import Cert.Cap
import Cert.F5.Comb
import Cert.RC.F5T0
import Cert.RC.F5T1
import Cert.RC.F5T2
import Cert.RC.F5T3
import Cert.RC.F5T4
import Cert.RC.F5T5

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

/-- The records of F5 pass the check. -/
theorem hpF5 : ∀ t r d, t < 6 → r ≤ 129 → d < 55 → pR capT 5 0 54 10 16 30 F5.rl 6 129 55 t r d = true := by
  intro t r d ht hr hd
  interval_cases t
  · by_cases h0 : r < 8
    · exact grid_spec' rcF50_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF50_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF50_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF50_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF50_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF50_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF50_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF50_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF50_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF50_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF50_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF50_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF50_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF50_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF50_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF50_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF50_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF51_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF51_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF51_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF51_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF51_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF51_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF51_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF51_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF51_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF51_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF51_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF51_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF51_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF51_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF51_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF51_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF51_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF52_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF52_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF52_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF52_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF52_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF52_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF52_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF52_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF52_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF52_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF52_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF52_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF52_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF52_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF52_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF52_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF52_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF53_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF53_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF53_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF53_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF53_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF53_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF53_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF53_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF53_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF53_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF53_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF53_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF53_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF53_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF53_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF53_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF53_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF54_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF54_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF54_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF54_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF54_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF54_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF54_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF54_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF54_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF54_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF54_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF54_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF54_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF54_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF54_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF54_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF54_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF55_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF55_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF55_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF55_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF55_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF55_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF55_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF55_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF55_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF55_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF55_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF55_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF55_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF55_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF55_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF55_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF55_16 r (by omega) (by omega) d hd

/-- **F5: every sequence with 5 links of weight 4 and at most 54 holes has at most `P_5(x)` rows**, by the kernel. -/
theorem capF5 (hlow : ∀ j, j < 5 → PS.SeqCapLt 7 j (PS.capF T5899.Ptabs j) (54 + 1)) :
    PS.SeqCapLt 7 5 (PS.capF T5899.Ptabs 5) (54 + 1) := by
  rw [← capT_eq] at hlow ⊢
  exact seqCap_of_searchC (P := capT) (rl := F5.rl) (A := 6) (R := 129) (C := 55) wfacts rfl rfl
    (by decide) hpF5 hlow (seqCapLt_zero' _ _ _) F5.ok

end Cert
end SuperpermLowerBounds
