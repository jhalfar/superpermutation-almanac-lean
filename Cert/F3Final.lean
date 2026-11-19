import Cert.WCheck
import Cert.RSpec
import Cert.Cap
import Cert.F3.Comb
import Cert.RC.F3T0
import Cert.RC.F3T1
import Cert.RC.F3T2
import Cert.RC.F3T3

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

/-- The records of F3 pass the check. -/
theorem hpF3 : ∀ t r d, t < 4 → r ≤ 131 → d < 67 → pR capT 3 0 66 10 16 30 F3.rl 4 131 67 t r d = true := by
  intro t r d ht hr hd
  interval_cases t
  · by_cases h0 : r < 8
    · exact grid_spec' rcF30_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF30_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF30_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF30_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF30_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF30_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF30_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF30_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF30_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF30_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF30_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF30_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF30_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF30_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF30_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF30_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF30_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF31_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF31_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF31_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF31_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF31_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF31_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF31_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF31_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF31_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF31_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF31_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF31_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF31_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF31_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF31_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF31_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF31_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF32_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF32_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF32_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF32_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF32_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF32_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF32_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF32_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF32_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF32_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF32_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF32_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF32_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF32_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF32_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF32_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF32_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF33_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF33_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF33_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF33_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF33_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF33_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF33_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF33_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF33_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF33_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF33_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF33_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF33_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF33_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF33_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF33_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF33_16 r (by omega) (by omega) d hd

/-- **F3: every sequence with 3 links of weight 4 and at most 66 holes has at most `P_3(x)` rows**, by the kernel. -/
theorem capF3 (hlow : ∀ j, j < 3 → PS.SeqCapLt 7 j (PS.capF T5899.Ptabs j) (66 + 1)) :
    PS.SeqCapLt 7 3 (PS.capF T5899.Ptabs 3) (66 + 1) := by
  rw [← capT_eq] at hlow ⊢
  exact seqCap_of_searchC (P := capT) (rl := F3.rl) (A := 4) (R := 131) (C := 67) wfacts rfl rfl
    (by decide) hpF3 hlow (seqCapLt_zero' _ _ _) F3.ok

end Cert
end SuperpermLowerBounds
