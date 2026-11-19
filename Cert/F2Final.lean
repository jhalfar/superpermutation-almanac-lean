import Cert.WCheck
import Cert.RSpec
import Cert.Cap
import Cert.F2.Comb
import Cert.RC.F2T0
import Cert.RC.F2T1
import Cert.RC.F2T2

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

/-- The records of F2 pass the check. -/
theorem hpF2 : ∀ t r d, t < 3 → r ≤ 132 → d < 73 → pR capT 2 0 72 10 16 30 F2.rl 3 132 73 t r d = true := by
  intro t r d ht hr hd
  interval_cases t
  · by_cases h0 : r < 8
    · exact grid_spec' rcF20_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF20_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF20_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF20_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF20_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF20_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF20_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF20_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF20_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF20_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF20_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF20_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF20_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF20_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF20_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF20_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF20_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF21_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF21_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF21_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF21_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF21_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF21_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF21_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF21_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF21_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF21_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF21_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF21_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF21_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF21_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF21_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF21_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF21_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF22_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF22_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF22_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF22_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF22_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF22_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF22_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF22_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF22_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF22_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF22_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF22_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF22_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF22_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF22_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF22_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF22_16 r (by omega) (by omega) d hd

/-- **F2: every sequence with 2 links of weight 4 and at most 72 holes has at most `P_2(x)` rows**, by the kernel. -/
theorem capF2 (hlow : ∀ j, j < 2 → PS.SeqCapLt 7 j (PS.capF T5899.Ptabs j) (72 + 1)) :
    PS.SeqCapLt 7 2 (PS.capF T5899.Ptabs 2) (72 + 1) := by
  rw [← capT_eq] at hlow ⊢
  exact seqCap_of_searchC (P := capT) (rl := F2.rl) (A := 3) (R := 132) (C := 73) wfacts rfl rfl
    (by decide) hpF2 hlow (seqCapLt_zero' _ _ _) F2.ok

end Cert
end SuperpermLowerBounds
