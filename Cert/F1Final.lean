import Cert.WCheck
import Cert.RSpec
import Cert.Cap
import Cert.F1.Comb
import Cert.RC.F1T0
import Cert.RC.F1T1

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

/-- The records of F1 pass the check. -/
theorem hpF1 : ∀ t r d, t < 2 → r ≤ 133 → d < 79 → pR capT 1 0 78 10 16 30 F1.rl 2 133 79 t r d = true := by
  intro t r d ht hr hd
  interval_cases t
  · by_cases h0 : r < 8
    · exact grid_spec' rcF10_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF10_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF10_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF10_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF10_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF10_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF10_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF10_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF10_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF10_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF10_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF10_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF10_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF10_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF10_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF10_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF10_16 r (by omega) (by omega) d hd
  · by_cases h0 : r < 8
    · exact grid_spec' rcF11_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF11_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF11_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF11_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF11_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF11_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF11_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF11_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF11_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF11_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF11_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF11_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF11_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF11_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF11_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF11_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF11_16 r (by omega) (by omega) d hd

/-- **F1: every sequence with 1 links of weight 4 and at most 78 holes has at most `P_1(x)` rows**, by the kernel. -/
theorem capF1 (hlow : ∀ j, j < 1 → PS.SeqCapLt 7 j (PS.capF T5899.Ptabs j) (78 + 1)) :
    PS.SeqCapLt 7 1 (PS.capF T5899.Ptabs 1) (78 + 1) := by
  rw [← capT_eq] at hlow ⊢
  exact seqCap_of_searchC (P := capT) (rl := F1.rl) (A := 2) (R := 133) (C := 79) wfacts rfl rfl
    (by decide) hpF1 hlow (seqCapLt_zero' _ _ _) F1.ok

end Cert
end SuperpermLowerBounds
