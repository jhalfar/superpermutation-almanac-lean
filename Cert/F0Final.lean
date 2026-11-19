import Cert.WCheck
import Cert.RSpec
import Cert.Cap
import Cert.F0.Comb
import Cert.RC.F0T0

set_option maxHeartbeats 0

namespace SuperpermLowerBounds
namespace Cert

/-- The records of F0 pass the check. -/
theorem hpF0 : ∀ t r d, t < 1 → r ≤ 134 → d < 85 → pR capT 0 0 84 20 31 5 F0.rl 1 134 85 t r d = true := by
  intro t r d ht hr hd
  interval_cases t
  · by_cases h0 : r < 8
    · exact grid_spec' rcF00_0 r (by omega) (by omega) d hd
    by_cases h1 : r < 16
    · exact grid_spec' rcF00_1 r (by omega) (by omega) d hd
    by_cases h2 : r < 24
    · exact grid_spec' rcF00_2 r (by omega) (by omega) d hd
    by_cases h3 : r < 32
    · exact grid_spec' rcF00_3 r (by omega) (by omega) d hd
    by_cases h4 : r < 40
    · exact grid_spec' rcF00_4 r (by omega) (by omega) d hd
    by_cases h5 : r < 48
    · exact grid_spec' rcF00_5 r (by omega) (by omega) d hd
    by_cases h6 : r < 56
    · exact grid_spec' rcF00_6 r (by omega) (by omega) d hd
    by_cases h7 : r < 64
    · exact grid_spec' rcF00_7 r (by omega) (by omega) d hd
    by_cases h8 : r < 72
    · exact grid_spec' rcF00_8 r (by omega) (by omega) d hd
    by_cases h9 : r < 80
    · exact grid_spec' rcF00_9 r (by omega) (by omega) d hd
    by_cases h10 : r < 88
    · exact grid_spec' rcF00_10 r (by omega) (by omega) d hd
    by_cases h11 : r < 96
    · exact grid_spec' rcF00_11 r (by omega) (by omega) d hd
    by_cases h12 : r < 104
    · exact grid_spec' rcF00_12 r (by omega) (by omega) d hd
    by_cases h13 : r < 112
    · exact grid_spec' rcF00_13 r (by omega) (by omega) d hd
    by_cases h14 : r < 120
    · exact grid_spec' rcF00_14 r (by omega) (by omega) d hd
    by_cases h15 : r < 128
    · exact grid_spec' rcF00_15 r (by omega) (by omega) d hd
    exact grid_spec' rcF00_16 r (by omega) (by omega) d hd

/-- **F0: every sequence with 0 links of weight 4 and at most 84 holes has at most `P_0(x)` rows**, by the kernel. -/
theorem capF0 (hlow : ∀ j, j < 0 → PS.SeqCapLt 7 j (PS.capF T5899.Ptabs j) (84 + 1)) :
    PS.SeqCapLt 7 0 (PS.capF T5899.Ptabs 0) (84 + 1) := by
  rw [← capT_eq] at hlow ⊢
  exact seqCap_of_searchC (P := capT) (rl := F0.rl) (A := 1) (R := 134) (C := 85) wfacts rfl rfl
    (by decide) hpF0 hlow (seqCapLt_zero' _ _ _) F0.ok

end Cert
end SuperpermLowerBounds
