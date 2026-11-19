import Cert.F0Final
import Cert.F1Final
import Cert.F2Final
import Cert.F3Final
import Cert.F4Final
import Cert.F5Final
import Cert.FFFinal
import LowerBounds.PTheorem
import LowerBounds.PFinal

/-! 5,899 for 7 symbols with every search checked by the kernel (no native_decide). -/

namespace SuperpermLowerBounds

open T5899

theorem seqCaps_kernel :
    PS.SeqCapLt 7 0 (PS.capF Ptabs 0) 85 ∧ PS.SeqCapLt 7 1 (PS.capF Ptabs 1) 79 ∧
      PS.SeqCapLt 7 2 (PS.capF Ptabs 2) 73 ∧ PS.SeqCapLt 7 3 (PS.capF Ptabs 3) 67 ∧
      PS.SeqCapLt 7 4 (PS.capF Ptabs 4) 61 ∧ PS.SeqCapLt 7 5 (PS.capF Ptabs 5) 55 := by
  have c0 := Cert.capF0 (fun j hj => absurd hj (Nat.not_lt_zero j))
  have c1 := Cert.capF1 (fun j hj => by interval_cases j; exact c0.mono (by norm_num))
  have c2 := Cert.capF2 (fun j hj => by
    interval_cases j
    · exact c0.mono (by norm_num)
    · exact c1.mono (by norm_num))
  have c3 := Cert.capF3 (fun j hj => by
    interval_cases j
    · exact c0.mono (by norm_num)
    · exact c1.mono (by norm_num)
    · exact c2.mono (by norm_num))
  have c4 := Cert.capF4 (fun j hj => by
    interval_cases j
    · exact c0.mono (by norm_num)
    · exact c1.mono (by norm_num)
    · exact c2.mono (by norm_num)
    · exact c3.mono (by norm_num))
  have c5 := Cert.capF5 (fun j hj => by
    interval_cases j
    · exact c0.mono (by norm_num)
    · exact c1.mono (by norm_num)
    · exact c2.mono (by norm_num)
    · exact c3.mono (by norm_num)
    · exact c4.mono (by norm_num))
  exact ⟨c0, c1, c2, c3, c4, c5⟩

theorem caps_kernel : Caps := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := seqCaps_kernel
  refine ⟨?_, ?_, ?_⟩
  · exact PS.chainCapK_of_wcap (PS.wcap_of_seqCap c0)
  · intro s hs1 hs5
    interval_cases s
    · exact PS.pathCapK_of_seqCap c1
    · exact PS.pathCapK_of_seqCap c2
    · exact PS.pathCapK_of_seqCap c3
    · exact PS.pathCapK_of_seqCap c4
    · exact PS.pathCapK_of_seqCap c5
  · have hM : PS.SeqCapLt 7 0 (fun x => Mtab.getD x 0) (77 + 1) := by
      rw [← capF_zero]
      exact c0.mono (by norm_num)
    exact PS.ringCapK_of_ringCapT (Cert.ringCap_kernel hM)

theorem profiles_kernel : Profiles := by
  have c0 := seqCaps_kernel.1
  have hM : PS.WCap 7 (fun x => Mtab.getD x 0) 36 := by
    rw [← capF_zero]
    exact PS.wcap_of_seqCap (c0.mono (by norm_num))
  exact ⟨Cert.prof0_kernel hM, Cert.prof1_kernel hM, Cert.prof2_kernel hM, Cert.prof3_kernel hM,
    Cert.prof4_kernel hM⟩

/-- **Every word over `Fin 7` that contains all permutations has at least 5,899 letters**, with every finite
search evaluated by the Lean kernel. -/
theorem covers_lower_bound_7_kernel :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length :=
  covers_5899_of_caps caps_kernel profiles_kernel

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_lower_bound_7_kernel
