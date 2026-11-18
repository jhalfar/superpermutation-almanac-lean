import LowerBounds.F5900K16
import LowerBounds.KFinalNative
import LowerBounds.J15FinalNative
import LowerBounds.PFinalK16Native

/-!
# 5,900 for 7 symbols, with the searches evaluated as compiled code

**Trusted here.**  The theorem of this file depends on the axioms recorded by `native_decide` for 89
equations:

* the twelve equations of the proof of 5,899 (`PK16F0Native.lean`, `PK16F1Native.lean`, `PK16Native.lean`,
  `PRingNative.lean`, `PProfNative.lean`; see `PFinalK16Native.lean`);
* the 41 equations for table T' and Theorem K in the 36 files `KK*Native.lean` and `KSmallNative.lean`
  (joined in `KFinalNative.lean`);
* the 36 equations for the joint statements in the 36 files `J15*Native.lean` (joined in
  `J15FinalNative.lean`).

These equations were not checked by the kernel: they were computed by the compiled searches (the Lean
compiler, the C compiler of the Lean toolchain, the Lean runtime, the library `SearchEngine` of
`lakefile.toml`). Everything else is checked by the kernel: this file only applies `covers_5900_of_k16`
(`F5900K16.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`) to the evaluated equations.

No file of level 1 imports this file.  The name of the theorem ends in `_native`.
-/

namespace SuperpermLowerBounds

/-- **Every word over `Fin 7` that contains all permutations has at least 5,900 letters** (with
the searches evaluated as compiled code). -/
theorem covers_lower_bound_7_5900_native :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5900 ≤ w.length :=
  covers_5900_of_k16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (PS.covered_one K16.f0k) (PS.covered_one K16.f1k) (PS.covered_one K16.f2k)
    (PS.covered_one K16.f3k) (PS.covered_one K16.f4k) (PS.covered_one K16.f5k)
    (PS.covered_one PS.ring)
    (PS.covered_one PS.prof36) (PS.covered_one PS.prof26) (PS.covered_one PS.prof34)
    (PS.covered_one PS.prof14) (PS.covered_one PS.prof4)
    KS.evalsT_native KS.evalsK_native J15.evals_native

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_lower_bound_7_5900_native
