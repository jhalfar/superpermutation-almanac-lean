import LowerBounds.PFinalK16
import LowerBounds.PK16F0Native
import LowerBounds.PK16F1Native
import LowerBounds.PK16Native
import LowerBounds.PRingNative
import LowerBounds.PProfNative

/-!
# 5,899 for 7 symbols, with the twelve evaluated equations

**Trusted here.**  Every theorem of this file depends on the axioms recorded by `native_decide` for the
twelve equations:

* F0 … F5: `K16.f0k`, `K16.f1k`, `K16.f2k`, `K16.f3k`, `K16.f4k`, `K16.f5k` (`PK16F0Native.lean`,
  `PK16F1Native.lean`, `PK16Native.lean`; the engine of `K16Search.lean`);
* FR: `PS.ring` (`PRingNative.lean`); FF: `PS.prof36`, `PS.prof26`, `PS.prof34`, `PS.prof14`, `PS.prof4`
  (`PProfNative.lean`; the engine of `PSearch.lean`).

They are joined by `covers_5899_of_k16` (`PFinalK16.lean`, axioms `propext`, `Classical.choice`,
`Quot.sound`). No file of level 1 imports this file.
-/

namespace SuperpermLowerBounds

open T5899

/-- **Every word over `Fin 7` that contains all permutations has at least 5,899 letters.** -/
theorem covers_lower_bound_7_k16_native :
    ∀ w : List (Fin 7), SuperpermutationBounds.Covers w → 5899 ≤ w.length :=
  covers_5899_of_k16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (PS.covered_one K16.f0k) (PS.covered_one K16.f1k) (PS.covered_one K16.f2k)
    (PS.covered_one K16.f3k) (PS.covered_one K16.f4k) (PS.covered_one K16.f5k)
    (PS.covered_one PS.ring)
    (PS.covered_one PS.prof36) (PS.covered_one PS.prof26) (PS.covered_one PS.prof34)
    (PS.covered_one PS.prof14) (PS.covered_one PS.prof4)

end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.covers_lower_bound_7_k16_native
