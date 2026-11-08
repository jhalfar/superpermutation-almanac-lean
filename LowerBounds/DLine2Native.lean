-- Changed for the Superpermutation Almanac: a modified copy of proofs/lean/n8_46134/LowerBounds/DLine2Native.lean of github.com/jhalfar/superpermutations (commit 64ab6a7, Apache License 2.0).
-- Comment only: lines 13-14 of the module doc name the shared library that Lake builds here instead of the one that build.sh made.
import LowerBounds.DSearch

/-!
# (H2): the search for a chain on 8 symbols above the line `17 r ≤ 38 δ + 264`, evaluated as compiled code

**Trusted here.**  The theorem of this file is proved by `native_decide`: Lean does not check the
computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.S.lineSearch_8_17_38_264._native.native_decide.ax_1_1`, listed by `#print axioms`).  So this file trusts, in
addition to the kernel: the Lean compiler (from `DSearch.lean` to C), the C compiler of the Lean
toolchain (`leanc`, clang), the Lean runtime (natural numbers, byte arrays, tasks), and that the
shared library that Lake builds from `DSearch.lean` and loads (the library `DSearchEngine` of
`lakefile.toml`, with `precompileModules`) was compiled from `DSearch.lean` as it is.  The search itself and the proof that its answer `false`
means what is claimed (`DSound.lean`, `DModel.lean`) are checked by the kernel and do not depend
on this file.

What is evaluated: `S.lineSearch 8 2097152 17 38 264 400 40 251`.
The table of marks has `8 ^ 7 = 2097152` bytes, the fuel is 400 pieces, and the search is cut at
depth 40 into 251 parts that run as tasks.

Reference: two C programs of mine, which share no code with this one, visit
5,807,830,513 chains for this search (deepest prefix 381 pieces) and find none.

This file imports `DSearch.lean` only.  No file of level 1 imports it.
-/

namespace SuperpermLowerBounds
namespace S

/-- **(H2), evaluated.**  The search for a model chain on 8 symbols with `17 r > 38 δ + 264`
finds none. -/
theorem lineSearch_8_17_38_264 : lineSearch 8 2097152 17 38 264 400 40 251 = false := by
  native_decide

end S
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.S.lineSearch_8_17_38_264
