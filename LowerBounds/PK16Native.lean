import LowerBounds.K16Search
import LowerBounds.PTables

/-!
# F2 to F5 (two to five links) of 5,899, searched by the engine of `K16Search.lean`, evaluated as compiled code

**Trusted here.**  Every theorem of this file is proved by `native_decide`: Lean does not check the
computation in its kernel but runs it as compiled code and records the result as an axiom
(`SuperpermLowerBounds.K16.<name>._native.native_decide.ax_1_1`, listed by `#print axioms`).  So this file
trusts, in addition to the kernel: the Lean compiler (from `PSearch.lean`, `KSearch.lean` and
`K16Search.lean` to C), the C compiler of the Lean toolchain, the Lean runtime (natural numbers, integers,
arrays, byte arrays, tasks), and that the library `SearchEngine` of `lakefile.toml` was compiled from these
three files as they are.  The search and the proof that its answer `false` means what is claimed
(`KSound.lean`, `KRev.lean`, `KPot.lean`, `KRules.lean`, `K16Word.lean`, `K16Sound.lean`, `K16Pot.lean`,
`K16Rules.lean`) are checked by the kernel and do not depend on this file.

What is evaluated: `K16.seqSearch 7 Ptabs s 0 (84 - 6 s) a b h true fuel ds nt 0 nt`, the statement F_s of the
written proof of 5,899 (every sequence with exactly `s` links of weight 4 and at most `84 - 6 s` holes has at
most `P_s(x)` rows, tables of set B) with the reversal cut for the potential `(a, b, h)` and Rule JS.
Reference: a C program with the same rule (`opt/n7/d16/krows/kjs.c`) keeps 185,928,533 / 69,918,349 / 814,664 /
62,942 prefixes for F2 / F3 / F4 / F5 and finds no violation; potential (10, 16, 30), one part each.

This file imports `K16Search.lean` and the tables `PTables.lean` only.  No file of level 1 imports it.
-/

namespace SuperpermLowerBounds
namespace K16

open T5899

/-- F2: two links, at most 72 holes (185,928,533 kept prefixes). -/
theorem f2k : seqSearch 7 Ptabs 2 0 72 10 16 30 true 400 0 1 0 1 = false := by
  native_decide

/-- F3: three links, at most 66 holes (69,918,349 kept prefixes). -/
theorem f3k : seqSearch 7 Ptabs 3 0 66 10 16 30 true 400 0 1 0 1 = false := by
  native_decide

/-- F4: four links, at most 60 holes (814,664 kept prefixes). -/
theorem f4k : seqSearch 7 Ptabs 4 0 60 10 16 30 true 400 0 1 0 1 = false := by
  native_decide

/-- F5: five links, at most 54 holes (62,942 kept prefixes). -/
theorem f5k : seqSearch 7 Ptabs 5 0 54 10 16 30 true 400 0 1 0 1 = false := by
  native_decide

end K16
end SuperpermLowerBounds

#print axioms SuperpermLowerBounds.K16.f2k
#print axioms SuperpermLowerBounds.K16.f3k
#print axioms SuperpermLowerBounds.K16.f4k
#print axioms SuperpermLowerBounds.K16.f5k
