import K7.Engine
import LowerBounds.PSearch

/-!
# The rules of `PSearch.lean` for the search of `Engine.lean`

`psRules rs A B C TB TK TJ bad keepN keepJ`: counters `(t, r, d)` as in `PSearch.lean` (links that are not
seams, rows and holes; with `rs` a jump starts the rows and holes again); continue with a seam when
`keepN t r d`, with a jump when `keepJ t r d`, found when `bad t r d`.  The three rules are read from the
bit tables `TB`, `TK`, `TJ` for `t < A`, `r < B`, `d < C` and computed outside; `Prove.lean` proves that
tables which agree with the rules (`TabAgrees`, checked by the kernel) give the statement `PS.PStmt` of
`PSeq.lean` for the rules.  `cutJ os ts Z`: the nodes with `os[t] + r ≥ Z` (with `os[t]` the rows before
link `t`, the number of rows) and the nodes where a profile `ts` jumps; a search is cut there into pieces
(`Frontier.lean`).  This file imports no Mathlib: the evaluations load only it.
-/

namespace K7

/-- A Boolean function of three numbers, read from the bits of `T` for `t < A`, `r < B`, `d < C`. -/
@[inline] def lk (A B C T : Nat) (f : Nat → Nat → Nat → Bool) (t r d : Nat) : Bool :=
  cond (t.blt A && r.blt B && d.blt C) (T.testBit ((t * B + r) * C + d)) (f t r d)

/-- The counters of the search: links that are not seams, rows, holes. -/
abbrev Cn := Nat × Nat × Nat

/-- The rules of `PSearch.lean`, read from tables. -/
def psRules (rs : Bool) (A B C TB TK TJ : Nat) (bad keepN keepJ : Nat → Nat → Nat → Bool) :
    Rules Cn where
  init n _ := (0, 1, n)
  stN c n _ := (c.1, c.2.1 + 1, c.2.2 + n)
  stJ c n _ := (c.1 + 1, (bif rs then 0 else c.2.1) + 1, (bif rs then 0 else c.2.2) + n)
  keepN c := lk A B C TK keepN c.1 c.2.1 c.2.2
  keepJ c := lk A B C TJ keepJ c.1 c.2.1 c.2.2
  bad c _ := lk A B C TB bad c.1 c.2.1 c.2.2

/-- A node with `os[t] + r ≥ Z`, or one that the profile `ts` continues with a jump. -/
def cutJ (os : List Nat) (ts : List (Nat × Nat)) (Z : Nat) (c : Cn) : Bool :=
  Nat.ble Z (os.getD c.1 0 + c.2.1) || SuperpermLowerBounds.PS.profKeepJ ts c.1 c.2.1 c.2.2

end K7
