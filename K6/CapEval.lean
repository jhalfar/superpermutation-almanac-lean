import K6.CE.EF0

/-!
# Evaluation by the kernel: the chain search on 6 symbols with the caps `W6` (0 to 20 holes)

One search, 52,386 calls of `go`, cut into pieces by `tools/gen_te.py` (see `K6/Frontier.lean`); the
files of the pieces are in `K6/CE/`.  No Mathlib is loaded.
-/

namespace K6

theorem capEval : part (capRules [W6] 0 20 TB_0_20 TK_0_20) 130 = false := CE.EF0

end K6

#print axioms K6.capEval
