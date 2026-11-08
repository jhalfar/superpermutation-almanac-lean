import K6.CapRules
import K6.Frontier

/-!
# Cutting the chain search

`cutR Z`: the counters `(rows, holes)` of a node with at least `Z` rows; the chain search is cut at
such nodes (`Frontier.lean`), with the frontiers written out in the files of `K6/CE/`.  This file
imports no Mathlib.
-/

namespace K6

/-- A node with `Z` rows or more. -/
def cutR (Z : Nat) (c : Nat × Nat) : Bool := Nat.ble Z c.1

end K6
