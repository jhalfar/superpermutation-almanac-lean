import K6.TightRules
import K6.Frontier

/-!
# Cutting the search of the tight case

`cutZ Z`: the counters of a node whose row number `z` is at least `Z`; the search of the tight case
is cut at such nodes (`Frontier.lean`).  The frontiers are compared with lists written out in the
files of `K6/TE/`, which needs equality of counters to be decidable.  This file imports no Mathlib.
-/

namespace K6

deriving instance DecidableEq for FC

/-- A node at row `Z` or later. -/
def cutZ (Z : Nat) (c : FC) : Bool := Nat.ble Z c.z

end K6
