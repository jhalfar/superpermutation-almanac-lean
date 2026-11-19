import LowerBounds.KSearch

/-! Reading the rule records, and their check (no Mathlib). -/

namespace SuperpermLowerBounds
namespace Cert

open KS (codeF potN a1F uF segF pkF big)

/-- The code. -/
def codeR (rl : Nat → Nat → Nat → Nat) (A R C t r d : Nat) : Nat :=
  bif Nat.blt t A && Nat.blt d C then (bif Nat.ble r R then rl t r d else rl t R d) % 8 else 0

/-- The mask. -/
def maskR (rl : Nat → Nat → Nat → Nat) (A R C t r d : Nat) : Nat :=
  bif Nat.blt t A && Nat.ble r R && Nat.blt d C then rl t r d / 8 % 64 else 63

/-- The bound of the first test of the cut. -/
def t1R (rl : Nat → Nat → Nat → Nat) (t r d : Nat) : Int := ((rl t r d / 512 % 1048576 : Nat) : Int) - 524288

/-- The bound of the second test of the cut. -/
def t2R (rl : Nat → Nat → Nat → Nat) (t r d : Nat) : Int :=
  ((rl t r d / 536870912 % 1048576 : Nat) : Int) - 262144

/-- The cut. -/
def cutR (rl : Nat → Nat → Nat → Nat) (A R C t r d : Nat) (m M : Int) : Bool :=
  decide (0 ≤ m) || !(Nat.blt t A && Nat.ble r R && Nat.blt d C) || decide (t1R rl t r d ≤ M + m) ||
    decide (t2R rl t r d ≤ m)

/-- What is checked about the record of `t`, `r`, `d`. -/
def pR (P : Nat → Nat → Nat) (s lo hi a b h : Nat) (rl : Nat → Nat → Nat → Nat) (A R C t r d : Nat) : Bool :=
  Nat.beq (rl t r d % 8) (codeF P s lo hi t r d) &&
  (List.range 6).all (fun j => Nat.beq (codeR rl A R C t r (d + (5 - j))) 0 ||
    Nat.beq (rl t r d / 8 % 64 / 2 ^ j % 2) 1) &&
  (Nat.ble (codeF P s lo hi t r d) 1 ||
    (decide (t1R rl t r d ≤ a1F P s lo hi a b h t r d) && decide (t2R rl t r d ≤ big) &&
      decide (t2R rl t r d + pkF (uF P s a b h) (segF P s a b h) (potN a b h t r d) t d hi ≤ t1R rl t r d)))

end Cert
end SuperpermLowerBounds
