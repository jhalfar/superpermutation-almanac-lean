import Cert.KEngine
import Cert.W
import LowerBounds.PSearch

/-! The checks of the word tables (no Mathlib; `WSpec.lean` proves what they give). -/

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- `p i` for `i0 ≤ i < i0 + n`. -/
def allIdx (p : Nat → Bool) (i0 : Nat) : Nat → Bool :=
  @Nat.rec (fun _ => Bool) true (fun n ih => p (i0 + n) && ih)

/-- The table `cT` lists `l` from index `i`. -/
def chkCodes : List Nat → Nat → Bool
  | [], _ => true
  | c :: cs, i => Nat.beq (cT i) c && chkCodes cs (i + 1)

/-- `l` is increasing and above `b`. -/
def incB : Nat → List Nat → Bool
  | _, [] => true
  | b, x :: l => Nat.blt b x && incB x l

/-- `OrbOK` as a check. -/
def orbB : Nat → Nat → Nat → Bool :=
  @Nat.rec (fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih D x => Nat.beq (x % 1024) (crkT D) && Nat.beq (x / 1024 % 8192) D && ih (nxT D) (x / 8388608))

/-- `SlotsOK` as a check. -/
def slotsB : Nat → Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih x => orbB 6 (x % P138 / 1024 % 8192) (x % P138) && ih (x / P138))

/-- One of the first `n` slots of `x` begins at `v`. -/
def anySlot (n x v : Nat) : Bool := (List.range n).any fun s => Nat.beq (slotD x s) v

/-- Everything that is checked about word `i`. -/
def pW (i : Nat) : Bool :=
  Nat.blt (nxT i) 5040 && Nat.beq (cT (nxT i)) (PS.nxtF (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (cT i)) &&
  Nat.beq (PS.cidxF 7 (4 * (7 - 1)) (16 ^ (7 - 1) - 1) (cT i)) (cidT (crkT i)) &&
  Nat.beq (wrecT i % 1024) (crkT (nxT i)) &&
  slotsB 6 (wrecT i / 1024) && slotsB 24 (wrecT i / 1024 / 2 ^ 828) &&
  (grp3 (PS.excF (16 ^ (7 - 1) - 1) (cT i) % 16 ^ (7 - 3))).all (fun v => anySlot 6 (wrecT i / 1024) v) &&
  (grp4 (PS.excF (16 ^ (7 - 1) - 1) (cT i) % 16 ^ (7 - 4))).all
    (fun v => anySlot 24 (wrecT i / 1024 / 2 ^ 828) v) &&
  (grp3 (cT i / 16 ^ 3)).contains i && (grp4 (cT i / 16 ^ 4)).contains i

end

end Cert
end SuperpermLowerBounds
