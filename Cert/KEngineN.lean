import Cert.KEngine

/-!
# The kernel engine with natural potentials

`goNat` is `goC` of `KEngine.lean` with the potentials `m`, `M` shifted by `off = 2 ^ 18` and kept as natural
numbers, so that the kernel works with its fast natural numbers only.  The potentials of the cuts are
`off + a r - (b d + 2 h t)` (weight 3) and that minus `h` (weight 4); the cut reads the two bounds of the rule
record as they are stored (`T1 + 2 off`, `T2 + off`).  `goN` takes the potentials as integers (as `goC`) and
shifts them once.  `KEquiv.lean` proves `goN = goC` for the records of a statement.

This file imports only `KEngine.lean`.
-/

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- The shift of the potentials. -/
abbrev offN : Nat := 262144

/-- The least of two numbers (by `Nat.ble`). -/
def nmin (a b : Nat) : Nat := bif Nat.ble a b then a else b

/-- The largest of two numbers. -/
def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a

/-- The cut on shifted potentials. -/
def cutNat (rl : Nat → Nat → Nat → Nat) (A R C t r d m M : Nat) : Bool :=
  Nat.ble offN m || !(Nat.blt t A && Nat.ble r R && Nat.blt d C) ||
    Nat.ble (rl t r d / 512 % 1048576) (M + m) || Nat.ble (rl t r d / 536870912 % 1048576) m

/-- The search below a prefix that is not skipped (shifted potentials). -/
def bodyNat (code mask : Nat → Nat → Nat → Nat) (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat)
    (wrec : Nat → Nat) (js : Bool)
    (G : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List CS → Res)
    (t r d m M q B : Nat) (L : List CS) : Res :=
  bif Nat.beq (code t r d) 0 then some L
  else bif Nat.beq (code t r d) 1 then none
  else
    bnd
      (bif !Nat.beq (code t r d) 3 &&
          cutNat rl A R C t r d (nmin m (offN + a * r - (b * d + 2 * h * t)))
            (nmax M (offN + a * r - (b * d + 2 * h * t))) then
        succC (fun n e B' L' => G t (r + 1) (d + n) (nmin m (offN + a * r - (b * d + 2 * h * t)))
          (nmax M (offN + a * r - (b * d + 2 * h * t))) e B' L') js
          (wrec q % 1024) (mask t (r + 1) d) 6 (wrec q / 1024) B L
      else some L)
      (fun L1 =>
        bif !Nat.beq (code t r d) 2 &&
            cutNat rl A R C t r d (nmin m (offN + a * r - (b * d + 2 * h * t + h)))
              (nmax M (offN + a * r - (b * d + 2 * h * t + h))) then
          succC (fun n e B' L' => G (t + 1) (r + 1) (d + n) (nmin m (offN + a * r - (b * d + 2 * h * t + h)))
            (nmax M (offN + a * r - (b * d + 2 * h * t + h))) e B' L')
            js (wrec q % 1024) (mask (t + 1) (r + 1) d) 24
            (wrec q / 1024 / 2 ^ 828) B L1
        else some L1)

/-- One prefix: skipped if it is the head of the list (the list holds the potentials unshifted). -/
def nodeNat (code mask : Nat → Nat → Nat → Nat) (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat)
    (wrec : Nat → Nat) (js : Bool)
    (G : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List CS → Res)
    (f t r d m M q B : Nat) (L : List CS) : Res :=
  @List.casesOn CS (fun _ => Res) L
    (bodyNat code mask rl A R C a b h wrec js G t r d m M q B L)
    (fun s L' => bif csEq s f t r d ((m : Int) - offN) ((M : Int) - offN) q B then some L'
      else bodyNat code mask rl A R C a b h wrec js G t r d m M q B L)

/-- The search with fuel `f` at a prefix (shifted potentials). -/
def goNat (code mask : Nat → Nat → Nat → Nat) (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat)
    (wrec : Nat → Nat) (js : Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → List CS → Res)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun f ih t r d m M q B L => nodeNat code mask rl A R C a b h wrec js ih (f + 1) t r d m M q B L)

/-- `goNat` with the potentials given as integers. -/
def goN (code mask : Nat → Nat → Nat → Nat) (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat)
    (wrec : Nat → Nat) (js : Bool) (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) : Res :=
  goNat code mask rl A R C a b h wrec js f t r d (m + offN).toNat (M + offN).toNat q B L

/-- The whole search with shifted potentials. -/
def searchN (code mask : Nat → Nat → Nat → Nat) (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat)
    (wrec : Nat → Nat) (js : Bool) (ws fuel : Nat) (L : List CS) : Res :=
  walkC (fun n e B L' => goNat code mask rl A R C a b h wrec js fuel 0 1 n offN offN e B L') 6 63 ws 0 L

end

end Cert
end SuperpermLowerBounds
