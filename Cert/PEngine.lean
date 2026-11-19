import Cert.KEngine

/-!
# A kernel engine for the searches of `PSearch.lean` (FR, FF)

The search of `PS.go` with the rule `bad`, `badR`, `keepN`, `keepS`, `keepJ` and the reset `rs`, written
for the kernel as `KEngine.lean`: marks in a number, the successors of weight 3 and 4 from the word records
(`wrec`), the jumps from the rows `orb i` of all 5,040 words, every loop `Nat.rec`, and a list of prefixes to
skip.  The potentials of `CS` are `0`.  `badR` asks that the start word is a successor of weight 3 of the last
entry: the start word is the word `0`, so this is `anySlot 6 (wrec q / 1024) 0`.

This file imports only `KEngine.lean`.
-/

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- Is `v` the first entry of one of the first `n` slots of `x`? (As `anySlot`, by `Nat.rec`.) -/
def slotHas (v : Nat) : Nat → Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih x => Nat.beq (x % P138 / 1024 % 8192) v || ih (x / P138))

/-- The jumps: the rows from the words `i`, `i + 1`, … (`n` of them). -/
def jumpC (G : Nat → Nat → Nat → List CS → Res) (orb : Nat → Nat) : Nat → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → List CS → Res) (fun _ _ L => some L)
    (fun _ ih i B L => bnd (walkC G 6 63 (orb i) B L) (fun L1 => ih (i + 1) B L1))

/-- The search below a prefix that is not skipped. -/
def pbodyC (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat)
    (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (t r d q B : Nat) (L : List CS) : Res :=
  bif bad t r d || (badR t r d && slotHas 0 6 (wrec q / 1024)) then none
  else
    bnd (bif keepN t r d then
          succC (fun n e B' L' => G t (r + 1) (d + n) 0 0 e B' L') false 0 63 6 (wrec q / 1024) B L
        else some L)
      (fun L1 => bnd (bif keepS t r d then
          succC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
            false 0 63 24 (wrec q / 1024 / 2 ^ 828) B L1
        else some L1)
        (fun L2 => bif keepJ t r d then
          jumpC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
            orb 5040 0 B L2
        else some L2))

/-- One prefix: skipped if it is the head of the list. -/
def pnodeC (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat)
    (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (f t r d q B : Nat) (L : List CS) : Res :=
  @List.casesOn CS (fun _ => Res) L
    (pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B L)
    (fun s L' => bif csEq s f t r d 0 0 q B then some L'
      else pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B L)

/-- The search with fuel `f` at a prefix (the potentials are not used). -/
def pgoC (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat) :
    Nat → Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun f ih t r d _ _ q B L => pnodeC bad badR keepN keepS keepJ rs wrec orb ih (f + 1) t r d q B L)

/-- The whole search: the first row from the start word, then `pgoC`. -/
def psearchC (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat)
    (ws fuel : Nat) (L : List CS) : Res :=
  walkC (fun n e B L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel 0 1 n 0 0 e B L') 6 63 ws 0 L

end

end Cert
end SuperpermLowerBounds
