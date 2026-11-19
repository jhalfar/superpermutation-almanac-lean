/-!
# A kernel engine for the searches of `K16Search.lean`

The search is the depth-first search of `K16.go` (rows linked by weight 3 and weight 4, the plain rule
`code`, the masks `mask`, the reversal cut `cut` with the potentials `fN`, `fS`, Rule JS if `js`), written
for the kernel:

* the marks are one natural number: bit `c` set means that the class of rank `c` is used;
* the successors of a word `q` and the blocks of their rows come from one number `wrec q`: bits `0 .. 9`
  hold the class rank of the next block of `q` (for Rule JS); then 30 slots of 138 bits, the 6 successors of
  weight 3 and the 24 of weight 4; a slot is 6 blocks of 23 bits, a block is a class rank (10 bits) and an
  entry (13 bits);
* every loop is `Nat.rec`.

The search can skip prefixes given in a list (`List CS`, in the order of the search): a prefix that is the
head of the list is not expanded and the head is removed.  `none` means found (a violation, or the fuel ran
out); `some L` means not found, with the rest `L` of the list.  `Cut.lean` proves that a search with a list
that ends with `some _` and searches of the prefixes of the list that end with `some []` give the whole search
(`some []` with the empty list); `KComplete.lean` proves that the whole search is complete.

This file imports nothing.
-/

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- `2 ^ 138`, the size of a slot. -/
abbrev P138 : Nat := 348449143727040986586495598010130648530944

/-- Slot `i` of `x`. -/
def slotX (x i : Nat) : Nat := x / P138 ^ i % P138

/-- The first entry of slot `i` of `x`. -/
def slotD (x i : Nat) : Nat := slotX x i / 1024 % 8192

/-- A prefix of the search: the fuel at its call, links of weight 4, rows, holes, the least and the largest
potential of its cuts, its last entry and its marks. -/
structure CS where
  f : Nat
  t : Nat
  r : Nat
  d : Nat
  m : Int
  M : Int
  q : Nat
  B : Nat

/-- The answer of a search: `none` found, `some L` not found, `L` the prefixes still to be skipped. -/
abbrev Res := Option (List CS)

/-- `o`, then `k` on the list that it leaves. -/
def bnd (o : Res) (k : List CS → Res) : Res :=
  @Option.rec (List CS) (fun _ => Res) none (fun L => k L) o

/-- Is `s` the prefix with these numbers? -/
def csEq (s : CS) (f t r d : Nat) (m M : Int) (q B : Nat) : Bool :=
  Nat.beq s.q q && Nat.beq s.d d && Nat.beq s.r r && Nat.beq s.t t && Nat.beq s.f f &&
    decide (s.m = m) && decide (s.M = M) && Nat.beq s.B B

/-- The row of one successor: the argument of `Nat.rec` is the number of blocks left (with `n + 1` left
the row that ends at the current block has `n` holes), `mk` the mask (bit 0: the row of the current block),
`x` the blocks still to come, `B` the marks.  `G n e B' L` is the search below the row that ends at entry `e`
with `n` holes. -/
def walkC (G : Nat → Nat → Nat → List CS → Res) : Nat → Nat → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → Nat → List CS → Res) (fun _ _ _ L => some L)
    (fun n ih mk x B L =>
      bif Nat.beq mk 0 then some L
      else bif Nat.testBit B (x % 1024) then some L
      else bnd (bif Nat.beq (mk % 2) 1 then G n (x / 1024 % 8192) (B ||| 2 ^ (x % 1024)) L else some L)
        (fun L1 => ih (mk / 2) (x / 8388608) (B ||| 2 ^ (x % 1024)) L1))

/-- The mask of a row that begins with the block of class `c0` behind a row whose next block has class `cq`:
with Rule JS only its row of one block. -/
def jsC (js : Bool) (cq c0 mk : Nat) : Nat := bif js && Nat.beq c0 cq then mk % 2 else mk

/-- The successors in turn: `x` holds the slots (138 bits each). -/
def succC (G : Nat → Nat → Nat → List CS → Res) (js : Bool) (cq mk : Nat) :
    Nat → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → List CS → Res) (fun _ _ L => some L)
    (fun _ ih x B L =>
      bnd (walkC G 6 (jsC js cq (x % 1024) mk) (x % 348449143727040986586495598010130648530944) B L)
        (fun L1 => ih (x / 348449143727040986586495598010130648530944) B L1))

/-- The search below a prefix that is not skipped. -/
def bodyC (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool)
    (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) : Res :=
  bif Nat.beq (code t r d) 0 then some L
  else bif Nat.beq (code t r d) 1 then none
  else
    bnd
      (bif !Nat.beq (code t r d) 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)) then
        succC (fun n e B' L' => G t (r + 1) (d + n) (min m (fN t r d)) (max M (fN t r d)) e B' L') js
          (wrec q % 1024) (mask t (r + 1) d) 6 (wrec q / 1024) B L
      else some L)
      (fun L1 =>
        bif !Nat.beq (code t r d) 2 && cut t r d (min m (fS t r d)) (max M (fS t r d)) then
          succC (fun n e B' L' => G (t + 1) (r + 1) (d + n) (min m (fS t r d)) (max M (fS t r d)) e B' L')
            js (wrec q % 1024) (mask (t + 1) (r + 1) d) 24
            (wrec q / 1024 / 2 ^ 828) B L1
        else some L1)

/-- One prefix: skipped if it is the head of the list. -/
def nodeC (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool)
    (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) : Res :=
  @List.casesOn CS (fun _ => Res) L
    (bodyC code mask fN fS cut wrec js G t r d m M q B L)
    (fun s L' => bif csEq s f t r d m M q B then some L'
      else bodyC code mask fN fS cut wrec js G t r d m M q B L)

/-- The search with fuel `f` at a prefix. -/
def goC (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool) :
    Nat → Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun f ih t r d m M q B L => nodeC code mask fN fS cut wrec js ih (f + 1) t r d m M q B L)

/-- The whole search: the first row from the start word (orbit record `ws`), then `goC` with fuel `fuel`. -/
def searchC (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
    (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool) (ws fuel : Nat)
    (L : List CS) : Res :=
  walkC (fun n e B L' => goC code mask fN fS cut wrec js fuel 0 1 n 0 0 e B L') 6 63 ws 0 L

end

end Cert
end SuperpermLowerBounds
