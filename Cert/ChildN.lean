import Cert.KEngineN
import LowerBounds.KSearch

/-!
# Prefixes given by their path

The evaluated lemmas name the prefix that they are about by a path from another prefix: one byte per row,
`6 i + j` for the row that begins at slot `i` of the record of the last entry (`0 .. 5` weight 3, `6 .. 29`
weight 4) and has `j + 1` blocks, and `180 + j` for the first row (from the start word).  `childOf` computes the
prefix as the search does.  Nothing is proved about it: a list entry and the lemma for it are the same term, so
a wrong path would only make a lemma fail.

This file imports only `KEngineN.lean` and `KSearch.lean`.
-/

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- The marks `B` with the classes of the first `n` blocks of `x`. -/
def marksOf : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun _ B => B)
    (fun _ ih x B => ih (x / 8388608) (B ||| 2 ^ (x % 1024)))

/-- The slot record `i` of the record `w`. -/
def slotOf (w i : Nat) : Nat :=
  bif Nat.blt i 6 then w / 1024 / P138 ^ i % P138 else w / 1024 / 2 ^ 828 / P138 ^ (i - 6) % P138

/-- One more row, step `c = 6 i + j`. -/
def stepCS (a b h : Nat) (wrec : Nat → Nat) (s : CS) (c : Nat) : CS :=
  ⟨s.f - 1, bif Nat.blt (c / 6) 6 then s.t else s.t + 1, s.r + 1, s.d + (5 - c % 6),
    min s.m (bif Nat.blt (c / 6) 6 then KS.potN a b h s.t s.r s.d else KS.potS a b h s.t s.r s.d),
    max s.M (bif Nat.blt (c / 6) 6 then KS.potN a b h s.t s.r s.d else KS.potS a b h s.t s.r s.d),
    slotOf (wrec s.q) (c / 6) / 8388608 ^ (c % 6) / 1024 % 8192,
    marksOf (c % 6 + 1) (slotOf (wrec s.q) (c / 6)) s.B⟩

/-- `k` more rows, the steps in the bytes of `p` (the lowest first). -/
def childOf (a b h : Nat) (wrec : Nat → Nat) : Nat → CS → Nat → CS :=
  @Nat.rec (fun _ => CS → Nat → CS) (fun s _ => s)
    (fun _ ih s p => ih (stepCS a b h wrec s (p % 256)) (p / 256))

/-- The first row, step `180 + j`, from the row record `ws` of the start word, with the fuel `fuel`. -/
def startCS (ws fuel c : Nat) : CS :=
  ⟨fuel, 0, 1, 5 - (c - 180), 0, 0, ws / 8388608 ^ (c - 180) / 1024 % 8192, marksOf (c - 180 + 1) ws 0⟩

/-- The prefix with the path `p` of `k` rows from the start. -/
def pathCS (a b h : Nat) (wrec : Nat → Nat) (ws fuel k p : Nat) : CS :=
  childOf a b h wrec (k - 1) (startCS ws fuel (p % 256)) (p / 256)

end

end Cert
end SuperpermLowerBounds

namespace SuperpermLowerBounds
namespace Cert

noncomputable section

/-- One more row for the searches of `PEngine.lean` with links of weight 3 only (FR): the potentials stay `0`. -/
def stepP (wrec : Nat → Nat) (s : CS) (c : Nat) : CS :=
  ⟨s.f - 1, s.t, s.r + 1, s.d + (5 - c % 6), 0, 0,
    slotOf (wrec s.q) (c / 6) / 8388608 ^ (c % 6) / 1024 % 8192,
    marksOf (c % 6 + 1) (slotOf (wrec s.q) (c / 6)) s.B⟩

/-- `k` more rows of `stepP`. -/
def childOfP (wrec : Nat → Nat) : Nat → CS → Nat → CS :=
  @Nat.rec (fun _ => CS → Nat → CS) (fun s _ => s)
    (fun _ ih s p => ih (stepP wrec s (p % 256)) (p / 256))

/-- The prefix with the path `p` of `k` rows from the start (FR). -/
def pathP (wrec : Nat → Nat) (ws fuel k p : Nat) : CS :=
  childOfP wrec (k - 1) (startCS ws fuel (p % 256)) (p / 256)

end

end Cert
end SuperpermLowerBounds
