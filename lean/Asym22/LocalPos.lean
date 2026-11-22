import Quantitative.GuardCoordinates
import Quantitative.GuardEvents
import Quantitative.ActiveSlotEvents

/-!
# Local positions of the guards (J. Halfar, November 2026)

Addition to Jay Pantone's quantitative development (release 9ccbe66).
His collision equations are written in the original cuts `x` of the guards,
modulo `m`; a local cut of the background is `x + e` with `0 ≤ e ≤ G`, and the
unknown `e` puts a slack `G` on every term of a foreign relation. Here the
equations are written in the local positions instead: the guard with cut
`x u` stands at index `x u + #{w : x w < x u}` of the background circle of
length `m + G`. Two candidates that share a row see the same letters, so a
foreign local cut differs from this index only by the active letters of the
two blocks (`Asym22.TD.PhysicalOldCuts`), a slack of order `r` instead of `G`.

This file has the part without the grid: the position map, its injectivity
(so counts over guard backgrounds become counts over all position tuples),
the literal index of an old-cut block, the foreign relation with bounded
offsets, and the power ratio `(m + G)^G ≤ 2 m^G`.
-/

namespace CoefficientTwoPrecision.TD.LocalPos

open CoefficientTwoPrecision.StationaryCircle CoefficientTwoPrecision.GuardCoordinates
open CoefficientTwoPrecision.StationaryRelations CoefficientTwoPrecision.GuardEvents
open CoefficientTwoPrecision.ActiveSlotEvents

variable {m G : Nat} {α : Type}

/-- The bound of the constants of a collision equation in local positions: `2 r^2`
(with `r = d + 3`), in place of Jay's `stationaryOffsetBound d G` and `primaryOffsetBound d G`,
which are of order `r G`. -/
def localOffsetBound (d : Nat) : Nat := 2 * (d + 3) ^ 2

theorem local_bound_guard (d : Nat) : 2 * d * (d + 4 + 1) ≤ localOffsetBound d := by
  unfold localOffsetBound
  nlinarith

theorem local_bound_event (d : Nat) : 2 * d * (d + 4 + 1) + (d - 1) ≤ localOffsetBound d := by
  unfold localOffsetBound
  have : d - 1 ≤ d := Nat.sub_le d 1
  nlinarith

/-- The number of guards whose cut is below `c`. -/
def before (x : Fin G → Fin m) (c : Nat) : Nat :=
  (Finset.univ.filter (fun w : Fin G => (x w).val < c)).card

theorem before_le (x : Fin G → Fin m) (c : Nat) : before x c ≤ G := by
  unfold before
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem before_mono (x : Fin G → Fin m) {c c' : Nat} (h : c ≤ c') : before x c ≤ before x c' := by
  unfold before
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  omega

theorem before_zero (x : Fin G → Fin m) : before x 0 = 0 := by
  unfold before
  simp

theorem before_succ (x : Fin G → Fin m) (c : Nat) :
    before x (c + 1) =
      before x c + (Finset.univ.filter (fun w : Fin G => (x w).val = c)).card := by
  classical
  unfold before
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  · apply Finset.disjoint_filter.mpr
    intro w _ h1 h2
    omega

theorem before_succ_le (x : Fin G → Fin m) (hx : Function.Injective x) (c : Nat) :
    before x (c + 1) ≤ before x c + 1 := by
  classical
  rw [before_succ]
  apply Nat.add_le_add_left
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hx (Fin.ext (ha.trans hb.symm))

/-- The index of guard `u` in the background circle. -/
def localPos (x : Fin G → Fin m) (u : Fin G) : Fin (m + G) :=
  ⟨(x u).val + before x (x u).val, by
    have h1 := before_le x (x u).val
    have h2 := (x u).isLt
    omega⟩

theorem localPos_val (x : Fin G → Fin m) (u : Fin G) :
    (localPos x u).val = (x u).val + before x (x u).val := rfl

theorem localPos_lt_iff (x : Fin G → Fin m) (u w : Fin G) :
    localPos x w < localPos x u ↔ (x w).val < (x u).val := by
  rw [Fin.lt_def, localPos_val, localPos_val]
  constructor
  · intro h
    by_contra hn
    have hmono := before_mono x (Nat.le_of_not_lt hn)
    omega
  · intro h
    have hmono := before_mono x (Nat.le_of_lt h)
    omega

/-- Different guard-cut maps have different position maps. -/
theorem localPos_injective :
    Function.Injective (localPos : (Fin G → Fin m) → Fin G → Fin (m + G)) := by
  intro x x' h
  funext u
  have hb (y : Fin G → Fin m) : before y (y u).val =
      (Finset.univ.filter (fun w : Fin G => localPos y w < localPos y u)).card := by
    unfold before
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (localPos_lt_iff y u w).symm
  have h1 := hb x
  have h2 := hb x'
  rw [h] at h1
  have hv : (localPos x u).val = (localPos x' u).val := by rw [h]
  rw [localPos_val, localPos_val] at hv
  apply Fin.ext
  omega

theorem filter_length_eq_card (p : Fin G → Prop) [DecidablePred p] :
    ((List.finRange G).filter (fun j => decide (p j))).length =
      (Finset.univ.filter p).card := by
  classical
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange G).filter _)]
  congr 1
  ext j
  simp

theorem block_length (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) :
    (block old guard cuts cut).length =
      (Finset.univ.filter (fun w : Fin G => (cuts w).val = cut.val)).card + 1 := by
  classical
  have h := filter_length_eq_card (fun j : Fin G => cuts j = cut)
  have he : (Finset.univ.filter (fun w : Fin G => (cuts w).val = cut.val)) =
      Finset.univ.filter (fun j : Fin G => cuts j = cut) := by
    ext w
    simp [Fin.ext_iff]
  rw [he, ← h]
  simp [block, controlsAt]

/-- The literal length of the first `n` old-cut blocks. -/
theorem prefix_length (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (n : Nat) (hn : n ≤ m) :
    (((List.finRange m).take n).flatMap (block old guard cuts)).length = n + before cuts n := by
  induction n with
  | zero => simp [before_zero]
  | succ n ih =>
    have hlt : n < m := hn
    have hi : n < (List.finRange m).length := by simpa using hlt
    have htake : (List.finRange m).take (n + 1) = (List.finRange m).take n ++ [⟨n, hlt⟩] := by
      rw [List.take_succ_eq_append_getElem hi]
      simp
    rw [htake, List.flatMap_append, List.length_append, ih (Nat.le_of_lt hlt)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [block_length, before_succ]
    dsimp only
    omega

theorem blockStart_eq (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) : blockStart old guard cuts cut = cut.val + before cuts cut.val :=
  prefix_length old guard cuts cut.val (Nat.le_of_lt cut.isLt)

/-- An index inside the block of old cut `cut` lies between the two prefix counts. -/
theorem block_index_bounds (old : Fin m → α) (guard : Fin G → α) (cuts : Fin G → Fin m)
    (cut : Fin m) (offset : Nat) (hoff : offset < (block old guard cuts cut).length) :
    cut.val + before cuts cut.val ≤ blockStart old guard cuts cut + offset ∧
      blockStart old guard cuts cut + offset ≤ cut.val + before cuts (cut.val + 1) := by
  rw [blockStart_eq]
  rw [block_length] at hoff
  rw [before_succ]
  omega

/-- The stationary relation of a frame, transported to coordinates `Y` that differ
from the local cuts by at most `R`: the constant is bounded by `2 d (R + 1)`. -/
theorem local_relation {d : Nat} (M : Int) (hd : 2 ≤ d) (assignment : Assignment d)
    (Y localCuts : Fin (d + 2) → Int) (R : Nat)
    (hoffset : ∀ i, (localCuts i - Y i).natAbs ≤ R)
    (q : Fin (d + 2) → Int) (phase : Fin (d + 2) → Fin 2) (t : Int)
    (hq : Int.ModEq M (∑ i, weight assignment i * q i) 0)
    (hlocal : ∀ i, Int.ModEq M (localCuts i) (q i + t + (phase i).val)) :
    ∃ b : Int, b.natAbs ≤ 2 * d * (R + 1) ∧
      Int.ModEq M (∑ i, weight assignment i * Y i) b := by
  have hsum := weight_abs_sum hd assignment
  have hframe := frame_relation M t (weight assignment) q
    (fun i => ((phase i).val : Int)) localCuts (weight_sum assignment) hq hlocal
  have hph := weighted_abs_bound (weight assignment)
    (fun i => ((phase i).val : Int)) 1 (fun i => by have hi := (phase i).isLt; omega)
  have hoff := weighted_abs_bound (weight assignment) (fun i => localCuts i - Y i) R hoffset
  rw [hsum] at hph hoff
  refine ⟨(∑ i, weight assignment i * ((phase i).val : Int)) -
    ∑ i, weight assignment i * (localCuts i - Y i), ?_, ?_⟩
  · have h := Int.natAbs_sub_le (∑ i, weight assignment i * ((phase i).val : Int))
      (∑ i, weight assignment i * (localCuts i - Y i))
    have he : 2 * d * (R + 1) = 2 * d * 1 + 2 * d * R := by ring
    omega
  · have he : (∑ i, weight assignment i * Y i) =
        (∑ i, weight assignment i * localCuts i) -
          ∑ i, weight assignment i * (localCuts i - Y i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact hframe.sub_right _

/-- The event congruence: the shared control stands at `q + t + phase`. -/
theorem primary_relation_local {d : Nat} (M : Int) (hd : 2 ≤ d)
    (assignment : Assignment d) (shared : Fin (d + 2)) (Y : Fin (d + 2) → Int)
    (q t : Int) (phase : Fin 2) (b : Int) (C : Nat)
    (hforeign : Int.ModEq M (∑ i, weight assignment i * Y i) b)
    (hb : b.natAbs ≤ C)
    (hshared : Int.ModEq M (Y shared) (q + t + phase.val)) :
    ∃ b1 : Int, b1.natAbs ≤ C + (d - 1) ∧
      Int.ModEq M
        (weight assignment shared * (q + t) + remainingSum assignment shared Y) b1 := by
  let a := weight assignment shared
  have hcoef : a.natAbs ≤ d - 1 := by
    dsimp [a]
    rw [weight_abs_formula hd]
    split_ifs <;> omega
  have hproduct : (a * (phase.val : Int)).natAbs ≤ d - 1 := by
    rw [Int.natAbs_mul]
    have hp : ((phase.val : Int)).natAbs ≤ 1 := by have := phase.isLt; omega
    calc
      a.natAbs * ((phase.val : Int)).natAbs ≤ (d - 1) * 1 := Nat.mul_le_mul hcoef hp
      _ = d - 1 := Nat.mul_one _
  have hb1 := Int.natAbs_sub_le b (a * (phase.val : Int))
  refine ⟨b - a * (phase.val : Int), by omega, ?_⟩
  rw [split_shared] at hforeign
  have hsub := ((hshared.mul_left a).add_right (remainingSum assignment shared Y)).symm.trans
    hforeign
  have h := hsub.sub_right (a * (phase.val : Int))
  have hleft : a * (q + t + (phase.val : Int)) + remainingSum assignment shared Y -
      a * (phase.val : Int) = a * (q + t) + remainingSum assignment shared Y := by ring
  rw [hleft] at h
  exact h

/-- `(1 + G/m)^k ≤ 1 / (1 - k G / m)` in natural numbers. -/
theorem power_shift (m G k : Nat) (hk : k * G ≤ m) :
    (m + G) ^ k * (m - k * G) ≤ m ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k * G ≤ m := by nlinarith
    have ih' := ih hk'
    have hstep : (m + G) * (m - (k + 1) * G) ≤ m * (m - k * G) := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hk
      have h1 : m - (k + 1) * G = s := by omega
      have h2 : m - k * G = s + G := by
        have : (k + 1) * G = k * G + G := by ring
        omega
      rw [h1, h2, hs]
      calc
        ((k + 1) * G + s + G) * s ≤ ((k + 1) * G + s + G) * s + (k + 1) * G * G :=
          Nat.le_add_right _ _
        _ = ((k + 1) * G + s) * (s + G) := by ring
    calc
      (m + G) ^ (k + 1) * (m - (k + 1) * G) = (m + G) ^ k * ((m + G) * (m - (k + 1) * G)) := by
        ring
      _ ≤ (m + G) ^ k * (m * (m - k * G)) := Nat.mul_le_mul_left _ hstep
      _ = ((m + G) ^ k * (m - k * G)) * m := by ring
      _ ≤ m ^ (k + 1) * m := Nat.mul_le_mul_right _ ih'
      _ = m ^ (k + 1 + 1) := by ring

/-- For `m ≥ 2 G^2` the position tuples are at most twice the cut tuples. -/
theorem power_double (m G : Nat) (hsize : 2 * G ^ 2 ≤ m) : (m + G) ^ G ≤ 2 * m ^ G := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have hG : G = 0 := by
      rcases Nat.eq_zero_or_pos G with h | h
      · exact h
      · have : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ h
        omega
    subst hG
    simp
  have hGG : G * G ≤ m := by nlinarith
  have h := power_shift m G G hGG
  have hhalf : m ≤ 2 * (m - G * G) := by
    have : G * G = G ^ 2 := by ring
    omega
  have h2 : (m + G) ^ G * m ≤ 2 * ((m + G) ^ G * (m - G * G)) := by
    have := Nat.mul_le_mul_left ((m + G) ^ G) hhalf
    nlinarith
  have h3 : (m + G) ^ G * m ≤ (2 * m ^ G) * m := by
    calc
      (m + G) ^ G * m ≤ 2 * ((m + G) ^ G * (m - G * G)) := h2
      _ ≤ 2 * m ^ (G + 1) := Nat.mul_le_mul_left 2 h
      _ = (2 * m ^ G) * m := by ring
  exact Nat.le_of_mul_le_mul_right h3 hm

end CoefficientTwoPrecision.TD.LocalPos

#print axioms CoefficientTwoPrecision.TD.LocalPos.localPos_injective
#print axioms CoefficientTwoPrecision.TD.LocalPos.blockStart_eq
#print axioms CoefficientTwoPrecision.TD.LocalPos.local_relation
#print axioms CoefficientTwoPrecision.TD.LocalPos.power_double
