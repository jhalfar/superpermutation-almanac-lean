import K6.Engine

/-!
# A search of `Engine.lean` cut into pieces

A search that is too large for one evaluation by the kernel is cut at a depth: `goL R cut f U q c`
runs the search below a node as `go` does, but stops at every node whose counters satisfy `cut`
and returns the list of these nodes (the frontier) in the order of the search, with `none` where
the search finds something or runs out of fuel.  `partL` does the same for the whole search
`part`.

`go_of_goL`: if the frontier below a node has no `none` and the search answers `false` below every
node of the frontier, then the search answers `false` below the node.  So a search is proved to
answer `false` by one evaluation that computes the frontier (and compares it with a list written
out in a file) and by evaluations of the search below the nodes of that list, a few at a time
(`allNo`), and a node with a large search below it is cut again.  The lists and the depths are
chosen outside Lean; nothing depends on them but the size of the evaluations.

This file imports no Mathlib.
-/

namespace K6

/-- A node of the search: the fuel, the used classes, the last entry and the counters. -/
abbrev Node (Cn : Type) := Nat × Nat × Nat × Cn

/-- `walk`, collecting lists. -/
def walkL {α : Type} (g : Nat → Nat → Nat → List α) : Nat → Nat → Nat → List α
  | _, _, 0 => []
  | U, D, n + 1 =>
    cond (U.testBit (ci D)) []
      (g (U ||| bit (ci D)) D n ++ walkL g (U ||| bit (ci D)) (nx D) n)

/-- `succ3`, collecting lists. -/
def succ3L {α : Type} (g : Nat → Nat → Nat → List α) (U q : Nat) : Nat → List α
  | 0 => []
  | j + 1 => walkL g U (s3 q j) 5 ++ succ3L g U q j

/-- `jumps`, collecting lists. -/
def jumpsL {α : Type} (g : Nat → Nat → Nat → List α) (U : Nat) : Nat → List α
  | 0 => []
  | i + 1 => walkL g U i 5 ++ jumpsL g U i

/-- The frontier of the search below a node: the nodes below it where `cut` holds, and `none` where
the search finds something or runs out of fuel before. -/
def goL {Cn : Type} (R : Rules Cn) (cut : Cn → Bool) :
    Nat → Nat → Nat → Cn → List (Option (Node Cn))
  | 0, _, _, _ => [none]
  | f + 1, U, q, c =>
    cond (cut c) [some (f + 1, U, q, c)]
      (cond (R.bad c U) [none]
        (cond (R.keepN c) (succ3L (fun U' e n => goL R cut f U' e (R.stN c n e)) U q 5) [] ++
          cond (R.keepJ c) (jumpsL (fun U' e n => goL R cut f U' e (R.stJ c n e)) U 720) []))

/-- The frontier of the whole search `part R fuel`. -/
def partL {Cn : Type} (R : Rules Cn) (cut : Cn → Bool) (fuel : Nat) : List (Option (Node Cn)) :=
  walkL (fun U e n => goL R cut fuel U e (R.init n e)) 0 0 5

/-- The search answers `false` below every node of the list. -/
def allNo {Cn : Type} (R : Rules Cn) (L : List (Node Cn)) : Bool :=
  L.all fun x => !go R x.1 x.2.1 x.2.2.1 x.2.2.2

/-- A node of a frontier below which the search answers `false` (`none` is never good). -/
def GoodN {Cn : Type} (R : Rules Cn) : Option (Node Cn) → Prop
  | none => False
  | some x => go R x.1 x.2.1 x.2.2.1 x.2.2.2 = false

section

variable {Cn : Type} (R : Rules Cn) (cut : Cn → Bool)

theorem walk_of_walkL {α : Type} {P : α → Prop} (g : Nat → Nat → Nat → Bool)
    (gL : Nat → Nat → Nat → List α) (hg : ∀ U e n, (∀ x ∈ gL U e n, P x) → g U e n = false) :
    ∀ n U D, (∀ x ∈ walkL gL U D n, P x) → walk g U D n = false
  | 0, _, _, _ => rfl
  | n + 1, U, D, h => by
    have e1 : walkL gL U D (n + 1) = cond (U.testBit (ci D)) []
        (gL (U ||| bit (ci D)) D n ++ walkL gL (U ||| bit (ci D)) (nx D) n) := rfl
    have e2 : walk g U D (n + 1) = cond (U.testBit (ci D)) false
        (g (U ||| bit (ci D)) D n || walk g (U ||| bit (ci D)) (nx D) n) := rfl
    rw [e2]
    rw [e1] at h
    cases hb : U.testBit (ci D)
    · rw [hb] at h
      have h1 := hg _ _ _ (fun x hx => h x (List.mem_append_left _ hx))
      have h2 := walk_of_walkL g gL hg n _ _ (fun x hx => h x (List.mem_append_right _ hx))
      rw [Bool.cond_false, h1, h2]
      rfl
    · rfl

theorem succ3_of_succ3L {α : Type} {P : α → Prop} (g : Nat → Nat → Nat → Bool)
    (gL : Nat → Nat → Nat → List α) (hg : ∀ U e n, (∀ x ∈ gL U e n, P x) → g U e n = false)
    (U q : Nat) : ∀ j, (∀ x ∈ succ3L gL U q j, P x) → succ3 g U q j = false
  | 0, _ => rfl
  | j + 1, h => by
    have e1 : succ3L gL U q (j + 1) = walkL gL U (s3 q j) 5 ++ succ3L gL U q j := rfl
    have e2 : succ3 g U q (j + 1) = (walk g U (s3 q j) 5 || succ3 g U q j) := rfl
    rw [e1] at h
    rw [e2, walk_of_walkL g gL hg 5 U _ (fun x hx => h x (List.mem_append_left _ hx)),
      succ3_of_succ3L g gL hg U q j (fun x hx => h x (List.mem_append_right _ hx))]
    rfl

theorem jumps_of_jumpsL {α : Type} {P : α → Prop} (g : Nat → Nat → Nat → Bool)
    (gL : Nat → Nat → Nat → List α) (hg : ∀ U e n, (∀ x ∈ gL U e n, P x) → g U e n = false)
    (U : Nat) : ∀ i, (∀ x ∈ jumpsL gL U i, P x) → jumps g U i = false
  | 0, _ => rfl
  | i + 1, h => by
    have e1 : jumpsL gL U (i + 1) = walkL gL U i 5 ++ jumpsL gL U i := rfl
    have e2 : jumps g U (i + 1) = (walk g U i 5 || jumps g U i) := rfl
    rw [e1] at h
    rw [e2, walk_of_walkL g gL hg 5 U _ (fun x hx => h x (List.mem_append_left _ hx)),
      jumps_of_jumpsL g gL hg U i (fun x hx => h x (List.mem_append_right _ hx))]
    rfl

/-- **The search answers `false` below a node if it does so below every node of the frontier.** -/
theorem go_of_goL : ∀ f U q c, (∀ x ∈ goL R cut f U q c, GoodN R x) → go R f U q c = false
  | 0, _, _, _, h => (h none (List.mem_singleton_self _)).elim
  | f + 1, U, q, c, h => by
    have e1 : goL R cut (f + 1) U q c = cond (cut c) [some (f + 1, U, q, c)]
        (cond (R.bad c U) [none]
          (cond (R.keepN c) (succ3L (fun U' e n => goL R cut f U' e (R.stN c n e)) U q 5) [] ++
            cond (R.keepJ c) (jumpsL (fun U' e n => goL R cut f U' e (R.stJ c n e)) U 720) [])) :=
      rfl
    rw [e1] at h
    cases hc : cut c
    · rw [hc, Bool.cond_false] at h
      cases hb : R.bad c U
      · rw [hb, Bool.cond_false] at h
        have e2 : go R (f + 1) U q c = (R.bad c U ||
            (R.keepN c && succ3 (fun U' e n => go R f U' e (R.stN c n e)) U q 5) ||
            (R.keepJ c && jumps (fun U' e n => go R f U' e (R.stJ c n e)) U 720)) := rfl
        have hN : (R.keepN c && succ3 (fun U' e n => go R f U' e (R.stN c n e)) U q 5) = false := by
          cases hk : R.keepN c
          · rfl
          · rw [hk, Bool.cond_true] at h
            rw [Bool.true_and]
            exact succ3_of_succ3L (fun U' e n => go R f U' e (R.stN c n e))
              (fun U' e n => goL R cut f U' e (R.stN c n e))
              (fun U' e n hx => go_of_goL f U' e _ hx) U q 5
              (fun x hx => h x (List.mem_append_left _ hx))
        have hJ : (R.keepJ c && jumps (fun U' e n => go R f U' e (R.stJ c n e)) U 720) = false := by
          cases hk : R.keepJ c
          · rfl
          · rw [hk, Bool.cond_true] at h
            rw [Bool.true_and]
            exact jumps_of_jumpsL (fun U' e n => go R f U' e (R.stJ c n e))
              (fun U' e n => goL R cut f U' e (R.stJ c n e))
              (fun U' e n hx => go_of_goL f U' e _ hx) U 720
              (fun x hx => h x (List.mem_append_right _ hx))
        rw [e2, hb, hN, hJ]
        rfl
      · rw [hb, Bool.cond_true] at h
        exact (h none (List.mem_singleton_self _)).elim
    · rw [hc, Bool.cond_true] at h
      exact h _ (List.mem_singleton_self _)

theorem good_of_allNo {L : List (Node Cn)} (h : allNo R L = true) :
    ∀ x ∈ L.map some, GoodN R x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have := List.all_eq_true.mp h y hy
  show go R y.1 y.2.1 y.2.2.1 y.2.2.2 = false
  simpa using this

/-- A node below which the search is cut at `cut`, with the frontier `L`. -/
theorem allNo_of_frontier (s : Node Cn) (L : List (Node Cn))
    (hL : goL R cut s.1 s.2.1 s.2.2.1 s.2.2.2 = L.map some) (h : allNo R L = true) :
    allNo R [s] = true := by
  have := go_of_goL R cut s.1 s.2.1 s.2.2.1 s.2.2.2 (by rw [hL]; exact good_of_allNo R h)
  simp [allNo, this]

/-- **The whole search answers `false`** if it does so below every node of its frontier. -/
theorem part_of_partL (fuel : Nat) (L : List (Node Cn)) (hL : partL R cut fuel = L.map some)
    (h : allNo R L = true) : part R fuel = false :=
  walk_of_walkL (fun U e n => go R fuel U e (R.init n e))
    (fun U e n => goL R cut fuel U e (R.init n e))
    (fun U e n hx => go_of_goL R cut fuel U e _ hx) 5 0 0
    (by
      show ∀ x ∈ partL R cut fuel, GoodN R x
      rw [hL]
      exact good_of_allNo R h)

theorem allNo_app {L1 L2 : List (Node Cn)} (h1 : allNo R L1 = true) (h2 : allNo R L2 = true) :
    allNo R (L1 ++ L2) = true := by
  unfold allNo at *
  rw [List.all_append, h1, h2]
  rfl

end

end K6
