-- Changed for the 5,898 batch: K6/Cap.lean of the 872 batch (proofs/lean/small/K6/Cap.lean of
-- github.com/jhalfar/superpermutations at commit 64ab6a7) for 7 symbols and for all rules of PSearch.lean without
-- links of weight 4 (`pstmt_of_part`); the table checks read three counters.
import K7.Sound
import K7.Rules
import LowerBounds.PRules
import LowerBounds.PFinal

/-!
# The statements of `PSeq.lean` from the kernel search on 7 symbols

`pstmt_of_part`: if the search of `Engine.lean` with the rules `psRules rs A B C TB TK TJ bad keepN keepJ`
answers `false`, and the bit tables agree with the rules `bad`, `keepN`, `keepJ` (`TabAgrees`, checked by the
kernel), then the statement `PS.PStmt 7 rs bad noRule keepN noRule keepJ` of `PSeq.lean` holds: no sequence
of rows whose prefixes the rules keep (seams by `keepN`, jumps by `keepJ`, no links of weight 4) is `bad`.
From there the theorems of `PLevels.lean` and `PRules.lean` (of the 5,899 proof in `../n7`, unchanged) give the
chain caps (`chainCapK_of_part`, `wcap_of_part`) and the profile statements (`noProfileK_of_part`).

This is `K6/Cap.lean` of the 872 batch (for the chain rules on 6 symbols) for 7 symbols and for all rules of
`PSearch.lean` without links of weight 4 and without the closing test: the proof relabels the symbols so that
the first word is `1 2 3 4 5 6 7`, as `PS.stmt_of_parts` does, and reads the rule along the sequence
(`PS.RuleAlong`) as the rule of the engine (`KAlong`).
-/

namespace K7

open SuperpermLowerBounds SuperpermLowerBounds.S SuperpermLowerBounds.PS

/-- The table `T` agrees with `f` on `t < A`, `r < B`, `d < C`. -/
def TabAgrees (A B C T : ℕ) (f : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range A).all fun t => (List.range B).all fun r => (List.range C).all fun d =>
    T.testBit ((t * B + r) * C + d) == f t r d

theorem lk_eq {A B C T : ℕ} {f : ℕ → ℕ → ℕ → Bool} (h : TabAgrees A B C T f = true) (t r d : ℕ) :
    lk A B C T f t r d = f t r d := by
  unfold lk
  by_cases hin : t < A ∧ r < B ∧ d < C
  · obtain ⟨ht, hr, hd⟩ := hin
    have hb : (t.blt A && r.blt B && d.blt C) = true := by
      simp [Nat.blt_eq, ht, hr, hd]
    rw [hb, Bool.cond_true]
    have h1 := List.all_eq_true.mp h t (List.mem_range.mpr ht)
    have h2 := List.all_eq_true.mp h1 r (List.mem_range.mpr hr)
    have h3 := List.all_eq_true.mp h2 d (List.mem_range.mpr hd)
    simpa using h3
  · have hb : (t.blt A && r.blt B && d.blt C) = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      exact hin ⟨hc.1.1, hc.1.2, hc.2⟩
    rw [hb, Bool.cond_false]

/-- The table `T` agrees with `f` on `t`, `r0 ≤ r < r0 + n`, `d < C` (a piece of `TabAgrees`). -/
def RowsAgree (B C T : ℕ) (f : ℕ → ℕ → ℕ → Bool) (t r0 n : ℕ) : Bool :=
  (List.range n).all fun i => (List.range C).all fun d =>
    T.testBit ((t * B + (r0 + i)) * C + d) == f t (r0 + i) d

/-- `TabAgrees` from pieces of `w` rows. -/
theorem tabAgrees_of_rows {A B C T w m : ℕ} {f : ℕ → ℕ → ℕ → Bool} (hB : B ≤ m * w)
    (h : ∀ t, t < A → ∀ k, k < m → RowsAgree B C T f t (k * w) w = true) :
    TabAgrees A B C T f = true := by
  unfold TabAgrees
  rw [List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro r hr
  have ht' := List.mem_range.mp ht
  have hr' := List.mem_range.mp hr
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0, Nat.mul_zero] at hB
      omega
    · exact h0
  have hk : r / w < m := by
    rw [Nat.div_lt_iff_lt_mul hw]
    omega
  have h1 := h t ht' (r / w) hk
  unfold RowsAgree at h1
  have h2 := List.all_eq_true.mp h1 (r % w) (List.mem_range.mpr (Nat.mod_lt r hw))
  have e : r / w * w + r % w = r := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod r w
  rw [e] at h2
  exact h2

/-- `PS.PCont` is `KCont`. -/
theorem kcont_of_pcont : ∀ (rest : List TRow) (last : List ℕ) (used : List (List ℕ)),
    PCont 7 last used rest → KCont last used rest
  | [], _, _, _ => trivial
  | (_, []) :: _, _, _, h => h.elim
  | (kd, v :: R) :: rest, last, used, h => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨by omega, h2, fun hk => h3.1 hk, h4, h5, h6, kcont_of_pcont rest _ _ h7⟩

section Rules

variable {rs : Bool} {A B C TB TK TJ : ℕ} {bad keepN keepJ : ℕ → ℕ → ℕ → Bool}

/-- The rule along a sequence of `PSearch.lean` is the rule of the engine. -/
theorem kalong_of_ruleAlong (hB : TabAgrees A B C TB bad = true) (hK : TabAgrees A B C TK keepN = true)
    (hJ : TabAgrees A B C TJ keepJ = true) :
    ∀ (rest : List TRow) (t r d : ℕ) (last : List ℕ) (used : List (List ℕ)),
      RuleAlong 7 rs bad noRule keepN noRule keepJ t r d last rest →
      KAlong (psRules rs A B C TB TK TJ bad keepN keepJ) (t, r, d) used rest
  | [], t, r, d, last, used, h => by
    simp only [RuleAlong, noRule, Bool.false_eq_true, false_and, or_false] at h
    show lk A B C TB bad t r d = true
    rw [lk_eq hB]
    exact h
  | (_, []) :: _, _, _, _, _, _, h => by simp [RuleAlong] at h
  | (kd, v :: R) :: rest, t, r, d, last, used, h => by
    simp only [RuleAlong] at h
    obtain ⟨hk, h'⟩ := h
    match kd, hk, h' with
    | 0, hk, h' =>
      refine ⟨?_, ?_⟩
      · show lk A B C TK keepN t r d = true
        rw [lk_eq hK]
        exact hk
      · have e : stepC (psRules rs A B C TB TK TJ bad keepN keepJ) (t, r, d) 0 (5 - R.length)
            (enc ((v :: R).getLast (List.cons_ne_nil v R))) = (t, r + 1, d + (5 - R.length)) :=
          rfl
        rw [e]
        simp only [tK, rK, if_pos] at h'
        have e2 : 7 - 2 - R.length = 5 - R.length := rfl
        rw [e2] at h'
        exact kalong_of_ruleAlong hB hK hJ rest _ _ _ _ _ h'
    | 1, hk, _ => simp [keepK, noRule] at hk
    | kd + 2, hk, h' =>
      refine ⟨?_, ?_⟩
      · show lk A B C TJ keepJ t r d = true
        rw [lk_eq hJ]
        exact hk
      · have e : stepC (psRules rs A B C TB TK TJ bad keepN keepJ) (t, r, d) (kd + 2) (5 - R.length)
            (enc ((v :: R).getLast (List.cons_ne_nil v R))) =
            (t + 1, (bif rs then 0 else r) + 1, (bif rs then 0 else d) + (5 - R.length)) :=
          rfl
        rw [e]
        have e1 : tK (kd + 2) t = t + 1 := rfl
        have e3 : ∀ x, rK rs (kd + 2) x = (bif rs then 0 else x) := fun x => rfl
        have e2 : 7 - 2 - R.length = 5 - R.length := rfl
        rw [e1, e3, e3, e2] at h'
        exact kalong_of_ruleAlong hB hK hJ rest _ _ _ _ _ h'

/-- **The search on 7 symbols, evaluated by the kernel, proves the statement of `PSeq.lean`.** -/
theorem pstmt_of_part {fuel : ℕ}
    (hB : TabAgrees A B C TB bad = true) (hK : TabAgrees A B C TK keepN = true)
    (hJ : TabAgrees A B C TJ keepJ = true)
    (hs : part (psRules rs A B C TB TK TJ bad keepN keepJ) fuel = false) :
    PStmt 7 rs bad noRule keepN noRule keepJ := by
  intro L hL hne hkeep
  refine ⟨?_, fun h => by simp [ap, noRule] at h⟩
  by_contra hbad
  rw [Bool.not_eq_false] at hbad
  cases L with
  | nil => exact hne rfl
  | cons x0 rest0 =>
    obtain ⟨kd0, Q0⟩ := x0
    have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
    obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
    have hv0 : PermW 7 v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
    have hL' := hL.relabel hv0
    have hkeep' : ∀ u x w, relabSeq v0 ((kd0, v0 :: R0) :: rest0) = u ++ x :: w → u ≠ [] →
        ap (keepK keepN noRule keepJ x.1) (cnt 7 rs u) = true := by
      intro u x w huw hu
      obtain ⟨u0, L2, e0, hu0, hL2⟩ := List.map_eq_append_iff.mp huw
      obtain ⟨x1, w1, e1, hx1, _⟩ := List.map_eq_cons_iff.mp hL2
      have h := hkeep u0 x1 w1 (by rw [e0, e1]) (by
        rintro rfl
        exact hu hu0.symm)
      have ec : cnt 7 rs u = cnt 7 rs u0 := by
        rw [← hu0]
        exact cnt_relab rs v0 u0
      rw [ec, ← hx1]
      exact h
    have hbad' : ap bad (cnt 7 rs (relabSeq v0 ((kd0, v0 :: R0) :: rest0))) = true := by
      rw [cnt_relab]
      exact hbad
    have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
        (kd0, [1, 2, 3, 4, 5, 6, 7] :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
      have e := S.map_relab_self hv0.1
      rw [hv0.2.1] at e
      have e' : v0.map (S.relab v0) = [1, 2, 3, 4, 5, 6, 7] := by rw [e]; rfl
      simp [relabSeq, e']
    rw [hshape] at hL' hkeep' hbad'
    generalize R0.map (List.map (S.relab v0)) = R1 at hL' hkeep' hbad'
    generalize relabSeq v0 rest0 = rest1 at hL' hkeep' hbad'
    have hperm : ∀ w ∈ [1, 2, 3, 4, 5, 6, 7] :: R1, PermW 7 w :=
      hL'.words (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self
    have hcl : List.Pairwise (fun a b => ¬ a ~r b)
        (([1, 2, 3, 4, 5, 6, 7] :: R1) ++ (rest1.map Prod.snd).flatten) := by
      have := hL'.classes
      simp only [List.map_cons, List.flatten_cons] at this
      exact this
    have hcl' := List.pairwise_append.mp hcl
    have hsz := hL'.size_le (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self
    have hR1 : R1.length ≤ 5 := by
      simp only [List.length_cons] at hsz
      omega
    have hdoor := S.door_chain (by norm_num) _ hperm
      (hL'.doors (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) List.mem_cons_self) hcl'.1
    have hcont := pcont_of_seq (by norm_num) rest1 (kd0, [1, 2, 3, 4, 5, 6, 7] :: R1)
      ([1, 2, 3, 4, 5, 6, 7] :: R1) (List.cons_ne_nil _ _) hL' hcl'.2.2
    have hne1 : ∀ y ∈ rest1, y.2 ≠ [] :=
      fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)
    have ec : (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) = (0, 1, 5 - R1.length) := by
      simp only [List.length_cons, Prod.mk.injEq, true_and]
      omega
    have hA := ruleAlong_of_prefix (k := 7) rs bad noRule keepN noRule keepJ rest1
      (0, 1, 5 - R1.length)
      (([1, 2, 3, 4, 5, 6, 7] :: R1).getLast (List.cons_ne_nil _ _)) hne1
      (by
        intro u x w huw
        have h := hkeep' ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: u) x w (by rw [huw]; rfl) (by simp)
        have e2 : cnt 7 rs ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: u)
            = u.foldl (SuperpermLowerBounds.PS.stepC 7 rs)
                (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) := rfl
        rw [e2, ec] at h
        exact h)
      (by
        have e2 : cnt 7 rs ((kd0, [1, 2, 3, 4, 5, 6, 7] :: R1) :: rest1)
            = rest1.foldl (SuperpermLowerBounds.PS.stepC 7 rs)
                (0, 1, 7 - 1 - ([1, 2, 3, 4, 5, 6, 7] :: R1).length) := rfl
        rw [e2, ec] at hbad'
        exact Or.inl hbad')
    have hK' := kalong_of_ruleAlong hB hK hJ rest1 0 1 (5 - R1.length) _
      ([1, 2, 3, 4, 5, 6, 7] :: R1) hA
    exact not_kalong (psRules rs A B C TB TK TJ bad keepN keepJ) hs R1 rest1 hR1 hperm hdoor hcl'.1
      (kcont_of_pcont _ _ _ hcont) hK'

end Rules

/-- **Chain caps from the kernel search** (levels `0 … hi`). -/
theorem wcap_of_part {caps : List (List ℕ)} {hi A B C TB TK fuel : ℕ}
    (hB : TabAgrees A B C TB (seqBad caps 0 0 hi) = true)
    (hK : TabAgrees A B C TK (seqKeepN caps 0 0 hi) = true)
    (hJ : TabAgrees A B C 0 noRule = true)
    (hs : part (psRules false A B C TB TK 0 (seqBad caps 0 0 hi) (seqKeepN caps 0 0 hi) noRule) fuel
      = false) :
    WCap 7 (capF caps 0) hi := by
  have hst := pstmt_of_part hB hK hJ hs
  have hst' : PStmt 7 false (seqBad caps 0 0 hi) noRule (seqKeepN caps 0 0 hi) (seqKeepS caps 0 0 hi)
      noRule := by
    intro L hL hne hkeep
    refine hst L hL hne (fun u x w huw hu => ?_)
    rcases x with ⟨kd, Q⟩
    have h := hkeep u (kd, Q) w huw hu
    rcases kd with _ | _ | kd
    · exact h
    · simp [keepK, ap, seqKeepS] at h
    · simp [keepK, ap, noRule] at h
  exact wcap_of_seqCap (seqCap_level (fun j hj => absurd hj (Nat.not_lt_zero j))
    (seqCapLt_zero 7 0 _) hst')

/-- **Chain caps from the kernel search** (levels `0 … hi`), on vertices. -/
theorem chainCapK_of_part {caps : List (List ℕ)} {hi A B C TB TK fuel : ℕ}
    (hB : TabAgrees A B C TB (seqBad caps 0 0 hi) = true)
    (hK : TabAgrees A B C TK (seqKeepN caps 0 0 hi) = true)
    (hJ : TabAgrees A B C 0 noRule = true)
    (hs : part (psRules false A B C TB TK 0 (seqBad caps 0 0 hi) (seqKeepN caps 0 0 hi) noRule) fuel
      = false) :
    ChainCapK 7 (capF caps 0) hi :=
  chainCapK_of_wcap (wcap_of_part hB hK hJ hs)

/-- **A profile statement from the kernel search**, given the chain cap. -/
theorem noProfileK_of_part {M : List ℕ} {ts : List (ℕ × ℕ)} {G A B C TB TK TJ fuel : ℕ}
    (hM : WCap 7 (fun x => M.getD x 0) G) (hts : ∀ t ∈ ts, 1 ≤ t.1 ∧ t.2 ≤ G) (hne : ts ≠ [])
    (hB : TabAgrees A B C TB (profBad ts) = true) (hK : TabAgrees A B C TK (profKeepN M ts) = true)
    (hJ : TabAgrees A B C TJ (profKeepJ ts) = true)
    (hs : part (psRules true A B C TB TK TJ (profBad ts) (profKeepN M ts) (profKeepJ ts)) fuel = false) :
    NoProfileK 7 ts :=
  noProfileK_of_stmt hM hts hne (pstmt_of_part hB hK hJ hs)

end K7

#print axioms K7.pstmt_of_part
#print axioms K7.chainCapK_of_part
#print axioms K7.noProfileK_of_part
