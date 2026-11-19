import Cert.PEngine
import Cert.KComplete
import LowerBounds.PSeq

/-!
# The kernel engine of `PEngine.lean` is complete

As `KComplete.lean`, for the searches of `PSearch.lean` (FR, FF): `pstmt_of_psearchC` gives `PS.PStmt`.
Besides `CEnc` the jumps need the rows of all words (`PEnc.orb`) and the start word is the word `0`.
-/

namespace SuperpermLowerBounds
namespace Cert

open S (PermW WLink DoorEq)
open PS (TRow PCont LinkK IsSeq relabSeq PAlong RuleAlong tK rK keepK PStmt)

/-- What the jumps and the ring test need besides `CEnc`. -/
structure PEnc (enc : List ℕ → ℕ) (crk nx wrec orb : ℕ → ℕ) (ws : ℕ) : Prop where
  ce : CEnc enc crk nx wrec ws
  orb_ok : ∀ v, PermW 7 v → OrbOK crk nx 6 (enc v) (orb (enc v))
  lt : ∀ v, PermW 7 v → enc v < 5040
  st0 : enc (List.range' 1 7) = 0

/-! ### Suffixes -/

theorem jumpC_suffix (G : Nat → Nat → Nat → List CS → Res) (hG : ∀ n e B L, SufR L (G n e B L))
    (orb : Nat → Nat) : ∀ (n i B : Nat) (L : List CS), SufR L (jumpC G orb n i B L) := by
  intro n
  induction n with
  | zero => intro i B L; exact sufR_some L
  | succ n ih =>
    intro i B L
    show SufR L (bnd (walkC G 6 63 (orb i) B L) (fun L1 => jumpC G orb n (i + 1) B L1))
    refine sufR_bnd (walkC_suffix G hG _ _ _ _ _) ?_
    intro L1 _ L' h'
    exact ih _ _ L1 L' h'

section Rule

variable (bad badR keepN keepS keepJ : Nat → Nat → Nat → Bool) (rs : Bool) (wrec orb : Nat → Nat)

theorem pbodyC_suffix (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hG : ∀ t r d m M q B L, SufR L (G t r d m M q B L)) (t r d q B : Nat) (L : List CS) :
    SufR L (pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B L) := by
  unfold pbodyC
  refine sufR_cond _ (sufR_none L) (sufR_bnd ?_ ?_)
  · exact sufR_cond _ (succC_suffix _ (fun n e B L => hG _ _ _ _ _ _ _ _) _ _ _ _ _ _ _) (sufR_some L)
  · intro L1 _ L' h'
    have h2 : SufR L1 (bnd (bif keepS t r d then
          succC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
            false 0 63 24 (wrec q / 1024 / 2 ^ 828) B L1
        else some L1)
        (fun L2 => bif keepJ t r d then
          jumpC (fun n e B' L' => G (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
            orb 5040 0 B L2
        else some L2)) := by
      refine sufR_bnd (sufR_cond _ (succC_suffix _ (fun n e B L => hG _ _ _ _ _ _ _ _) _ _ _ _ _ _ _)
        (sufR_some L1)) ?_
      intro L2 _ L'' h''
      exact (sufR_cond _ (jumpC_suffix _ (fun n e B L => hG _ _ _ _ _ _ _ _) _ _ _ _ _) (sufR_some L2)) L'' h''
    exact h2 L' h'

theorem pnodeC_suffix (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hG : ∀ t r d m M q B L, SufR L (G t r d m M q B L)) (f t r d q B : Nat) (L : List CS) :
    SufR L (pnodeC bad badR keepN keepS keepJ rs wrec orb G f t r d q B L) := by
  cases L with
  | nil => exact pbodyC_suffix bad badR keepN keepS keepJ rs wrec orb G hG t r d q B []
  | cons s L' =>
    show SufR (s :: L') (bif csEq s f t r d 0 0 q B then some L'
      else pbodyC bad badR keepN keepS keepJ rs wrec orb G t r d q B (s :: L'))
    refine sufR_cond _ ?_ (pbodyC_suffix bad badR keepN keepS keepJ rs wrec orb G hG t r d q B _)
    intro L1 h
    cases h
    exact List.suffix_cons s L'

theorem pgoC_succ (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) :
    pgoC bad badR keepN keepS keepJ rs wrec orb (f + 1) t r d m M q B L =
      pnodeC bad badR keepN keepS keepJ rs wrec orb (pgoC bad badR keepN keepS keepJ rs wrec orb f)
        (f + 1) t r d q B L := rfl

theorem pgoC_suffix : ∀ (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS),
    SufR L (pgoC bad badR keepN keepS keepJ rs wrec orb f t r d m M q B L) := by
  intro f
  induction f with
  | zero => intro t r d m M q B L; exact sufR_none L
  | succ f ih =>
    intro t r d m M q B L
    rw [pgoC_succ]
    exact pnodeC_suffix bad badR keepN keepS keepJ rs wrec orb _ ih (f + 1) t r d q B L

end Rule

/-! ### Completeness -/

section Engine

variable {enc : List ℕ → ℕ} {crk nx wrec orb : ℕ → ℕ} {ws : ℕ}

theorem slotHas_of (v : ℕ) : ∀ (n x i : ℕ), i < n → slotD x i = v → slotHas v n x = true := by
  intro n
  induction n with
  | zero => intro x i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro x i hi hv
    show (Nat.beq (x % P138 / 1024 % 8192) v || slotHas v n (x / P138)) = true
    cases i with
    | zero =>
      have e : slotD x 0 = x % P138 / 1024 % 8192 := by simp [slotD, slotX]
      rw [e] at hv
      rw [beqT hv]
      rfl
    | succ i =>
      have e : slotD x (i + 1) = slotD (x / P138) i := by
        unfold slotD slotX
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      rw [e] at hv
      rw [ih (x / P138) i (by omega) hv, Bool.or_true]

theorem jumpC_found (G : ℕ → ℕ → ℕ → List CS → Res) (hG : ∀ n e B L, SufR L (G n e B L)) (B : ℕ) :
    ∀ (n i D : ℕ), i ≤ D → D < i + n → walkC G 6 63 (orb D) B [] = none →
      jumpC G orb n i B [] = none := by
  intro n
  induction n with
  | zero => intro i D h1 h2; omega
  | succ n ih =>
    intro i D h1 h2 hw
    show bnd (walkC G 6 63 (orb i) B []) (fun L1 => jumpC G orb n (i + 1) B L1) = none
    by_cases hD : D = i
    · subst hD
      rw [hw]
      rfl
    · have hsuf := walkC_suffix G hG 6 63 (orb i) B []
      generalize walkC G 6 63 (orb i) B [] = X at hsuf
      cases X with
      | none => rfl
      | some L1 =>
        rw [nil_of_sufR hsuf rfl, bnd_some]
        exact ih (i + 1) D (by omega) (by omega) hw

variable {bad badR keepN keepS keepJ : ℕ → ℕ → ℕ → Bool} {rs : Bool}

theorem pgoC_complete (PE : PEnc enc crk nx wrec orb ws) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (B : ℕ) (last : List ℕ)
      (used : List (List ℕ)),
      PermW 7 last → (∀ u ∈ used, PermW 7 u) → MInvN enc crk B used → PCont 7 last used rest →
      PAlong 7 enc rs bad badR keepN keepS keepJ 0 1 0 fuel t r d last rest →
      pgoC bad badR keepN keepS keepJ rs wrec orb fuel t r d m M (enc last) B [] = none := by
  have CE := PE.ce
  have hid : PermW 7 (List.range' 1 7) := PS.permW_range' 7
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro rest t r d m M B last used hlast hused hM hcont halong
    rw [pgoC_succ]
    show pbodyC bad badR keepN keepS keepJ rs wrec orb (pgoC bad badR keepN keepS keepJ rs wrec orb fuel)
      t r d (enc last) B [] = none
    unfold pbodyC
    cases hb : (bad t r d || (badR t r d && slotHas 0 6 (wrec (enc last) / 1024)))
    · rw [Bool.cond_false]
      cases rest with
      | nil =>
        exfalso
        simp only [PAlong] at halong
        rcases halong with h | ⟨h1, h2⟩
        · simp [h] at hb
        · obtain ⟨i, hi, hD⟩ := CE.s3 last _ hlast hid h2
          rw [PE.st0] at hD
          have := slotHas_of 0 6 _ i hi hD
          simp [h1, this] at hb
      | cons Q rest' =>
        obtain ⟨kd, Q⟩ := Q
        cases Q with
        | nil => exact hcont.elim
        | cons v R =>
          obtain ⟨hR, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
          simp only [PAlong] at halong
          obtain ⟨hkeep, _, halong'⟩ := halong
          have hv : PermW 7 v := hperm v List.mem_cons_self
          have hused' : ∀ u ∈ used ++ v :: R, PermW 7 u := by
            intro u hu
            rcases List.mem_append.mp hu with h | h
            · exact hused u h
            · exact hperm u h
          have hbit : (63 / 2 ^ R.length) % 2 = 1 := by
            have : R.length ≤ 5 := hR
            interval_cases h : R.length <;> norm_num
          have hwalk : ∀ (x : ℕ), OrbOK crk nx 6 (enc v) x →
              walkC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (tK kd t)
                (rK rs kd r + 1) (rK rs kd d + n) 0 0 e B' L') 6 63 x B [] = none := by
            intro x hx
            exact walkC_complete CE _ (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              R 5 63 v x B used (by omega) hbit hperm hdoor hx hM hused hnew hpw
              (by
                intro B' hB'
                exact ih rest' _ _ _ 0 0 B' _ (used ++ v :: R) (hperm _ (List.getLast_mem _)) hused' hB'
                  hcont' halong')
          match kd, hkeep, hlink, hwalk with
          | 0, hkeep, hlink, hwalk =>
            have hk : keepN t r d = true := hkeep
            rw [hk, Bool.cond_true]
            obtain ⟨i, hi, hD⟩ := CE.s3 last v hlast hv (hlink.1 rfl)
            have hO := slotsOK_get (CE.slots3 last hlast) hi
            rw [hD] at hO
            have hw0 : walkC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L') 6 (jsC false 0 (slotX (wrec (enc last) / 1024) i % 1024) 63)
                (slotX (wrec (enc last) / 1024) i) B [] = none := hwalk _ hO
            have hf := succC_found (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L') (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              false 0 63 B 6 (wrec (enc last) / 1024) i hi hw0
            rw [hf]
            rfl
          | 1, hkeep, hlink, hwalk =>
            have hk : keepS t r d = true := hkeep
            obtain ⟨i, hi, hD⟩ := CE.s4 last v hlast hv (hlink.2 rfl)
            have hO := slotsOK_get (CE.slots4 last hlast) hi
            rw [hD] at hO
            have hw1 : walkC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L') 6 (jsC false 0 (slotX (wrec (enc last) / 1024 / 2 ^ 828) i % 1024) 63)
                (slotX (wrec (enc last) / 1024 / 2 ^ 828) i) B [] = none := hwalk _ hO
            have hf := succC_found (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L') (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              false 0 63 B 24 (wrec (enc last) / 1024 / 2 ^ 828) i hi hw1
            have hsuf : SufR [] (bif keepN t r d then
                succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L')
                  false 0 63 6 (wrec (enc last) / 1024) B []
                else some []) :=
              sufR_cond _ (succC_suffix _ (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                _ _ _ _ _ _ _) (sufR_some [])
            generalize (bif keepN t r d then
                succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L')
                  false 0 63 6 (wrec (enc last) / 1024) B []
                else some []) = X at hsuf
            cases X with
            | none => rfl
            | some L1 =>
              rw [nil_of_sufR hsuf rfl, bnd_some, hk, Bool.cond_true, hf]
              rfl
          | kd + 2, hkeep, _, hwalk =>
            have hk : keepJ t r d = true := hkeep
            have hw2 : walkC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L') 6 63 (orb (enc v)) B [] = none := hwalk _ (PE.orb_ok v hv)
            have hf := jumpC_found (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1) ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L') (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) B 5040 0
              (enc v) (Nat.zero_le _) (by have := PE.lt v hv; omega) hw2
            have hsuf : SufR [] (bif keepN t r d then
                succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L')
                  false 0 63 6 (wrec (enc last) / 1024) B []
                else some []) :=
              sufR_cond _ (succC_suffix _ (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                _ _ _ _ _ _ _) (sufR_some [])
            generalize (bif keepN t r d then
                succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel t (r + 1) (d + n) 0 0 e B' L')
                  false 0 63 6 (wrec (enc last) / 1024) B []
                else some []) = X at hsuf
            cases X with
            | none => rfl
            | some L1 =>
              rw [nil_of_sufR hsuf rfl, bnd_some]
              have hsuf2 : SufR [] (bif keepS t r d then
                  succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
                    false 0 63 24 (wrec (enc last) / 1024 / 2 ^ 828) B []
                  else some []) :=
                sufR_cond _ (succC_suffix _ (fun n e B' L' => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                  _ _ _ _ _ _ _) (sufR_some [])
              generalize (bif keepS t r d then
                  succC (fun n e B' L' => pgoC bad badR keepN keepS keepJ rs wrec orb fuel (t + 1)
                    ((bif rs then 0 else r) + 1) ((bif rs then 0 else d) + n) 0 0 e B' L')
                    false 0 63 24 (wrec (enc last) / 1024 / 2 ^ 828) B []
                  else some []) = Y at hsuf2
              cases Y with
              | none => rfl
              | some L2 =>
                rw [nil_of_sufR hsuf2 rfl, bnd_some, hk, Bool.cond_true]
                exact hf
    · rfl

/-- The whole search finds a sequence along which the rule holds. -/
theorem psearchC_none (PE : PEnc enc crk nx wrec orb ws) (fuel : ℕ)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ 5) (hperm : ∀ w ∈ List.range' 1 7 :: R1, PermW 7 w)
    (hdoor : List.IsChain (DoorEq 7) (List.range' 1 7 :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 7 :: R1))
    (hcont : PCont 7 ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 7 :: R1) rest)
    (halong : PAlong 7 enc rs bad badR keepN keepS keepJ 0 1 0 fuel 0 1 (5 - R1.length)
      ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) rest) :
    psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel [] = none := by
  have hbit : (63 / 2 ^ R1.length) % 2 = 1 := by
    interval_cases h : R1.length <;> norm_num
  exact walkC_complete PE.ce _ (fun n e B L => pgoC_suffix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    R1 5 63 (List.range' 1 7) ws 0 [] hR1 hbit hperm hdoor PE.ce.ws (minvN_zero enc crk) (by simp)
    (by simp) hpw
    (by
      intro B' hB'
      exact pgoC_complete PE fuel rest 0 1 (5 - R1.length) 0 0 B' _ (List.range' 1 7 :: R1)
        (hperm _ (List.getLast_mem _)) hperm (by simpa using hB') hcont halong)

/-- **The rule holds along no sequence from the start word** (as `PS.not_ruleAlong_of_search`). -/
theorem not_ruleAlong_of_psearchC (PE : PEnc enc crk nx wrec orb ws) {fuel : ℕ}
    (hs : psearchC bad badR keepN keepS keepJ rs wrec orb ws fuel [] ≠ none)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ 7 - 2) (hperm : ∀ w ∈ List.range' 1 7 :: R1, PermW 7 w)
    (hdoor : List.IsChain (DoorEq 7) (List.range' 1 7 :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 7 :: R1))
    (hcont : PCont 7 ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) (List.range' 1 7 :: R1) rest) :
    ¬ RuleAlong 7 rs bad badR keepN keepS keepJ 0 1 (7 - 2 - R1.length)
      ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) rest := by
  intro hA
  have hP := PS.palong_of_ruleAlong (enc := enc) 0 rest fuel _ _ _ _ hA
  exact hs (psearchC_none PE fuel R1 rest hR1 hperm hdoor hpw hcont hP)

end Engine

end Cert
end SuperpermLowerBounds
