import Asym25.Parking
import Quantitative.OriginTransport

/-!
# Exponent 25: in the compiled repair program the role phase follows the translation

`Aligned r n b program` says, for a program that starts after `n` normal
batches and `b` batches: every normal macro starts with the two counts
congruent modulo `r`, and every parking macro uses the normal order and
starts with the normal count congruent to 0 or 2. Jay Pantone's compiler
(`RepairProgram.compile`) produces such a program when every group's phase
is 0 or 2 (`compile_aligned`): a parking block has a multiple of `r`
batches, so it does not change the difference of the two counts modulo `r`.

`tied_prefix_state` is his `MacroCatalogue.proper_prefix_state` with the
joint index named and tied to the translation, and `tied_row_mem` is his
`LiteralEnvelope.actual_row_mem` followed by `OriginTransport.envelope_canonical`,
for a safe cut that is a multiple of `r`. The conclusion `EnvelopeT` is the
envelope that `Asym25.Degree` counts.
-/

namespace CoefficientTwoPrecision.Asym25

open PositiveParking JointStates LiteralSchedule PositiveSchedule TargetTrace MacroCatalogue
open RepairIntervals RepairGroups RepairProgram OriginTransport
open SuperpermutationUpperBound

def Aligned (r : ℕ) : ℕ → ℕ → List Macro → Prop
  | _, _, [] => True
  | n, b, .normal :: rest => n % r = b % r ∧ Aligned r (n + 1) (b + 1) rest
  | n, b, .parking c :: rest => c = false ∧ (n % r = 0 ∨ n % r = 2) ∧ Aligned r n (b + 2) rest

theorem aligned_append (r : ℕ) (first second : List Macro) (n b : ℕ)
    (h1 : Aligned r n b first)
    (h2 : Aligned r (n + normalCount first) (b + batchCount first) second) :
    Aligned r n b (first ++ second) := by
  induction first generalizing n b with
  | nil => simpa only [List.nil_append, normalCount, batchCount, Nat.add_zero] using h2
  | cons instruction first ih =>
    cases instruction with
    | normal =>
      refine ⟨h1.1, ih (n + 1) (b + 1) h1.2 ?_⟩
      have e1 : n + 1 + normalCount first = n + (normalCount first + 1) := by omega
      have e2 : b + 1 + batchCount first = b + (1 + batchCount first) := by omega
      rw [e1, e2]
      exact h2
    | parking c =>
      refine ⟨h1.1, h1.2.1, ih n (b + 2) h1.2.2 ?_⟩
      have e2 : b + 2 + batchCount first = b + (2 + batchCount first) := by omega
      rw [e2]
      exact h2

theorem aligned_normals (r a n b : ℕ) (h : n % r = b % r) :
    Aligned r n b (List.replicate a .normal) := by
  induction a generalizing n b with
  | zero => trivial
  | succ a ih => exact ⟨h, ih (n + 1) (b + 1) (Nat.ModEq.add_right 1 h)⟩

theorem aligned_parkings (r a n b : ℕ) (h : n % r = 0 ∨ n % r = 2) :
    Aligned r n b (List.replicate a (.parking false)) := by
  induction a generalizing b with
  | zero => trivial
  | succ a ih => exact ⟨rfl, h, ih (b + 2)⟩

/-- What alignment says about the macro at a split of the program. -/
def SplitProp (r n b : ℕ) (before : List Macro) : Macro → Prop
  | .normal => (n + normalCount before) % r = (b + batchCount before) % r
  | .parking c => c = false ∧
      ((n + normalCount before) % r = 0 ∨ (n + normalCount before) % r = 2)

theorem aligned_split (r : ℕ) (before : List Macro) (instruction : Macro) (after : List Macro)
    (n b : ℕ) (h : Aligned r n b (before ++ instruction :: after)) :
    SplitProp r n b before instruction := by
  induction before generalizing n b with
  | nil =>
    cases instruction with
    | normal => simpa only [SplitProp, normalCount, batchCount, Nat.add_zero] using h.1
    | parking c =>
      exact ⟨h.1, by simpa only [normalCount, Nat.add_zero] using h.2.1⟩
  | cons first before ih =>
    cases first with
    | normal =>
      have hrec := ih (n + 1) (b + 1) h.2
      have e1 : n + 1 + normalCount before = n + (normalCount before + 1) := by omega
      have e2 : b + 1 + batchCount before = b + (1 + batchCount before) := by omega
      cases instruction with
      | normal =>
        change (n + 1 + normalCount before) % r = (b + 1 + batchCount before) % r at hrec
        rw [e1, e2] at hrec
        exact hrec
      | parking c =>
        obtain ⟨hc, hrec⟩ := hrec
        rw [e1] at hrec
        exact ⟨hc, hrec⟩
    | parking c' =>
      have hrec := ih n (b + 2) h.2.2
      have e2 : b + 2 + batchCount before = b + (2 + batchCount before) := by omega
      cases instruction with
      | normal =>
        change (n + normalCount before) % r = (b + 2 + batchCount before) % r at hrec
        rw [e2] at hrec
        exact hrec
      | parking c => exact hrec

variable {Label : Type*}

/-- The compiled repair program is aligned when all phases are 0 or 2 and
the normal order is used for parking. -/
theorem compile_aligned (r : ℕ) (phase : EventGroup (2 * r + 1) Label → ℕ)
    (choice : EventGroup (2 * r + 1) Label → Bool) (stop : ℕ) (hr : 3 ≤ r)
    (groups : List (EventGroup (2 * r + 1) Label)) (cursor n b : ℕ)
    (hphase : ∀ G ∈ groups, phase G = 0 ∨ phase G = 2)
    (hchoice : ∀ G ∈ groups, choice G = false)
    (hfirst : ∀ G ∈ groups, r ≤ G.first)
    (hcursor : ∀ G ∈ groups, cursor ≤ groupStart r phase G)
    (hbefore : groups.Pairwise Before)
    (hn : n % r = cursor % r) (hb : b % r = cursor % r) :
    Aligned r n b (compile r phase choice stop cursor groups) := by
  induction groups generalizing cursor n b with
  | nil => exact aligned_normals r _ n b (hn.trans hb.symm)
  | cons G groups ih =>
    have hpG : phase G < r := by
      rcases hphase G (by simp) with h | h <;> omega
    have hfG := hfirst G (by simp)
    have hcG := hcursor G (by simp)
    obtain ⟨hGbefore, htailBefore⟩ := List.pairwise_cons.mp hbefore
    have hstartPhase : groupStart r phase G % r = phase G :=
      (repairStart_bounds r (phase G) G.first (by omega) hpG hfG).2.2
    have hgs : cursor + (groupStart r phase G - cursor) = groupStart r phase G := by omega
    have h1 : (n + (groupStart r phase G - cursor)) % r = groupStart r phase G % r := by
      have h := Nat.ModEq.add_right (groupStart r phase G - cursor) hn
      rwa [hgs] at h
    have hP : groupParking r phase G % r = 0 % r :=
      (Nat.modEq_zero_iff_dvd).mpr (groupParking_dvd r phase G)
    have h2 : (b + (groupStart r phase G - cursor) + groupParking r phase G) % r =
        groupStart r phase G % r := by
      have h := Nat.ModEq.add (Nat.ModEq.add_right (groupStart r phase G - cursor) hb) hP
      rwa [hgs, Nat.add_zero] at h
    have hhalf : 2 * (groupParking r phase G / 2) = groupParking r phase G :=
      Nat.mul_div_cancel' (groupParking_even r phase G)
    have hend : groupEnd r phase G = groupStart r phase G + groupParking r phase G + 1 := rfl
    have hendMod : (groupStart r phase G + 1) % r = groupEnd r phase G % r := by
      have h := Nat.ModEq.add_right 1
        (Nat.ModEq.add (Nat.ModEq.refl (n := r) (groupStart r phase G)) hP.symm)
      rw [Nat.add_zero] at h
      rw [hend]
      exact h
    have hcTail : ∀ H ∈ groups, groupEnd r phase G ≤ groupStart r phase H := by
      intro H hH
      have hpH : phase H < r := by
        rcases hphase H (List.mem_cons_of_mem G hH) with h | h <;> omega
      exact groupEnd_le_next r phase G H (by omega) hpG hpH hfG
        (hfirst H (List.mem_cons_of_mem G hH)) (hGbefore H hH)
    change Aligned r n b
      (List.replicate (groupStart r phase G - cursor) .normal ++
        List.replicate (groupParking r phase G / 2) (.parking (choice G)) ++
        .normal :: compile r phase choice stop (groupEnd r phase G) groups)
    rw [hchoice G (by simp)]
    apply aligned_append
    · apply aligned_append
      · exact aligned_normals r _ n b (hn.trans hb.symm)
      · apply aligned_parkings
        rw [normalCount_replicate_normal, h1, hstartPhase]
        exact hphase G (by simp)
    · rw [normalCount_append, batchCount_append, normalCount_replicate_normal,
        batchCount_replicate_normal, normalCount_replicate_parking, batchCount_replicate_parking,
        hhalf, Nat.add_zero, ← Nat.add_assoc]
      refine ⟨h1.trans h2.symm, ?_⟩
      apply ih (groupEnd r phase G)
        (n + (groupStart r phase G - cursor) + 1)
        (b + (groupStart r phase G - cursor) + groupParking r phase G + 1)
        (fun H hH => hphase H (List.mem_cons_of_mem G hH))
        (fun H hH => hchoice H (List.mem_cons_of_mem G hH))
        (fun H hH => hfirst H (List.mem_cons_of_mem G hH)) hcTail htailBefore
      · exact (Nat.ModEq.add_right 1 h1).trans hendMod
      · exact (Nat.ModEq.add_right 1 h2).trans hendMod

/-- The compiled program of `Asym25.Parking` is aligned. -/
theorem program_aligned (k M : ℕ) (hk : 2 ≤ k)
    (groups : List (EventGroup (2 * (k + 1) + 1) RepairAvoidance.ForbiddenPair))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before) :
    Aligned (k + 1) 0 0 (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups) :=
  compile_aligned (k + 1) (groupPhase k) (groupChoice k) M (by omega) groups 0 0 0
    (fun G _ => parkPhase_cases G.label) (fun _ _ => rfl) hfirst (fun _ _ => Nat.zero_le _)
    hbefore rfl rfl

/-- Jay Pantone's `proper_prefix_state` for an aligned program: the joint
index is named, uses the normal order, and its role phase is 0, 2 or the
translation modulo `k + 1`. -/
theorem tied_prefix_state (k : Nat) (program : List Macro)
    (hal : Aligned (k + 1) 0 0 program) (n : Nat)
    (hn : n < (programWord k program).length) :
    ∃ index : Index k, ∃ translation : Nat,
      index.2.1 = false ∧
      (index.1.val = 0 ∨ index.1.val = 2 ∨ index.1.val = translation % (k + 1)) ∧
      execute updateLabels ((programWord k program).take n) (id : Assignment) =
        (interpret k (List.range k) index).labels ∧
      ∀ a < k, ((programWord k program).take n).count a =
        translation + (interpret k (List.range k) index).phases a := by
  obtain ⟨before, instruction, after, ell, hprog, hell, htake⟩ := prefix_view k program n hn
  rw [htake]
  let s := normalCount before % (k + 1)
  have hs : s < k + 1 := Nat.mod_lt _ (by omega)
  have hboundary : execute updateLabels (programWord k before) (id : Assignment) =
      normalBoundary (List.range k) s := by
    rw [program_action]
    exact normalBoundary_mod k (normalCount before)
  have hsplit := aligned_split (k + 1) before instruction after 0 0 (hprog ▸ hal)
  cases instruction with
  | normal =>
    have hell' : ell < k := by simpa only [macroWord, List.length_range] using hell
    have htie : s = batchCount before % (k + 1) := by
      simpa only [SplitProp, Nat.zero_add] using hsplit
    refine ⟨(⟨s, hs⟩, false, ⟨ell, by omega⟩), batchCount before, rfl,
      Or.inr (Or.inr htie), ?_, ?_⟩
    · rw [execute_append, hboundary]
      change _ = execute updateLabels (pairPrefix (List.range k) ell)
        (normalBoundary (List.range k) s)
      rw [pairPrefix_first_half _ _ (by rw [List.length_range]; omega)]
      rfl
    · intro a ha
      rw [List.count_append, program_count k before a ha]
      change batchCount before + ((List.range k).take ell).count a =
        batchCount before + phase (List.range k) ell a
      have hlt : ell < (List.range k).length := by rw [List.length_range]; exact hell'
      simp only [phase, hlt, ↓reduceIte]
  | parking choice =>
    obtain ⟨hc, hs02⟩ := hsplit
    subst hc
    have hell' : ell < 2 * k := by
      simpa only [macroWord, List.length_append, List.length_reverse, menu_length,
        List.length_range, Nat.two_mul] using hell
    obtain ⟨completed, hcounts⟩ := parking_prefix_counts k false ell hell'
    have htie : s = 0 ∨ s = 2 := by
      simpa only [Nat.zero_add] using hs02
    refine ⟨(⟨s, hs⟩, false, ⟨ell, by omega⟩), batchCount before + completed, rfl, ?_, ?_, ?_⟩
    · rcases htie with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [execute_append, hboundary]
      rfl
    · intro a ha
      rw [List.count_append, program_count k before a ha]
      change batchCount before + (pairPrefix (menu (List.range k) false) ell).count a = _
      rw [hcounts a ha]
      exact (Nat.add_assoc _ _ _).symm

variable {M k : Nat} {α : Type}

/-- The tied envelope: a joint index of the normal order, a translation with
role phase 0, 2 or the translation modulo `k + 1`, and a mobile gap. -/
def EnvelopeT (background : Fin M → α) (initial : Option Nat → α)
    (initialCuts : Fin k → Fin M) (source : List α) : Prop :=
  ∃ index : Index k, ∃ translation : Nat,
    index.2.1 = false ∧
    (index.1.val = 0 ∨ index.1.val = 2 ∨ index.1.val = translation % (k + 1)) ∧
    ∃ cuts : Fin k → Fin M, ∃ gap : Nat,
      source = renderedBase background
        (fun p => initial ((interpret k (List.range k) index).labels p)) cuts gap ∧
      ∀ j, (cuts j).val = ((initialCuts j).val + translation +
        (interpret k (List.range k) index).phases j.val) % M

/-- Every row of an aligned program run from a cut that is a multiple of
`k + 1` lies in the tied envelope of the fixed background. -/
theorem tied_row_mem [NeZero M] (hM : 0 < M) (background : Fin M → α) (origin : Fin M)
    (horigin : k + 1 ∣ origin.val)
    (program : List Macro) (hal : Aligned (k + 1) 0 0 program) (word : List (Fin k))
    (hprogram : word.map Fin.val = programWord k program)
    (initial : Option Nat → α) (initialCuts : Fin k → Fin M)
    (gap : Nat) (sweeps : List Nat) (finalGap : Nat)
    (htrace : Trace hM (shiftedBackground background origin) word initial initialCuts gap
      sweeps finalGap)
    (satellite : α) (row : Row α)
    (hrow : row ∈ scheduleRows satellite sweeps
      (renderedBase (shiftedBackground background origin) initial initialCuts gap)) :
    EnvelopeT background initial initialCuts row.base := by
  obtain ⟨pre, target, tail, rowGap, hword, hbase⟩ :=
    row_prefix_state hM (shiftedBackground background origin) word initial initialCuts gap
      sweeps finalGap htrace satellite row hrow
  have hn : pre.length < (programWord k program).length := by
    rw [← hprogram, List.length_map, hword, List.length_append, List.length_cons]
    omega
  have htake : (programWord k program).take pre.length = pre.map Fin.val := by
    rw [← hprogram, hword, List.map_append, List.map_cons]
    apply List.take_left'
    simp only [List.length_map]
  obtain ⟨index, translation, hfalse, htie, hroles, hcounts⟩ :=
    tied_prefix_state k program hal pre.length hn
  rw [htake] at hroles hcounts
  have hlabels : executeLabels pre initial =
      fun p => initial ((interpret k (List.range k) index).labels p) := by
    rw [executeLabels_eq_execute]
    have h := LiteralEnvelope.execute_pullback (pre.map Fin.val) initial (id : Assignment)
    rw [hroles] at h
    exact h
  have hcuts : ∀ j, (executeCuts hM pre initialCuts j).val = ((initialCuts j).val + translation +
      (interpret k (List.range k) index).phases j.val) % M := by
    intro j
    rw [executeCuts_count]
    have hc := hcounts j.val j.isLt
    rw [List.count_map_of_injective pre Fin.val Fin.val_injective j] at hc
    rw [hc, Nat.add_assoc]
  obtain ⟨canonicalGap, hcanonical⟩ := rendered_base_canonical background origin
    (fun p => initial ((interpret k (List.range k) index).labels p))
    (executeCuts hM pre initialCuts) rowGap
  refine ⟨index, translation + origin.val, hfalse, ?_,
    (fun i => executeCuts hM pre initialCuts i + origin), canonicalGap, ?_, ?_⟩
  · rcases htie with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      obtain ⟨c, hc⟩ := horigin
      rw [h, hc, Nat.add_mul_mod_self_left]
  · rw [hbase, hlabels]
    exact hcanonical
  · intro j
    rw [Fin.val_add, hcuts, Nat.mod_add_mod]
    congr 1
    omega

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.compile_aligned
#print axioms CoefficientTwoPrecision.Asym25.tied_row_mem
