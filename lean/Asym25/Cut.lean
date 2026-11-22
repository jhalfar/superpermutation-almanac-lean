import Quantitative.RepairedContourCounts

/-!
# Exponent 25: the safe cut is a multiple of `r`

Jay Pantone chooses the safe cut of a candidate by counting: the radius-`L`
neighbourhoods of the events cover fewer than `M` residues
(`RepairIntervals.exists_safe_cut`). Among the `M / r` multiples of `r` one
is still free when `r (2L + 1) |events| < M` (`exists_aligned_cut`). With such
a cut the batch index of a row and its translation agree modulo `r`.

The four theorems after it are his `exists_grouped_circle`,
`exists_repair_program`, `construct_repair` and `construct_counted_repair`
with the cut as a parameter instead of an existential; the text is his, with
that one change. `construct_aligned_repair` puts them together.
-/

namespace CoefficientTwoPrecision.Asym25

open SuperpermutationUpperBound PositiveParking LiteralState StationaryCircle
open LiteralSchedule PositiveSchedule TargetTrace ClosedTrace MacroCatalogue FiniteProgram
open FiniteRoles BatchSafety RobustMatching SourceAlphabet OriginTransport
open SourceFamilyAdapter SourceAdvancement SourceUniverse ActualCyclicMatching
open RepairIntervals RepairGroups RepairProgram CyclicRepairSchedule

variable {M k : Nat} {Control Label : Type} [NeZero M] [DecidableEq Label]

/-- A multiple of `r` outside all event neighbourhoods. -/
theorem exists_aligned_cut (events : Finset (ZMod M × Label)) (L r : ℕ) (hr : 0 < r)
    (hdiv : r ∣ M) (hroom : r * ((2 * L + 1) * events.card) < M) :
    ∃ cut : ZMod M, r ∣ cut.val ∧ cut ∉ forbiddenCuts events L := by
  classical
  obtain ⟨q, hq⟩ := hdiv
  let multiples : Finset (ZMod M) := (Finset.range q).image (fun i : ℕ => ((r * i : ℕ) : ZMod M))
  have hval : ∀ i < q, (((r * i : ℕ) : ZMod M)).val = r * i := by
    intro i hi
    apply ZMod.val_natCast_of_lt
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_left hi hr
  have hinj : Set.InjOn (fun i : ℕ => ((r * i : ℕ) : ZMod M)) (Finset.range q : Set ℕ) := by
    intro i hi j hj heq
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_range.mp (Finset.mem_coe.mp hj)
    have h := congrArg ZMod.val heq
    dsimp only at h
    rw [hval i hi', hval j hj'] at h
    exact Nat.eq_of_mul_eq_mul_left hr h
  have hcardM : multiples.card = q := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsmall : (forbiddenCuts events L).card < multiples.card := by
    rw [hcardM]
    have h := forbiddenCuts_card events L
    have hlt : r * ((2 * L + 1) * events.card) < r * q := by rw [← hq]; exact hroom
    exact lt_of_le_of_lt h (Nat.lt_of_mul_lt_mul_left hlt)
  obtain ⟨cut, hcut, hfree⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hcut
  exact ⟨_, ⟨i, hval i (Finset.mem_range.mp hi)⟩, hfree⟩

/-- Construct the cut and all event groups from the finite cyclic event
set. Every group remains away from both ends of the cut-open circle. -/
theorem grouped_circle_at
    (events : Finset (ZMod M × Label)) (L : ℕ)
    (cut : ZMod M) (hcut : cut ∉ forbiddenCuts events L)
    (hseparated : Separated events L) :
    ∃ groups : List (EventGroup L Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      ∀ G ∈ groups, L < G.first ∧ G.last + L < M := by
  have hcoordinates := fun event hevent => event_coordinate_bounds events L cut hcut event hevent
  obtain ⟨groups, hperm, hbefore⟩ := group_events L (liftedEvents events cut)
    (lifted_labels events L cut hseparated)
  refine ⟨groups, hperm, hbefore, ?_⟩
  intro G hG
  have hcoord : ∀ t label, (t, label) ∈ G.events → L < t ∧ t + L < M := by
    intro t label ht
    have hflat : (t, label) ∈ groups.flatMap EventGroup.events :=
      List.mem_flatMap.mpr ⟨G, hG, ht⟩
    have hlift := hperm.mem_iff.mp hflat
    obtain ⟨event, hevent, heq⟩ := List.mem_map.mp hlift
    have hb := hcoordinates event (Finset.mem_toList.mp hevent)
    have htEq : (event.1 - cut).val = t := congrArg Prod.fst heq
    simpa only [htEq] using hb
  exact ⟨(hcoord G.first G.label G.first_mem).1,
    (hcoord G.last G.label G.last_mem).2⟩

/-- A complete finite schedule, with an actual macro list specified by
the compiler. Its use still requires the local role lemma to choose the
phase and parking order for each forbidden pair. -/
theorem repair_program_at
    (events : Finset (ZMod M × Label)) (r : ℕ) (hr : 0 < r)
    (hM : 0 < M) (cut : ZMod M) (hcut : cut ∉ forbiddenCuts events (2 * r + 1))
    (hseparated : Separated events (2 * r + 1))
    (phase : Label → ℕ) (hphase : ∀ label, phase label < r)
    (choice : Label → Bool) :
    ∃ groups : List (EventGroup (2 * r + 1) Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      (∀ G ∈ groups, 2 * r + 1 < G.first ∧ G.last + (2 * r + 1) < M) ∧
      batchCount (compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups) = M ∧
      normalCount (compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups) % r = M % r ∧
      changedBatches r phase groups ≤ 2 * (2 * r + 1) * events.card ∧
      ∃ beforeProgram : List Macro,
        compile r (fun G => phase G.label) (fun G => choice G.label) M 0 groups = beforeProgram ++ [.normal] := by
  obtain ⟨groups, hperm, hbefore, hbounds⟩ :=
    grouped_circle_at events (2 * r + 1) cut hcut hseparated
  have hfirst : ∀ G ∈ groups, r ≤ G.first := by
    intro G hG
    have h := (hbounds G hG).1
    omega
  have hfit : ∀ G ∈ groups, groupEnd r (fun H => phase H.label) G < M := by
    intro G hG
    obtain ⟨_, _, _, _, hend, _⟩ := rounded_repair_interval r (phase G.label) G.first G.last
      hr (hphase G.label) (hbounds G hG).1 G.first_le_last
    exact lt_of_le_of_lt hend (hbounds G hG).2
  obtain ⟨hbatch, hnormal, hlast⟩ := constructed_program_counts r M
    (fun G => phase G.label) (fun G => choice G.label) groups hr hM
    (fun G _ => hphase G.label) hfirst hfit hbefore
  have hchanged := changedBatches_bound r phase groups hr hphase hfirst
  rw [hperm.length_eq, lifted_length] at hchanged
  exact ⟨groups, hperm, hbefore, hbounds, hbatch, hnormal, hchanged, hlast⟩

theorem construct_repair_at (hk : 4 ≤ k) (hM : 2 * k ≤ M) (hdiv : k + 1 ∣ M)
    (controls old : List Nat) (hold : 0 < old.length)
    (hA : (controls ++ old).Nodup) (hsatellite : 9 ∉ controls ++ old)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ controls ++ old ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (hcontrols : ∀ c, embed c ∈ controls)
    (hprojection : CyclicEq old (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))))
    (assignment : Role k ≃ Control) (q : Fin k → Fin M)
    (hmono : StrictMono q) (hrobust : Robust (fun i => cutValue (q i)))
    (hzero : q ⟨0, by omega⟩ = 0)
    (events : Finset (ZMod M × Label))
    (cut : ZMod M) (hcut : cut ∉ forbiddenCuts events (2 * (k + 1) + 1))
    (hseparated : Separated events (2 * (k + 1) + 1))
    (phase : Label → Nat) (hphase : ∀ label, phase label < k + 1) (choice : Label → Bool) :
    ∃ groups : List (EventGroup (2 * (k + 1) + 1) Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      (∀ G ∈ groups, 2 * (k + 1) + 1 < G.first ∧ G.last + (2 * (k + 1) + 1) < M) ∧
      ∃ C : SourceContour (controls ++ old) (M + k - 1), ∃ gap sweeps finalGap,
        Trace (show 0 < M by omega) (shiftedBackground background (translationCut cut))
          (FiniteProgram.word k (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap sweeps finalGap ∧
        C.rows = scheduleRows 9 sweeps
          (renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
            (fun rank => q rank.rev) gap) ∧
        scheduleEnd sweeps (renderedBase (shiftedBackground background (translationCut cut))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap) =
            renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
              (fun rank => q rank.rev) gap ∧
        C.rows.Pairwise (fun first last => ¬ first.base.IsRotated last.base) ∧
        (∀ row ∈ C.rows, LiteralEnvelope.Envelope background (engineLabels embed assignment)
          (fun rank => q rank.rev) row.base) ∧
        (∀ row ∈ C.rows, InsertionAbove controls old row.base) ∧
        (C.rows.map Row.charge).sum = 2 * M * k ∧
        portGcd C.rows (M + k - 1) ≤ k := by
  classical
  obtain ⟨groups, hgroups, hbefore, hbounds, hbatch, hnormal, hchanged, lastPre, hlast⟩ :=
    repair_program_at events (k + 1) (by omega) (by omega) cut hcut hseparated phase hphase choice
  let program := compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups
  have hnormalDiv : k + 1 ∣ normalCount program := by
    apply Nat.dvd_of_mod_eq_zero
    change normalCount (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups) % (k + 1) = 0
    rw [hnormal, Nat.mod_eq_zero_of_dvd hdiv]
  obtain ⟨firstTail, hfirst⟩ := FiniteProgram.compile_starts_normal (k + 1) M (by omega) (by omega)
    (fun G => phase G.label) (fun G => choice G.label) groups
    (fun G _ => hphase G.label) (fun G hG => by have := (hbounds G hG).1; omega)
  obtain ⟨C, gap, sweeps, finalGap, htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩ :=
    LocalSourceContour.construct_program hk hM controls old hold hA hsatellite background embed
      hbackground hembed hdisjoint hsupport hcontrols hprojection assignment q hmono hrobust hzero
      (translationCut cut) program hbatch hnormalDiv firstTail lastPre hfirst hlast
  exact ⟨groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
    htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩

/-- The actual source constructor, with its exact charge, connector bound,
all original row properties, and the proved perturbation estimate. The
same contour and same trace witness every field in the conclusion. -/
theorem construct_counted_repair_at (hk : 5 ≤ k) (hM : 2 * k ≤ M) (hdiv : k + 1 ∣ M)
    (controls old : List Nat) (hold : 0 < old.length)
    (hA : (controls ++ old).Nodup) (hsatellite : 9 ∉ controls ++ old)
    (background : Fin M → Nat) (embed : Control → Nat)
    (hbackground : Function.Injective background) (hembed : Function.Injective embed)
    (hdisjoint : ∀ c i, embed c ≠ background i)
    (hsupport : ∀ a, a ∈ controls ++ old ↔ (∃ i, background i = a) ∨ ∃ c, embed c = a)
    (hcontrols : ∀ c, embed c ∈ controls)
    (hprojection : CyclicEq old (((List.finRange M).map background).filter (fun a => decide (a ∉ controls))))
    (assignment : Role k ≃ Control) (q : Fin k → Fin M)
    (hmono : StrictMono q) (hrobust : Robust (fun i => cutValue (q i)))
    (hzero : q ⟨0, by omega⟩ = 0)
    (K : Nat) (events : Finset (ZMod M × Label)) (hcount : events.card ≤ K)
    (cut : ZMod M) (hcut : cut ∉ forbiddenCuts events (2 * (k + 1) + 1))
    (hseparated : Separated events (2 * (k + 1) + 1))
    (phase : Label → Nat) (hphase : ∀ label, phase label < k + 1) (choice : Label → Bool) :
    ∃ groups : List (EventGroup (2 * (k + 1) + 1) Label),
      (groups.flatMap EventGroup.events).Perm (liftedEvents events cut) ∧
      groups.Pairwise Before ∧
      (∀ G ∈ groups, 2 * (k + 1) + 1 < G.first ∧ G.last + (2 * (k + 1) + 1) < M) ∧
      ∃ C : SourceContour (controls ++ old) (M + k - 1), ∃ gap sweeps finalGap,
        Trace (show 0 < M by omega) (shiftedBackground background (translationCut cut))
          (FiniteProgram.word k (compile (k + 1) (fun G => phase G.label) (fun G => choice G.label) M 0 groups))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap sweeps finalGap ∧
        C.rows = scheduleRows 9 sweeps
          (renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
            (fun rank => q rank.rev) gap) ∧
        scheduleEnd sweeps (renderedBase (shiftedBackground background (translationCut cut))
          (engineLabels embed assignment) (fun rank => q rank.rev) gap) =
            renderedBase (shiftedBackground background (translationCut cut)) (engineLabels embed assignment)
              (fun rank => q rank.rev) gap ∧
        C.rows.Pairwise (fun first last => ¬ first.base.IsRotated last.base) ∧
        (∀ row ∈ C.rows, LiteralEnvelope.Envelope background (engineLabels embed assignment)
          (fun rank => q rank.rev) row.base) ∧
        (∀ row ∈ C.rows, InsertionAbove controls old row.base) ∧
        (C.rows.map Row.charge).sum = 2 * M * k ∧
        portGcd C.rows (M + k - 1) ≤ k ∧
        |(C.rows.length : ℚ) - ((M * ((k - 1) * M + k * (k + 1) + 1) : Nat) : ℚ)| ≤
          ((10 * (k + 1) ^ 2 * K * M : Nat) : ℚ) := by
  classical
  obtain ⟨groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
      htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd⟩ :=
    construct_repair_at (by omega : 4 ≤ k) hM hdiv controls old hold hA hsatellite
      background embed hbackground hembed hdisjoint hsupport hcontrols hprojection assignment q hmono hrobust hzero
      events cut hcut hseparated phase hphase choice
  have hgroupCount : (groups.flatMap EventGroup.events).length ≤ K := by
    rw [hgroups.length_eq, lifted_length]
    exact hcount
  let localBackground := shiftedBackground background (translationCut cut)
  have hlocalInjective : Function.Injective localBackground :=
    shifted_injective background hbackground (translationCut cut)
  have hlocalDisjoint : ∀ c i, embed c ≠ localBackground i :=
    fun c i => hdisjoint c (i + translationCut cut)
  have hnd := SourceAlphabet.base_nodup localBackground embed hlocalInjective hembed hlocalDisjoint
    assignment (fun rank => q rank.rev) gap
  have hlen := SourceAlphabet.base_length localBackground embed hlocalInjective hembed hlocalDisjoint
    assignment (fun rank => q rank.rev) gap
  have herror := RepairedContourCounts.closed_row_error hk (by omega : k + 1 ≤ M) hdiv K groups phase hphase choice
    hbefore hbounds hgroupCount q hmono hrobust hzero localBackground (engineLabels embed assignment)
    gap sweeps finalGap htrace hnd hlen hclosed
  refine ⟨groups, hgroups, hbefore, hbounds, C, gap, sweeps, finalGap,
    htrace, hrows, hclosed, hsimple, henvelope, hinsertion, hcharge, hgcd, ?_⟩
  simpa only [hrows] using herror

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.exists_aligned_cut
#print axioms CoefficientTwoPrecision.Asym25.construct_counted_repair_at
