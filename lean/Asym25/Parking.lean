import Quantitative.CompiledEventAvoidance

/-!
# Exponent 25: parking with the normal order from role phase 0 or 2

Jay Pantone's repair starts a parking interval at the role phase at which
the forbidden control is mobile (`RepairAvoidance.mobilePhase`), which can
be any of the `r` phases, and chooses between two parking orders. Here the
parking order is always the normal one, and the interval starts at role
phase 0 or 2 (`parkPhase`). During pairs of the normal order and its
reverse a control stays in the slot it started in, the next slot of the
normal cycle, or the mobile role (`pair_prefix_index`); the two slots for
phase 0 and the two for phase 2 are different, so one of the two phases
keeps the control out of the forbidden slot (`parked_index_avoids`).

`aligned_repair_avoids` and `event_prefix_avoids` are his
`RepairAvoidance.compiled_repair_avoids` and
`CompiledEventAvoidance.event_prefix_avoids` for this choice; their proofs
follow his, with the new role lemma in place of `repeated_parking_avoids`.
-/

namespace CoefficientTwoPrecision.Asym25

open PositiveParking JointStates MacroCatalogue RepairIntervals RepairGroups
open RepairProgram RepairProgramSlices RepairAvoidance CompiledEventAvoidance

/-- A prefix of the normal order moves a role to itself, to the next role of
the normal cycle, or to the mobile role. -/
theorem range_index (m : ℕ) (p : Option ℕ) :
    roleIndex (execute PositiveParking.star (List.range m) p) = roleIndex p ∨
      roleIndex (execute PositiveParking.star (List.range m) p) = roleIndex p + 1 ∨
      roleIndex (execute PositiveParking.star (List.range m) p) = 0 := by
  rw [normal_batch_roleIndex]
  unfold cyclicSuccessor
  split
  · exact Or.inr (Or.inl rfl)
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- A prefix of a word followed by its reverse acts as a prefix of the word. -/
theorem pair_take (w : List ℕ) (t : ℕ) (p : Option ℕ) :
    ∃ m, execute PositiveParking.star ((w ++ w.reverse).take t) p =
      execute PositiveParking.star (w.take m) p := by
  by_cases ht : t ≤ w.length
  · exact ⟨t, by rw [List.take_append_of_le_length ht]⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = w.length + s := ⟨t - w.length, by omega⟩
    refine ⟨w.length - s, ?_⟩
    rw [List.take_length_add_append, List.take_reverse]
    have hsplit : w ++ (w.drop (w.length - s)).reverse =
        w.take (w.length - s) ++ (w.drop (w.length - s) ++ (w.drop (w.length - s)).reverse) := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hsplit, execute_append,
      execute_reverse_cancel PositiveParking.star PositiveParking.star_involutive]

theorem pair_prefix_index (k t : ℕ) (p : Option ℕ) :
    roleIndex (execute PositiveParking.star
        ((List.range k ++ (List.range k).reverse).take t) p) = roleIndex p ∨
      roleIndex (execute PositiveParking.star
        ((List.range k ++ (List.range k).reverse).take t) p) = roleIndex p + 1 ∨
      roleIndex (execute PositiveParking.star
        ((List.range k ++ (List.range k).reverse).take t) p) = 0 := by
  obtain ⟨m, hm⟩ := pair_take (List.range k) t p
  rw [hm, List.take_range]
  exact range_index _ p

/-- The same through any number of pairs: every pair returns all roles. -/
theorem repeated_pair_prefix_index (k n t : ℕ) (p : Option ℕ) :
    roleIndex (execute PositiveParking.star
        ((repeatWord n (List.range k ++ (List.range k).reverse)).take t) p) = roleIndex p ∨
      roleIndex (execute PositiveParking.star
        ((repeatWord n (List.range k ++ (List.range k).reverse)).take t) p) = roleIndex p + 1 ∨
      roleIndex (execute PositiveParking.star
        ((repeatWord n (List.range k ++ (List.range k).reverse)).take t) p) = 0 := by
  induction n generalizing t with
  | zero => exact Or.inl (by simp [repeatWord])
  | succ n ih =>
    rw [repeatWord]
    by_cases ht : t ≤ (List.range k ++ (List.range k).reverse).length
    · rw [List.take_append_of_le_length ht]
      exact pair_prefix_index k t p
    · obtain ⟨s, rfl⟩ : ∃ s, t = (List.range k ++ (List.range k).reverse).length + s :=
        ⟨t - (List.range k ++ (List.range k).reverse).length, by omega⟩
      rw [List.take_length_add_append, execute_append,
        execute_reverse_cancel PositiveParking.star PositiveParking.star_involutive]
      exact ih s

/-- The role phase at which the parking of a forbidden pair starts: 0, or 2
when the control is in the forbidden slot or one step before it at phase 0. -/
def parkPhase (pair : ForbiddenPair) : ℕ :=
  if pair.2 + 1 = roleIndex pair.1 ∨ pair.2 + 1 = roleIndex pair.1 + 1 then 2 else 0

theorem parkPhase_lt (k : ℕ) (hk : 2 ≤ k) (pair : ForbiddenPair) : parkPhase pair < k + 1 := by
  unfold parkPhase
  split <;> omega

theorem parkPhase_cases (pair : ForbiddenPair) : parkPhase pair = 0 ∨ parkPhase pair = 2 := by
  unfold parkPhase
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- After a number of normal batches congruent to the chosen phase, the
forbidden slot is neither the control's role nor the next one. -/
theorem parked_index_avoids (k : ℕ) (hk : 3 ≤ k) (role : Option ℕ) (slot s : ℕ)
    (hrole : roleIndex role ≤ k) (hslot : slot < k)
    (hs : s % (k + 1) = parkPhase (role, slot)) :
    slot + 1 ≠ (roleIndex role + s) % (k + 1) ∧
      slot + 1 ≠ (roleIndex role + s) % (k + 1) + 1 := by
  have hmod : (roleIndex role + s) % (k + 1) =
      (roleIndex role + parkPhase (role, slot)) % (k + 1) := by
    rw [Nat.add_mod, hs, Nat.mod_eq_of_lt (show roleIndex role < k + 1 by omega)]
  rw [hmod]
  unfold parkPhase
  dsimp only
  split
  · rename_i h
    by_cases hlt : roleIndex role + 2 < k + 1
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · rename_i h
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    omega

def groupPhase (k : ℕ) (G : EventGroup (2 * (k + 1) + 1) ForbiddenPair) : ℕ :=
  parkPhase G.label

def groupChoice (k : ℕ) (_ : EventGroup (2 * (k + 1) + 1) ForbiddenPair) : Bool := false

/-- Every update boundary in a group's compiled parking block avoids that
group's forbidden pair (Jay Pantone's `compiled_repair_avoids` for the
phases 0 and 2 and the normal parking order). -/
theorem aligned_repair_avoids (k M : ℕ) (hk : 3 ≤ k)
    (groups : List (EventGroup (2 * (k + 1) + 1) ForbiddenPair))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before)
    (G : EventGroup (2 * (k + 1) + 1) ForbiddenPair) (hG : G ∈ groups)
    (hrole : roleIndex G.label.1 ≤ k) (hslot : G.label.2 < k) :
    ∃ beforeProgram afterProgram : List Macro,
      compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups =
        beforeProgram ++
          List.replicate (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G)) ++
          .normal :: afterProgram ∧
      batchCount beforeProgram = groupStart (k + 1) (groupPhase k) G ∧
      ∀ t ≤ (programWord k
          (List.replicate (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G)))).length,
        let word := (programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
          ((programWord k beforeProgram).length + t)
        execute PositiveParking.star word G.label.1 ≠ some G.label.2 ∧
          (execute updateLabels word id) (some G.label.2) ≠ G.label.1 := by
  obtain ⟨beforeProgram, afterProgram, hprogram, hbatch, hphase⟩ :=
    repair_slice (k + 1) M (groupPhase k) (groupChoice k) groups (Nat.succ_pos _)
      (fun H _ => parkPhase_lt k (by omega) H.label) hfirst hbefore G hG
  refine ⟨beforeProgram, afterProgram, hprogram, hbatch, ?_⟩
  intro t ht
  let parking : List Macro := List.replicate
    (groupParking (k + 1) (groupPhase k) G / 2) (Macro.parking (groupChoice k G))
  have hword : programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups) =
      programWord k beforeProgram ++ (programWord k parking ++ programWord k (.normal :: afterProgram)) := by
    rw [hprogram, programWord_append, programWord_append]
    simp only [parking, List.append_assoc]
  have htake : (programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
      ((programWord k beforeProgram).length + t) =
      programWord k beforeProgram ++ (programWord k parking).take t := by
    rw [hword, List.take_length_add_append, List.take_append_of_le_length ht]
  have hstart : roleIndex (execute PositiveParking.star (programWord k beforeProgram) G.label.1) =
      (roleIndex G.label.1 + normalCount beforeProgram) % (k + 1) := by
    rw [program_position_action, normal_repeated_roleIndex k _ _ hrole]
  have hsafe := parked_index_avoids k hk G.label.1 G.label.2 (normalCount beforeProgram) hrole hslot
    hphase
  have hposition : execute PositiveParking.star
      ((programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take
        ((programWord k beforeProgram).length + t)) G.label.1 ≠ some G.label.2 := by
    rw [htake, execute_append]
    dsimp only [parking, groupChoice]
    rw [parking_programWord]
    change execute PositiveParking.star
      ((repeatWord (groupParking (k + 1) (groupPhase k) G / 2)
        (List.range k ++ (List.range k).reverse)).take t)
      (execute PositiveParking.star (programWord k beforeProgram) G.label.1) ≠ some G.label.2
    intro heq
    have hidx : roleIndex (execute PositiveParking.star
        ((repeatWord (groupParking (k + 1) (groupPhase k) G / 2)
          (List.range k ++ (List.range k).reverse)).take t)
        (execute PositiveParking.star (programWord k beforeProgram) G.label.1)) = G.label.2 + 1 :=
      congrArg roleIndex heq
    rcases repeated_pair_prefix_index k (groupParking (k + 1) (groupPhase k) G / 2) t
      (execute PositiveParking.star (programWord k beforeProgram) G.label.1) with h | h | h
    · rw [hidx, hstart] at h
      exact hsafe.1 h
    · rw [hidx, hstart] at h
      exact hsafe.2 h
    · rw [hidx] at h
      omega
  exact ⟨hposition, label_avoids_of_position_avoids _ _ _ hposition⟩

/-- Jay Pantone's `CompiledEventAvoidance.event_prefix_avoids` for the
aligned choice of phases. -/
theorem event_prefix_avoids (k M : Nat) (hk : 3 ≤ k)
    (groups : List (EventGroup (2 * (k + 1) + 1) ForbiddenPair))
    (hfirst : ∀ G ∈ groups, k + 1 ≤ G.first) (hbefore : groups.Pairwise Before)
    (event : Nat × ForbiddenPair) (hevent : event ∈ groups.flatMap EventGroup.events)
    (hrole : roleIndex event.2.1 ≤ k) (hslot : event.2.2 < k) (n : Nat) (htime : n / k = event.1) :
    (execute updateLabels
      ((programWord k (compile (k + 1) (groupPhase k) (groupChoice k) M 0 groups)).take n)
      id) (some event.2.2) ≠ event.2.1 := by
  obtain ⟨G, hG, hin⟩ := List.mem_flatMap.mp hevent
  obtain ⟨hleft, hright, hlabel⟩ := G.bounds event hin
  have hgroupRole : roleIndex G.label.1 ≤ k := by simpa only [hlabel] using hrole
  have hgroupSlot : G.label.2 < k := by simpa only [hlabel] using hslot
  obtain ⟨beforeProgram, afterProgram, hprogram, hbatch, havoid⟩ :=
    aligned_repair_avoids k M hk groups hfirst hbefore G hG hgroupRole hgroupSlot
  let start := groupStart (k + 1) (groupPhase k) G
  let parking := List.replicate (groupParking (k + 1) (groupPhase k) G / 2)
    (Macro.parking (groupChoice k G))
  have hstart : start ≤ G.first :=
    (repairStart_bounds (k + 1) (groupPhase k G) G.first (by omega)
      (parkPhase_lt k (by omega) G.label) (hfirst G hG)).2.1
  have hend : G.last + 1 ≤ start + groupParking (k + 1) (groupPhase k) G :=
    (parkingLength_bounds (k + 1) start G.last (by omega)
      (hstart.trans G.first_le_last)).1
  have hbeforeLength : (programWord k beforeProgram).length = k * start := by
    rw [programWord_length, hbatch]
  have hparkingLength : (programWord k parking).length =
      k * groupParking (k + 1) (groupPhase k) G := by
    rw [programWord_length, batchCount_replicate_parking]
    rw [Nat.mul_div_cancel' (groupParking_even (k + 1) (groupPhase k) G)]
  have hnLower : (programWord k beforeProgram).length ≤ n := by
    rw [hbeforeLength, Nat.mul_comm]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp
    rw [htime]
    exact hstart.trans hleft
  have hnUpper : n ≤ (programWord k beforeProgram).length + (programWord k parking).length := by
    have hn : n < (event.1 + 1) * k :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (by omega)
    have hb : event.1 + 1 ≤ start + groupParking (k + 1) (groupPhase k) G := by omega
    have hmul := Nat.mul_le_mul_right k hb
    rw [hbeforeLength, hparkingLength]
    nlinarith only [hn, hmul]
  have hwithin : n - (programWord k beforeProgram).length ≤ (programWord k parking).length := by
    omega
  have he := (havoid (n - (programWord k beforeProgram).length) hwithin).2
  have hindex : (programWord k beforeProgram).length +
      (n - (programWord k beforeProgram).length) = n := by omega
  simpa only [hindex, ← hlabel] using he

end CoefficientTwoPrecision.Asym25

#print axioms CoefficientTwoPrecision.Asym25.aligned_repair_avoids
#print axioms CoefficientTwoPrecision.Asym25.event_prefix_avoids
