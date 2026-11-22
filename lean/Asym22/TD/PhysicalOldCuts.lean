import Asym22.TD.GridBackground
import Quantitative.OldCircleProjection
import Asym22.LocalPos

/-!
Copy of Jay Pantone's `Quantitative/PhysicalOldCuts.lean` (release 9ccbe66) for the
transversal design of `Asym22.TD.ActiveGrid` (J. Halfar, November 2026):
namespace `CoefficientTwoPrecision.TD.PhysicalOldCuts`, imports of the copied modules
redirected to `Asym22.TD`. Added (November 2026, exponent-22 batch): the last four
theorems, which compare a foreign local cut with the local position of the same
control in the current background (`Asym22.LocalPos`); the two backgrounds differ
only by the active controls of the two blocks.

# Automatic original-cut projections for physical grid rows

The canonical one-control predicates below require no filter table as an
input. Membership in the active block separates its controls from guards,
and the role bijection separates the resident controls and mobile. Equal
cyclic rows therefore identify a common original cut for shared residents,
or identify a resident's original cut with a named guard's prescribed cut.
-/

namespace CoefficientTwoPrecision.TD.PhysicalOldCuts

open GuardCatalogue GridBackground GuardBackgrounds GuardCoordinates OldCircleProjection
open StationaryCircle

variable {m d A : Nat} {α : Type} [DecidableEq α]
variable (hA : 0 < A) (old : Fin m → α) (ho : Function.Injective old)
variable (label : Physical d A → α) (hl : Function.Injective label)
variable (hcross : ∀ p i, label p ≠ old i)

def residentControl (active : Active d A)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3)) (j : Fin (d + 2)) : Physical d A :=
  activeControl d A hA active (role (some j))

noncomputable def rowBase (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat) : List α :=
  ActualMatching.base (background hA old ho label hl hcross active guardCuts)
    (fun row => label (activeControl d A hA active row)) role localCuts gap

theorem resident_projection (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat) (target : Fin (d + 2)) :
    ∃ cut : Fin m, ∃ offset : Nat,
      offset < (block old (fun j => label (guardLabel d A hA active j)) guardCuts cut).length ∧
      (localCuts target).val = blockStart old (fun j => label (guardLabel d A hA active j)) guardCuts cut + offset ∧
      ((rowBase hA old ho label hl hcross active guardCuts role localCuts gap).filter
        (keepGuard old (label (residentControl hA active role target)))).IsRotated
          (SuperpermutationUpperBound.Transport.insertLetter ((List.finRange m).map old)
            (label (residentControl hA active role target)) cut.val) := by
  let embed := fun row => label (activeControl d A hA active row)
  let keep := keepGuard old (label (residentControl hA active role target))
  have hkeep (p : Physical d A) : keep (label p) = decide (p = residentControl hA active role target) :=
    keep_physical old label hl hcross _ p
  have hguard (j : Fin (guardNumber d A)) : keep (label (guardLabel d A hA active j)) = false := by
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role (some target)) j).symm
  have hresident (j : Fin (d + 2)) :
      keep (ActualMatching.resident embed role j) = decide (j = target) := by
    change keep (label (activeControl d A hA active (role (some j)))) = _
    rw [hkeep]
    simp only [residentControl, (activeControl_injective d A hA active).eq_iff,
      role.injective.eq_iff, Option.some.injEq]
  have hmobile : keep (embed (role none)) = false := by
    change keep (label (activeControl d A hA active (role none))) = false
    rw [hkeep]
    simp only [residentControl, (activeControl_injective d A hA active).eq_iff,
      role.injective.eq_iff, reduceCtorEq, decide_false]
  exact OldCircleProjection.resident_mobile_projection old _ guardCuts
    (background hA old ho label hl hcross active guardCuts)
    (background_word hA old ho label hl hcross active guardCuts)
    (ActualMatching.resident embed role)
    (ActualMatching.resident_injective embed (hl.comp (activeControl_injective d A hA active)) role)
    (fun j i => active_ne_background hA old ho label hl hcross active guardCuts (role (some j)) i)
    localCuts target (embed (role none)) gap keep (keepGuard_old old _) hguard hresident hmobile

theorem guard_projection (active : Active d A)
    (guardCuts : Fin (guardNumber d A) → Fin m)
    (role : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localCuts : Fin (d + 2) → Fin (m + guardNumber d A)) (gap : Nat)
    (target : Fin (guardNumber d A)) :
    ((rowBase hA old ho label hl hcross active guardCuts role localCuts gap).filter
      (keepGuard old (label (guardLabel d A hA active target)))).IsRotated
        (SuperpermutationUpperBound.Transport.insertLetter ((List.finRange m).map old)
          (label (guardLabel d A hA active target)) (guardCuts target).val) := by
  let embed := fun row => label (activeControl d A hA active row)
  let guard := fun j => label (guardLabel d A hA active j)
  let keep := keepGuard old (guard target)
  have hkeep (p : Physical d A) : keep (label p) = decide (p = guardLabel d A hA active target) :=
    keep_physical old label hl hcross _ p
  have hresident (j : Fin (d + 2)) : keep (ActualMatching.resident embed role j) = false := by
    change keep (label (activeControl d A hA active (role (some j)))) = false
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role (some j)) target)
  have hmobile : keep (embed (role none)) = false := by
    change keep (label (activeControl d A hA active (role none))) = false
    rw [hkeep]
    exact decide_eq_false_iff_not.mpr (activeControl_ne_guardLabel d A hA active (role none) target)
  exact OldCircleProjection.guard_mobile_projection old guard guardCuts
    (background hA old ho label hl hcross active guardCuts)
    (background_word hA old ho label hl hcross active guardCuts)
    (ActualMatching.resident embed role) localCuts target (embed (role none)) gap keep
    (keepGuard_old old _) (keepGuard_guard old guard
      (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i) target)
    hresident hmobile

theorem resident_guard_offset (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (guardTarget : Fin (guardNumber d A)) (residentTarget : Fin (d + 2))
    (htracked : guardLabel d A hA active guardTarget = residentControl hA foreign roleR residentTarget)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    ∃ e ≤ guardNumber d A,
      (localR residentTarget).val = (guardCutsL guardTarget).val + e := by
  have hleft := guard_projection hA old ho label hl hcross active guardCutsL roleL localL gapL guardTarget
  obtain ⟨cut, offset, hoff, hpos, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR residentTarget
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR residentTarget))
    (hcross _) _ _ _ hcyclic (guardCutsL guardTarget) cut hleft hright
  obtain ⟨e, he, hcoordinate⟩ := coordinate_offset old _ guardCutsR ho
    (hl.comp (guardLabel_injective d A hA foreign)) (fun j i => hcross _ i) cut offset hoff
  exact ⟨e, he, by simpa only [← hcut] using hpos.trans hcoordinate⟩

theorem common_resident_offsets (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (targetL targetR : Fin (d + 2))
    (htracked : residentControl hA active roleL targetL = residentControl hA foreign roleR targetR)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    ∃ cut : Fin m, ∃ eL ≤ guardNumber d A, ∃ eR ≤ guardNumber d A,
      (localL targetL).val = cut.val + eL ∧ (localR targetR).val = cut.val + eR := by
  obtain ⟨cutL, offsetL, hoffL, hposL, hleft⟩ := resident_projection hA old ho label hl hcross
    active guardCutsL roleL localL gapL targetL
  obtain ⟨cutR, offsetR, hoffR, hposR, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR targetR
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR targetR))
    (hcross _) _ _ _ hcyclic cutL cutR hleft hright
  obtain ⟨eL, heL, hcoordL⟩ := coordinate_offset old _ guardCutsL ho
    (hl.comp (guardLabel_injective d A hA active)) (fun j i => hcross _ i) cutL offsetL hoffL
  obtain ⟨eR, heR, hcoordR⟩ := coordinate_offset old _ guardCutsR ho
    (hl.comp (guardLabel_injective d A hA foreign)) (fun j i => hcross _ i) cutR offsetR hoffR
  exact ⟨cutL, eL, heL, eR, heR, hposL.trans hcoordL,
    by simpa only [← hcut] using hposR.trans hcoordR⟩

open ActiveGrid LocalPos

/-- A control that is a guard of both blocks has the same cut in both backgrounds. -/
theorem common_guard_cut (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (w j : Fin (guardNumber d A))
    (hlabel : guardLabel d A hA active w = guardLabel d A hA foreign j)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    guardCutsL w = guardCutsR j := by
  have hleft := guard_projection hA old ho label hl hcross active guardCutsL roleL localL gapL w
  have hright := guard_projection hA old ho label hl hcross foreign guardCutsR roleR localR gapR j
  rw [hlabel] at hleft
  exact same_old_cut old ho (label (guardLabel d A hA foreign j)) (hcross _) _ _ _ hcyclic
    (guardCutsL w) (guardCutsR j) hleft hright

omit [DecidableEq α] in
/-- The guards of the foreign block below a cut are the guards of the current block
below it, up to the `d + 3` active controls of the current block. -/
theorem before_le_add (active foreign : Active d A)
    (cutsL cutsR : Fin (guardNumber d A) → Fin m)
    (hcommon : ∀ w j, guardLabel d A hA active w = guardLabel d A hA foreign j →
      cutsL w = cutsR j) (c : Nat) :
    before cutsR c ≤ before cutsL c + (d + 3) := by
  classical
  let S := Finset.univ.filter (fun j : Fin (guardNumber d A) => (cutsR j).val < c)
  let inAct : Fin (guardNumber d A) → Prop := fun j =>
    guardLabel d A hA foreign j ∈ activeBlock (d + 3) A (by omega) hA active
  have h1 : (S.filter inAct).card ≤ d + 3 := by
    have h := Finset.card_le_card_of_injOn (s := S.filter inAct)
      (t := activeBlock (d + 3) A (by omega) hA active)
      (fun j => guardLabel d A hA foreign j)
      (fun j hj => by
        rw [Finset.mem_coe] at hj ⊢
        exact (Finset.mem_filter.mp hj).2)
      (fun a _ b _ h => guardLabel_injective d A hA foreign h)
    rwa [activeBlock_card] at h
  have h2 : (S.filter (fun j => ¬ inAct j)).card ≤ before cutsL c := by
    unfold before
    let f : Fin (guardNumber d A) → Fin (guardNumber d A) := fun j =>
      if h : guardLabel d A hA foreign j ∉ activeBlock (d + 3) A (by omega) hA active then
        guardEquiv d A hA active ⟨guardLabel d A hA foreign j, h⟩ else j
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      rw [Finset.mem_coe] at hj ⊢
      obtain ⟨hjS, hjn⟩ := Finset.mem_filter.mp hj
      have hjc := (Finset.mem_filter.mp hjS).2
      have hf : f j = guardEquiv d A hA active ⟨_, hjn⟩ := dif_pos hjn
      have hlab : guardLabel d A hA active (f j) = guardLabel d A hA foreign j := by
        rw [hf]
        simp [guardLabel]
      have hc := hcommon (f j) j hlab
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hc]
      exact hjc
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      have han := (Finset.mem_filter.mp ha).2
      have hbn := (Finset.mem_filter.mp hb).2
      have hfa : f a = guardEquiv d A hA active ⟨_, han⟩ := dif_pos han
      have hfb : f b = guardEquiv d A hA active ⟨_, hbn⟩ := dif_pos hbn
      rw [hfa, hfb] at hab
      have hv := congrArg Subtype.val ((guardEquiv d A hA active).injective hab)
      exact guardLabel_injective d A hA foreign hv
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) inAct
  change S.card ≤ _
  omega

/-- A foreign stationary control that is a guard of the current block: its foreign
local cut is its local position in the current background, up to `d + 4`. -/
theorem resident_guard_local (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (hinjL : Function.Injective guardCutsL)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (guardTarget : Fin (guardNumber d A)) (residentTarget : Fin (d + 2))
    (htracked : guardLabel d A hA active guardTarget = residentControl hA foreign roleR residentTarget)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    (((localR residentTarget).val : Int) - (localPos guardCutsL guardTarget).val).natAbs ≤ d + 4 := by
  have hleft := guard_projection hA old ho label hl hcross active guardCutsL roleL localL gapL guardTarget
  obtain ⟨cut, offset, hoff, hpos, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR residentTarget
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR residentTarget))
    (hcross _) _ _ _ hcyclic (guardCutsL guardTarget) cut hleft hright
  have hcommon : ∀ w j, guardLabel d A hA active w = guardLabel d A hA foreign j →
      guardCutsL w = guardCutsR j := fun w j h =>
    common_guard_cut hA old ho label hl hcross active foreign guardCutsL guardCutsR
      roleL roleR localL localR gapL gapR w j h hcyclic
  have hcommon' : ∀ j w, guardLabel d A hA foreign j = guardLabel d A hA active w →
      guardCutsR j = guardCutsL w := fun j w h => (hcommon w j h.symm).symm
  obtain ⟨hlo, hhi⟩ := block_index_bounds old (fun j => label (guardLabel d A hA foreign j))
    guardCutsR cut offset hoff
  have hLR := before_le_add hA foreign active guardCutsR guardCutsL hcommon' cut.val
  have hRL := before_le_add hA active foreign guardCutsL guardCutsR hcommon (cut.val + 1)
  have hs := before_succ_le guardCutsL hinjL cut.val
  rw [hpos, localPos_val, hcut]
  omega

/-- A control that is stationary in both rows: the two local cuts differ by at most `d + 4`. -/
theorem common_resident_local (active foreign : Active d A)
    (guardCutsL guardCutsR : Fin (guardNumber d A) → Fin m)
    (hinjL : Function.Injective guardCutsL) (hinjR : Function.Injective guardCutsR)
    (roleL roleR : FiniteRoles.Role (d + 2) ≃ Fin (d + 3))
    (localL localR : Fin (d + 2) → Fin (m + guardNumber d A)) (gapL gapR : Nat)
    (targetL targetR : Fin (d + 2))
    (htracked : residentControl hA active roleL targetL = residentControl hA foreign roleR targetR)
    (hcyclic : (rowBase hA old ho label hl hcross active guardCutsL roleL localL gapL).IsRotated
      (rowBase hA old ho label hl hcross foreign guardCutsR roleR localR gapR)) :
    (((localR targetR).val : Int) - (localL targetL).val).natAbs ≤ d + 4 := by
  obtain ⟨cutL, offsetL, hoffL, hposL, hleft⟩ := resident_projection hA old ho label hl hcross
    active guardCutsL roleL localL gapL targetL
  obtain ⟨cutR, offsetR, hoffR, hposR, hright⟩ := resident_projection hA old ho label hl hcross
    foreign guardCutsR roleR localR gapR targetR
  rw [htracked] at hleft
  have hcut := same_old_cut old ho (label (residentControl hA foreign roleR targetR))
    (hcross _) _ _ _ hcyclic cutL cutR hleft hright
  have hcommon : ∀ w j, guardLabel d A hA active w = guardLabel d A hA foreign j →
      guardCutsL w = guardCutsR j := fun w j h =>
    common_guard_cut hA old ho label hl hcross active foreign guardCutsL guardCutsR
      roleL roleR localL localR gapL gapR w j h hcyclic
  have hcommon' : ∀ j w, guardLabel d A hA foreign j = guardLabel d A hA active w →
      guardCutsR j = guardCutsL w := fun j w h => (hcommon w j h.symm).symm
  obtain ⟨hloL, hhiL⟩ := block_index_bounds old (fun j => label (guardLabel d A hA active j))
    guardCutsL cutL offsetL hoffL
  obtain ⟨hloR, hhiR⟩ := block_index_bounds old (fun j => label (guardLabel d A hA foreign j))
    guardCutsR cutR offsetR hoffR
  have h1 := before_le_add hA foreign active guardCutsR guardCutsL hcommon' cutL.val
  have h2 := before_le_add hA active foreign guardCutsL guardCutsR hcommon (cutL.val + 1)
  have h3 := before_le_add hA foreign active guardCutsR guardCutsL hcommon' (cutL.val + 1)
  have hsL := before_succ_le guardCutsL hinjL cutL.val
  have hsR := before_succ_le guardCutsR hinjR cutL.val
  rw [hposL, hposR]
  rw [← hcut] at hloR hhiR ⊢
  omega

end CoefficientTwoPrecision.TD.PhysicalOldCuts

#print axioms CoefficientTwoPrecision.TD.PhysicalOldCuts.resident_guard_offset
#print axioms CoefficientTwoPrecision.TD.PhysicalOldCuts.common_resident_offsets
#print axioms CoefficientTwoPrecision.TD.PhysicalOldCuts.resident_guard_local
#print axioms CoefficientTwoPrecision.TD.PhysicalOldCuts.common_resident_local
