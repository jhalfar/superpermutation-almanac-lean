import Quantitative.EnvelopeDegree

/-!
# Exponent 29: sorted target frames have few reconstructions

Jay Pantone's reconstruction count (`PositionalCatalogue.witness_count`) lists
one positional witness for every source omission, cyclic offset, target sum
slot and omitted target slot: `(d+2)(d+1)^2(2d)` witnesses for a pair of joint
states. A target frame is sorted, and this file uses that to show that the
witnesses repeat the same targets.

Fix the source omission `i` and the cyclic offset `c`. If the omitted target
slot `j` is not the anchor, the translation is fixed by the anchor, the
omitted cut takes one of at most `4d + 6` values (`omitted_value_mem`), and two
sorted targets with different omitted slots have different omitted cuts
(`omitted_value_lt`). If the anchor is omitted, the translation takes one of
at most `2(d+1)(d-1)` values (`translation_mem`), and equal translations force
equal offsets (`offset_eq_of_translation`).
-/

namespace CoefficientTwoPrecision.Asym29

open FiniteRoles BatchSafety ActualCyclicMatching AffineReconstruction

variable {M d : Nat} [NeZero M]

/-- Every phase correction is zero or one. -/
def IsBit (E : Fin (d + 2) → ZMod M) : Prop := ∀ p, E p = 0 ∨ E p = 1

/-- A sorted anchored tuple whose cuts add up to twice one of them. -/
def Framed (q : Fin (d + 2) → Fin M) : Prop :=
  StrictMono q ∧ q 0 = 0 ∧
    ∃ s : Fin (d + 2), s ≠ 0 ∧ ∑ p, cutValue (q p) = 2 * cutValue (q s)

/-- The retained target cuts, translated by `δ`, are the retained source
cuts `S` corrected by the target phases `E`. -/
def Matched (S E : Fin (d + 2) → ZMod M) (i j : Fin (d + 2)) (c : Fin (d + 1))
    (q : Fin (d + 2) → Fin M) (δ : ZMod M) : Prop :=
  ∀ x : Fin (d + 1),
    cutValue (q (j.succAbove x)) + δ = S (i.succAbove (x + c)) - E (j.succAbove x)

omit [NeZero M] in
theorem val_le_succ_of_cast {a b : ℕ} (ha : a < M) (hb : b < M) (hb0 : 0 < b)
    {u v : ZMod M} (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1)
    (h : (a : ZMod M) = (b : ZMod M) + (u - v)) : a ≤ b + 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · have h' : (a : ZMod M) = (b : ZMod M) := by simpa using h
    have := (ZMod.natCast_eq_natCast_iff' a b M).mp h'
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    omega
  · have h' : ((a + 1 : ℕ) : ZMod M) = (b : ZMod M) := by
      push_cast
      linear_combination h
    have := (ZMod.natCast_eq_natCast_iff' (a + 1) b M).mp h'
    rw [Nat.mod_eq_of_lt hb] at this
    rcases Nat.lt_or_ge (a + 1) M with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at this
      omega
    · have hM : a + 1 = M := by omega
      rw [hM, Nat.mod_self] at this
      omega
  · have h' : (a : ZMod M) = ((b + 1 : ℕ) : ZMod M) := by
      push_cast
      linear_combination h
    have := (ZMod.natCast_eq_natCast_iff' a (b + 1) M).mp h'
    rw [Nat.mod_eq_of_lt ha] at this
    have := Nat.mod_le (b + 1) M
    omega
  · have h' : (a : ZMod M) = (b : ZMod M) := by simpa using h
    have := (ZMod.natCast_eq_natCast_iff' a b M).mp h'
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    omega

theorem Framed.pos {q : Fin (d + 2) → Fin M} (hq : Framed q) {p : Fin (d + 2)}
    (hp : p ≠ 0) : 0 < (q p).val := by
  have h := hq.1 (Fin.pos_iff_ne_zero.mpr hp)
  rw [hq.2.1] at h
  have := Fin.lt_def.mp h
  simpa using this

theorem cutValue_zero_of {q : Fin (d + 2) → Fin M} (hz : q 0 = 0) :
    cutValue (q 0) = (0 : ZMod M) := by
  simp only [hz, cutValue, Fin.val_zero, Nat.cast_zero]

/-- With the anchor retained, the translation is fixed by the anchor. -/
theorem translation_of_anchor {S E : Fin (d + 2) → ZMod M} {i j : Fin (d + 2)}
    {c : Fin (d + 1)} {q : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hm : Matched S E i j c q δ) (hz : q 0 = 0) (hj : j ≠ 0) :
    δ = S (i.succAbove (0 + c)) - E 0 := by
  have h := hm 0
  rw [Fin.succAbove_ne_zero_zero hj] at h
  have h0 := cutValue_zero_of (M := M) hz
  linear_combination h - h0

/-- Two sorted targets with the same source omission and offset: the one with
the smaller omitted slot has the smaller omitted cut. -/
theorem omitted_value_lt {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    {i j j' : Fin (d + 2)} {c : Fin (d + 1)} {q q' : Fin (d + 2) → Fin M} {δ δ' : ZMod M}
    (hq : Framed q) (hq' : Framed q')
    (hm : Matched S E i j c q δ) (hm' : Matched S E i j' c q' δ')
    (hj : j ≠ 0) (hjj : j < j') : q j < q' j' := by
  have hj' : j' ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) hjj)
  have hδ := translation_of_anchor hm hq.2.1 hj
  have hδ' := translation_of_anchor hm' hq'.2.1 hj'
  have hjlt : j.val < d + 1 := by
    have h1 := j'.isLt
    have h2 := Fin.lt_def.mp hjj
    omega
  let x : Fin (d + 1) := ⟨j.val, hjlt⟩
  have hx : x.castSucc = j := Fin.ext rfl
  have h1 : j.succAbove x = x.succ := Fin.succAbove_of_le_castSucc j x (by rw [hx])
  have h2 : j'.succAbove x = j := by
    rw [Fin.succAbove_of_castSucc_lt j' x (by rw [hx]; exact hjj), hx]
  have e1 := hm x
  have e2 := hm' x
  rw [h1] at e1
  rw [h2] at e2
  have key : (((q x.succ).val : ℕ) : ZMod M) = (((q' j).val : ℕ) : ZMod M) + (E j - E x.succ) := by
    simp only [cutValue] at e1 e2
    linear_combination e1 - e2 - hδ + hδ'
  have hle := val_le_succ_of_cast (q x.succ).isLt (q' j).isLt (hq'.pos hj) (hE j) (hE x.succ) key
  have ha : q j < q x.succ := hq.1 (by rw [← hx]; exact Fin.castSucc_lt_succ)
  have hb : q' j < q' j' := hq'.1 hjj
  have ha' := Fin.lt_def.mp ha
  have hb' := Fin.lt_def.mp hb
  exact Fin.lt_def.mpr (by omega)

/-- With the anchor retained, the omitted slot and its cut determine the target. -/
theorem frame_eq_of_omitted {S E : Fin (d + 2) → ZMod M} {i j : Fin (d + 2)}
    {c : Fin (d + 1)} {q q' : Fin (d + 2) → Fin M} {δ δ' : ZMod M}
    (hz : q 0 = 0) (hz' : q' 0 = 0)
    (hm : Matched S E i j c q δ) (hm' : Matched S E i j c q' δ')
    (hj : j ≠ 0) (h : q j = q' j) : q = q' := by
  have hδ := translation_of_anchor hm hz hj
  have hδ' := translation_of_anchor hm' hz' hj
  funext p
  by_cases hp : p = j
  · rw [hp, h]
  · obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hp
    apply cutValue_injective
    linear_combination hm x - hm' x - hδ + hδ'

/-- With the anchor omitted, the offset and the translation determine the target. -/
theorem frame_eq_of_translation {S E : Fin (d + 2) → ZMod M} {i : Fin (d + 2)}
    {c : Fin (d + 1)} {q q' : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hz : q 0 = 0) (hz' : q' 0 = 0)
    (hm : Matched S E i 0 c q δ) (hm' : Matched S E i 0 c q' δ) : q = q' := by
  funext p
  by_cases hp : p = 0
  · rw [hp, hz, hz']
  · obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq hp
    apply cutValue_injective
    linear_combination hm x - hm' x

/-! ## The omitted cut takes few values -/

/-- The possible values of the omitted cut, for a fixed source omission and offset. -/
noncomputable def valueSet (S E : Fin (d + 2) → ZMod M) (i : Fin (d + 2)) (c : Fin (d + 1)) :
    Finset (ZMod M) := by
  classical
  exact
    (Finset.univ.image (fun b : Fin 2 =>
      (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) -
        (∑ p, E p) + ((b.val : ℕ) : ZMod M))) ∪
    (Finset.univ.image (fun eb : Fin (d + 1) × Fin 4 =>
      2 * (S (i.succAbove (eb.1 + c)) - (S (i.succAbove (0 + c)) - E 0)) -
        (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) +
        (∑ p, E p) - ((eb.2.val : ℕ) : ZMod M)))

omit [NeZero M] in
theorem valueSet_card (S E : Fin (d + 2) → ZMod M) (i : Fin (d + 2)) (c : Fin (d + 1)) :
    (valueSet S E i c).card ≤ 4 * d + 6 := by
  classical
  unfold valueSet
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 2)))
    (f := fun b : Fin 2 =>
      (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) -
        (∑ p, E p) + ((b.val : ℕ) : ZMod M))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (d + 1) × Fin 4)))
    (f := fun eb : Fin (d + 1) × Fin 4 =>
      2 * (S (i.succAbove (eb.1 + c)) - (S (i.succAbove (0 + c)) - E 0)) -
        (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) +
        (∑ p, E p) - ((eb.2.val : ℕ) : ZMod M))
  simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_prod] at h1 h2
  omega

theorem omitted_value_mem {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    {i j : Fin (d + 2)} {c : Fin (d + 1)} {q : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hq : Framed q) (hm : Matched S E i j c q δ) (hj : j ≠ 0) :
    cutValue (q j) ∈ valueSet S E i c := by
  classical
  obtain ⟨_, hz, s, hs, hsum⟩ := hq
  have hδ := translation_of_anchor hm hz hj
  subst hδ
  have hsplit : ∑ p, cutValue (q p) = cutValue (q j) + ∑ x, cutValue (q (j.succAbove x)) :=
    Fin.sum_univ_succAbove _ j
  have hEsplit : ∑ p, E p = E j + ∑ x, E (j.succAbove x) := Fin.sum_univ_succAbove _ j
  have hx : ∀ x, cutValue (q (j.succAbove x)) =
      (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0)) - E (j.succAbove x) :=
    fun x => by linear_combination hm x
  have hsumx : ∑ x, cutValue (q (j.succAbove x)) =
      (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) -
        ∑ x, E (j.succAbove x) := by
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib]
  unfold valueSet
  by_cases hsj : s = j
  · subst hsj
    have hval : cutValue (q s) =
        (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) -
          (∑ p, E p) + E s := by
      linear_combination hsplit - hsum + hsumx + hEsplit
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    rcases hE s with h0 | h1
    · exact ⟨0, Finset.mem_univ _, by rw [hval, h0]; simp⟩
    · exact ⟨1, Finset.mem_univ _, by rw [hval, h1]; simp⟩
  · obtain ⟨e, rfl⟩ := Fin.exists_succAbove_eq hsj
    have hval : cutValue (q j) =
        2 * (S (i.succAbove (e + c)) - (S (i.succAbove (0 + c)) - E 0)) -
          (∑ x : Fin (d + 1), (S (i.succAbove (x + c)) - (S (i.succAbove (0 + c)) - E 0))) +
          (∑ p, E p) - (E j + 2 * E (j.succAbove e)) := by
      linear_combination hsum - hsplit - hsumx - hEsplit + 2 * hx e
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    rcases hE j with h0 | h1 <;> rcases hE (j.succAbove e) with g0 | g1
    · exact ⟨(e, 0), Finset.mem_univ _, by rw [hval, h0, g0]; simp⟩
    · exact ⟨(e, 2), Finset.mem_univ _, by rw [hval, h0, g1]; simp⟩
    · exact ⟨(e, 1), Finset.mem_univ _, by rw [hval, h1, g0]; simp⟩
    · exact ⟨(e, 3), Finset.mem_univ _, by rw [hval, h1, g1]; simp; ring⟩

/-! ## The anchor omitted: few translations, one offset each -/

theorem zmod_root_count (n : ℕ) (hn : 0 < n) (v : ZMod M) :
    (Finset.univ.filter (fun δ : ZMod M => (n : ZMod M) * δ = v)).card ≤ n := by
  classical
  have hM : 0 < M := NeZero.pos M
  have h := FiniteFibers.fin_root_count M hM (n : ℤ) (v.val : ℤ) (by exact_mod_cast hn.ne')
  refine (Finset.card_le_card_of_injOn (fun δ : ZMod M => (⟨δ.val, ZMod.val_lt δ⟩ : Fin M))
    ?_ ?_).trans (by simpa using h)
  · intro δ hδ
    have hδ' := (Finset.mem_filter.mp hδ).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
    push_cast
    simpa only [ZMod.natCast_val, ZMod.cast_id', id] using hδ'
  · intro δ _ δ' _ heq
    exact ZMod.val_injective M (congrArg Fin.val heq)

/-- The possible values of `(d - 1) δ` when the anchor is omitted. -/
noncomputable def rhsSet (S E : Fin (d + 2) → ZMod M) (i : Fin (d + 2)) : Finset (ZMod M) := by
  classical
  exact Finset.univ.image (fun fb : Fin (d + 1) × Fin 2 =>
    (∑ y : Fin (d + 1), S (i.succAbove y)) - (∑ x : Fin (d + 1), E x.succ) -
      2 * S (i.succAbove fb.1) + 2 * ((fb.2.val : ℕ) : ZMod M))

noncomputable def translationSet (S E : Fin (d + 2) → ZMod M) (i : Fin (d + 2)) :
    Finset (ZMod M) := by
  classical
  exact Finset.univ.filter (fun δ : ZMod M => ((d - 1 : ℕ) : ZMod M) * δ ∈ rhsSet S E i)

theorem translationSet_card (hd : 2 ≤ d) (S E : Fin (d + 2) → ZMod M) (i : Fin (d + 2)) :
    (translationSet S E i).card ≤ (d + 1) * 2 * (d - 1) := by
  classical
  have hR : (rhsSet S E i).card ≤ (d + 1) * 2 := by
    unfold rhsSet
    refine Finset.card_image_le.trans ?_
    simp [Finset.card_univ, Fintype.card_prod]
  refine (FiniteFibers.card_le_of_fiber_bound (translationSet S E i) (rhsSet S E i)
    (fun δ => ((d - 1 : ℕ) : ZMod M) * δ) (d - 1) ?_ ?_).trans
    (Nat.mul_le_mul_right _ hR)
  · intro δ hδ
    exact (Finset.mem_filter.mp hδ).2
  · intro v _
    refine (Finset.card_le_card ?_).trans (zmod_root_count (d - 1) (by omega) v)
    intro δ hδ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hδ).2⟩

theorem translation_mem (hd : 2 ≤ d) {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    {i : Fin (d + 2)} {c : Fin (d + 1)} {q : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hq : Framed q) (hm : Matched S E i 0 c q δ) : δ ∈ translationSet S E i := by
  classical
  obtain ⟨_, hz, s, hs, hsum⟩ := hq
  obtain ⟨a, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hs
  have h0 : ∀ x : Fin (d + 1), (0 : Fin (d + 2)).succAbove x = x.succ :=
    fun x => congrFun Fin.succAbove_zero x
  have hx : ∀ x : Fin (d + 1), cutValue (q x.succ) =
      S (i.succAbove (x + c)) - E x.succ - δ := by
    intro x
    have h := hm x
    rw [h0] at h
    linear_combination h
  have hsplit : ∑ p, cutValue (q p) = cutValue (q 0) + ∑ x : Fin (d + 1), cutValue (q x.succ) :=
    Fin.sum_univ_succ _
  have hre : ∑ x : Fin (d + 1), S (i.succAbove (x + c)) = ∑ y : Fin (d + 1), S (i.succAbove y) :=
    Equiv.sum_comp (Equiv.addRight c) (fun y => S (i.succAbove y))
  have hsumx : ∑ x : Fin (d + 1), cutValue (q x.succ) =
      (∑ y : Fin (d + 1), S (i.succAbove y)) - (∑ x : Fin (d + 1), E x.succ) -
        ((d + 1 : ℕ) : ZMod M) * δ := by
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hre, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((d + 1 : ℕ) : ZMod M) = ((d - 1 : ℕ) : ZMod M) + 2 := by
    have h : d + 1 = (d - 1) + 2 := by omega
    calc
      ((d + 1 : ℕ) : ZMod M) = (((d - 1) + 2 : ℕ) : ZMod M) := congrArg _ h
      _ = ((d - 1 : ℕ) : ZMod M) + 2 := by push_cast; ring
  have hzero := cutValue_zero_of (M := M) hz
  have hval : ((d - 1 : ℕ) : ZMod M) * δ =
      (∑ y : Fin (d + 1), S (i.succAbove y)) - (∑ x : Fin (d + 1), E x.succ) -
        2 * S (i.succAbove (a + c)) + 2 * E a.succ := by
    linear_combination hsplit - hsum + hsumx + hzero - 2 * hx a - δ * hcast
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold rhsSet
  apply Finset.mem_image.mpr
  rcases hE a.succ with g0 | g1
  · exact ⟨(a + c, 0), Finset.mem_univ _, by rw [hval, g0]; simp⟩
  · exact ⟨(a + c, 1), Finset.mem_univ _, by rw [hval, g1]; simp⟩

/-- With the anchor omitted, two sorted targets with the same translation have
the same cyclic offset. -/
theorem offset_eq_of_translation (hd : 2 ≤ d) {S E : Fin (d + 2) → ZMod M} (hE : IsBit E)
    {i : Fin (d + 2)} {c c' : Fin (d + 1)} {q q' : Fin (d + 2) → Fin M} {δ : ZMod M}
    (hq : Framed q) (hq' : Framed q')
    (hm : Matched S E i 0 c q δ) (hm' : Matched S E i 0 c' q' δ) : c = c' := by
  by_contra hne
  have h0 : ∀ x : Fin (d + 1), (0 : Fin (d + 2)).succAbove x = x.succ :=
    fun x => congrFun Fin.succAbove_zero x
  let h : Fin (d + 1) := c' - c
  have hh : h ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hrel : ∀ x : Fin (d + 1), cutValue (q' x.succ) =
      cutValue (q (x + h).succ) + (E (x + h).succ - E x.succ) := by
    intro x
    have e1 := hm' x
    have e2 := hm (x + h)
    rw [h0] at e1 e2
    have hidx : x + h + c = x + c' := by
      show x + (c' - c) + c = x + c'
      rw [add_assoc, sub_add_cancel]
    rw [hidx] at e2
    linear_combination e1 - e2
  let x0 : Fin (d + 1) := -h
  let x1 : Fin (d + 1) := x0 - 1
  have hx0 : x0 + h = 0 := neg_add_cancel h
  have hx0ne : x0 ≠ 0 := neg_ne_zero.mpr hh
  have hx1 : x1 + h = -1 := by
    show -h - 1 + h = -1
    abel
  have hlt : x1 < x0 := Fin.sub_one_lt_iff.mpr (Fin.pos_iff_ne_zero.mpr hx0ne)
  -- q' at x0 is close to q at slot 1
  have rA := hrel x0
  rw [hx0] at rA
  have hA := val_le_succ_of_cast (q' x0.succ).isLt (q (0 : Fin (d + 1)).succ).isLt
    (hq.pos (Fin.succ_ne_zero _)) (hE (0 : Fin (d + 1)).succ) (hE x0.succ)
    (by simp only [cutValue] at rA; linear_combination rA)
  -- q at the last slot is close to q' at x1
  have rB := hrel x1
  rw [hx1] at rB
  have hB := val_le_succ_of_cast (q (-1 : Fin (d + 1)).succ).isLt (q' x1.succ).isLt
    (hq'.pos (Fin.succ_ne_zero _)) (hE x1.succ) (hE (-1 : Fin (d + 1)).succ)
    (by simp only [cutValue] at rB; linear_combination -rB)
  have hC : q' x1.succ < q' x0.succ := hq'.1 (Fin.succ_lt_succ_iff.mpr hlt)
  have hC' := Fin.lt_def.mp hC
  let p2 : Fin (d + 2) := ⟨2, by omega⟩
  have hD1 : q (0 : Fin (d + 1)).succ < q p2 := hq.1 (Fin.lt_def.mpr (by simp [p2]))
  have hD2 : q p2 < q (-1 : Fin (d + 1)).succ :=
    hq.1 (Fin.lt_def.mpr (by simp [p2, Fin.coe_neg_one]; omega))
  have hD1' := Fin.lt_def.mp hD1
  have hD2' := Fin.lt_def.mp hD2
  omega

end CoefficientTwoPrecision.Asym29
