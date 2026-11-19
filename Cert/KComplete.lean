import Cert.KEngine
import LowerBounds.K16Sound
import Mathlib.Tactic

/-!
# The kernel engine is complete

`CEnc enc crk nx wrec ws`: what the proof needs to know about the records, for a coding `enc` of the words
on 7 symbols by numbers, a class rank `crk` and a next entry `nx`: the class rank tells rotation classes
apart, `nx` is the door, the slots of `wrec q` are rows (`OrbOK`) and list the successors of weight 3 and 4,
the first field of `wrec q` is the class rank of the next block, and `ws` is the row of the start word.

`kstmt16_of_searchC`: if the whole search (`searchC` with the empty list) does not answer `none`, then
`KStmt16 7 js code fN fS cut` holds.  The proof is that of `K16Sound.lean`, with marks that are a number
and are never given back: a call answers `none`, or `some` of a suffix of the list it was given
(`*_suffix`), so with the empty list `some []`.
-/

namespace SuperpermLowerBounds
namespace Cert

open S (PermW WLink DoorEq)
open PS (TRow PCont LinkK IsSeq relabSeq)
open KS (fK KAlong RuleK)
open K16 (NoJSAlong KStmt16 tau2 permW_tau2)

/-! ### Results are suffixes of the list -/

/-- `o` is `none`, or `some` of a suffix of `L`. -/
def SufR (L : List CS) (o : Res) : Prop := ∀ L', o = some L' → L' <:+ L

theorem sufR_some (L : List CS) : SufR L (some L) := fun L' h => by
  cases h
  exact List.suffix_refl L

theorem sufR_none (L : List CS) : SufR L none := fun _ h => by cases h

theorem bnd_none (k : List CS → Res) : bnd none k = none := rfl

theorem bnd_some (L : List CS) (k : List CS → Res) : bnd (some L) k = k L := rfl

theorem sufR_bnd {L : List CS} {o : Res} {k : List CS → Res} (ho : SufR L o)
    (hk : ∀ L1, L1 <:+ L → SufR L1 (k L1)) : SufR L (bnd o k) := by
  cases o with
  | none => exact sufR_none L
  | some L1 =>
    intro L' h
    exact ((hk L1 (ho L1 rfl)) L' h).trans (ho L1 rfl)

theorem sufR_cond {L : List CS} (c : Bool) {a b : Res} (ha : SufR L a) (hb : SufR L b) :
    SufR L (bif c then a else b) := by
  cases c
  · exact hb
  · exact ha

theorem walkC_succ (G : Nat → Nat → Nat → List CS → Res) (n mk x B : Nat) (L : List CS) :
    walkC G (n + 1) mk x B L =
      (bif Nat.beq mk 0 then some L
      else bif Nat.testBit B (x % 1024) then some L
      else bnd (bif Nat.beq (mk % 2) 1 then G n (x / 1024 % 8192) (B ||| 2 ^ (x % 1024)) L else some L)
        (fun L1 => walkC G n (mk / 2) (x / 8388608) (B ||| 2 ^ (x % 1024)) L1)) := rfl

theorem succC_succ (G : Nat → Nat → Nat → List CS → Res) (js : Bool) (cq mk n x B : Nat)
    (L : List CS) :
    succC G js cq mk (n + 1) x B L =
      bnd (walkC G 6 (jsC js cq (x % 1024) mk) (x % P138) B L)
        (fun L1 => succC G js cq mk n (x / P138) B L1) := rfl

theorem walkC_suffix (G : Nat → Nat → Nat → List CS → Res) (hG : ∀ n e B L, SufR L (G n e B L)) :
    ∀ (n mk x B : Nat) (L : List CS), SufR L (walkC G n mk x B L) := by
  intro n
  induction n with
  | zero => intro mk x B L; exact sufR_some L
  | succ n ih =>
    intro mk x B L
    rw [walkC_succ]
    refine sufR_cond _ (sufR_some L) (sufR_cond _ (sufR_some L) (sufR_bnd ?_ ?_))
    · exact sufR_cond _ (hG _ _ _ _) (sufR_some L)
    · intro L1 h1 L' h'
      exact ih _ _ _ L1 L' h'

theorem succC_suffix (G : Nat → Nat → Nat → List CS → Res) (hG : ∀ n e B L, SufR L (G n e B L))
    (js : Bool) (cq mk : Nat) : ∀ (n x B : Nat) (L : List CS), SufR L (succC G js cq mk n x B L) := by
  intro n
  induction n with
  | zero => intro x B L; exact sufR_some L
  | succ n ih =>
    intro x B L
    rw [succC_succ]
    refine sufR_bnd (walkC_suffix G hG _ _ _ _ _) ?_
    intro L1 h1 L' h'
    exact ih _ _ L1 L' h'

section Rule

variable (code mask : Nat → Nat → Nat → Nat) (fN fS : Nat → Nat → Nat → Int)
  (cut : Nat → Nat → Nat → Int → Int → Bool) (wrec : Nat → Nat) (js : Bool)

theorem bodyC_suffix (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hG : ∀ t r d m M q B L, SufR L (G t r d m M q B L)) (t r d : Nat) (m M : Int) (q B : Nat)
    (L : List CS) : SufR L (bodyC code mask fN fS cut wrec js G t r d m M q B L) := by
  unfold bodyC
  refine sufR_cond _ (sufR_some L) (sufR_cond _ (sufR_none L) (sufR_bnd ?_ ?_))
  · exact sufR_cond _ (succC_suffix _ (fun n e B L => hG _ _ _ _ _ _ _ _) _ _ _ _ _ _ _) (sufR_some L)
  · intro L1 h1 L' h'
    have h2 : SufR L1 (bif !Nat.beq (code t r d) 2 && cut t r d (min m (fS t r d)) (max M (fS t r d)) then
          succC (fun n e B' L' => G (t + 1) (r + 1) (d + n) (min m (fS t r d)) (max M (fS t r d)) e B' L')
            js (wrec q % 1024) (mask (t + 1) (r + 1) d) 24
            (wrec q / 1024 / 2 ^ 828) B L1
        else some L1) :=
      sufR_cond _ (succC_suffix _ (fun n e B L => hG _ _ _ _ _ _ _ _) _ _ _ _ _ _ _) (sufR_some L1)
    exact h2 L' h'

theorem nodeC_suffix (G : Nat → Nat → Nat → Int → Int → Nat → Nat → List CS → Res)
    (hG : ∀ t r d m M q B L, SufR L (G t r d m M q B L)) (f t r d : Nat) (m M : Int) (q B : Nat)
    (L : List CS) : SufR L (nodeC code mask fN fS cut wrec js G f t r d m M q B L) := by
  cases L with
  | nil => exact bodyC_suffix code mask fN fS cut wrec js G hG t r d m M q B []
  | cons s L' =>
    show SufR (s :: L') (bif csEq s f t r d m M q B then some L'
      else bodyC code mask fN fS cut wrec js G t r d m M q B (s :: L'))
    refine sufR_cond _ ?_ (bodyC_suffix code mask fN fS cut wrec js G hG t r d m M q B _)
    intro L1 h
    cases h
    exact List.suffix_cons s L'

theorem goC_succ (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS) :
    goC code mask fN fS cut wrec js (f + 1) t r d m M q B L =
      nodeC code mask fN fS cut wrec js (goC code mask fN fS cut wrec js f) (f + 1) t r d m M q B L :=
  rfl

theorem goC_suffix : ∀ (f t r d : Nat) (m M : Int) (q B : Nat) (L : List CS),
    SufR L (goC code mask fN fS cut wrec js f t r d m M q B L) := by
  intro f
  induction f with
  | zero => intro t r d m M q B L; exact sufR_none L
  | succ f ih =>
    intro t r d m M q B L
    rw [goC_succ]
    exact nodeC_suffix code mask fN fS cut wrec js _ ih (f + 1) t r d m M q B L

end Rule

/-- With the empty list a call that does not find answers `some []`. -/
theorem nil_of_sufR {o : Res} (h : SufR [] o) {L : List CS} (hL : o = some L) : L = [] :=
  List.eq_nil_of_suffix_nil (h L hL)

theorem beqF {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beqT {a b : ℕ} (h : a = b) : Nat.beq a b = true := by subst h; exact Nat.beq_refl a

/-! ### The records -/

/-- The slot record `x` is the row of `n` blocks from the entry `D`. -/
def OrbOK (crk nx : ℕ → ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, _, _ => True
  | n + 1, D, x => x % 1024 = crk D ∧ x / 1024 % 8192 = D ∧ OrbOK crk nx n (nx D) (x / 8388608)

/-- The first `n` slots of `x` are rows of 6 blocks from their first entry. -/
def SlotsOK (crk nx : ℕ → ℕ) : ℕ → ℕ → Prop
  | 0, _ => True
  | n + 1, x => OrbOK crk nx 6 (x % P138 / 1024 % 8192) (x % P138) ∧ SlotsOK crk nx n (x / P138)

theorem slotsOK_get {crk nx : ℕ → ℕ} : ∀ {n x i : ℕ}, SlotsOK crk nx n x → i < n →
    OrbOK crk nx 6 (slotD x i) (slotX x i)
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, x, 0, h, _ => by
    simpa [slotD, slotX] using h.1
  | n + 1, x, i + 1, h, hi => by
    have e : slotX x (i + 1) = slotX (x / P138) i := by
      unfold slotX
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    have h2 := slotsOK_get h.2 (by omega : i < n)
    rw [slotD, e]
    exact h2

/-- What the engine needs to know about its records (7 symbols). -/
structure CEnc (enc : List ℕ → ℕ) (crk nx wrec : ℕ → ℕ) (ws : ℕ) : Prop where
  crk_inj : ∀ u v, PermW 7 u → PermW 7 v → crk (enc u) = crk (enc v) → u ~r v
  nx_eq : ∀ a b, PermW 7 a → DoorEq 7 a b → nx (enc a) = enc b
  slots3 : ∀ u, PermW 7 u → SlotsOK crk nx 6 (wrec (enc u) / 1024)
  slots4 : ∀ u, PermW 7 u → SlotsOK crk nx 24 (wrec (enc u) / 1024 / 2 ^ 828)
  s3 : ∀ u v, PermW 7 u → PermW 7 v → WLink 7 3 u v →
    ∃ i < 6, slotD (wrec (enc u) / 1024) i = enc v
  s4 : ∀ u v, PermW 7 u → PermW 7 v → WLink 7 4 u v →
    ∃ i < 24, slotD (wrec (enc u) / 1024 / 2 ^ 828) i = enc v
  cq : ∀ u, PermW 7 u → wrec (enc u) % 1024 = crk (nx (enc u))
  ws : OrbOK crk nx 6 (enc (List.range' 1 7)) ws

/-! ### The marks -/

/-- Every mark of `B` is the class rank of one of the words of `used`. -/
def MInvN (enc : List ℕ → ℕ) (crk : ℕ → ℕ) (B : ℕ) (used : List (List ℕ)) : Prop :=
  ∀ j, Nat.testBit B j = true → ∃ u ∈ used, j = crk (enc u)

theorem minvN_zero (enc : List ℕ → ℕ) (crk : ℕ → ℕ) : MInvN enc crk 0 [] := by
  intro j hj
  simp at hj

theorem minvN_or {enc : List ℕ → ℕ} {crk : ℕ → ℕ} {B : ℕ} {used : List (List ℕ)}
    (h : MInvN enc crk B used) (v : List ℕ) :
    MInvN enc crk (B ||| 2 ^ crk (enc v)) (used ++ [v]) := by
  intro j hj
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hj
  rcases hj with hj | hj
  · obtain ⟨u, hu, he⟩ := h j hj
    exact ⟨u, List.mem_append_left _ hu, he⟩
  · exact ⟨v, by simp, hj.symm⟩

theorem minvN_mono {enc : List ℕ → ℕ} {crk : ℕ → ℕ} {B : ℕ} {used used' : List (List ℕ)}
    (h : MInvN enc crk B used) (hs : ∀ u ∈ used, u ∈ used') : MInvN enc crk B used' := by
  intro j hj
  obtain ⟨u, hu, he⟩ := h j hj
  exact ⟨u, hs u hu, he⟩

section Engine

variable {enc : List ℕ → ℕ} {crk nx wrec : ℕ → ℕ} {ws : ℕ}

theorem unmarkedN (CE : CEnc enc crk nx wrec ws) {B : ℕ} {used : List (List ℕ)}
    (hM : MInvN enc crk B used) (hused : ∀ u ∈ used, PermW 7 u) {v : List ℕ} (hv : PermW 7 v)
    (hnew : ∀ u ∈ used, ¬ u ~r v) : Nat.testBit B (crk (enc v)) = false := by
  cases h : Nat.testBit B (crk (enc v)) with
  | false => rfl
  | true =>
    obtain ⟨u, hu, he⟩ := hM _ h
    exact absurd (CE.crk_inj u v (hused u hu) hv he.symm) (hnew u hu)

/-- The walk along a row finds the end of the sequence. -/
theorem walkC_complete (CE : CEnc enc crk nx wrec ws) (G : ℕ → ℕ → ℕ → List CS → Res)
    (hG : ∀ n e B L, SufR L (G n e B L)) :
    ∀ (R : List (List ℕ)) (n mk : ℕ) (v : List ℕ) (x B : ℕ) (used : List (List ℕ)),
      R.length ≤ n → (mk / 2 ^ R.length) % 2 = 1 → (∀ w ∈ v :: R, PermW 7 w) →
      List.IsChain (DoorEq 7) (v :: R) → OrbOK crk nx (n + 1) (enc v) x →
      MInvN enc crk B used → (∀ u ∈ used, PermW 7 u) →
      (∀ u ∈ used, ∀ w ∈ v :: R, ¬ u ~r w) → List.Pairwise (fun a b => ¬ a ~r b) (v :: R) →
      (∀ B', MInvN enc crk B' (used ++ v :: R) →
        G (n - R.length) (enc ((v :: R).getLast (List.cons_ne_nil v R))) B' [] = none) →
      walkC G (n + 1) mk x B [] = none := by
  intro R
  induction R with
  | nil =>
    intro n mk v x B used _ hbit hperm _ hx hM hused hnew _ hfin
    have hv := hperm v List.mem_cons_self
    have h0 := unmarkedN CE hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hb : mk % 2 = 1 := by simpa using hbit
    have hmk : Nat.beq mk 0 = false := beqF (by omega)
    have hb' : Nat.beq (mk % 2) 1 = true := beqT hb
    obtain ⟨hx1, hx2, _⟩ := hx
    have hf := hfin _ (minvN_or hM v)
    simp only [List.length_nil, Nat.sub_zero, List.getLast_singleton] at hf
    rw [walkC_succ, hmk, cond_false, hx1, h0, cond_false, hb', cond_true, hx2, hf]
    rfl
  | cons v' R' ih =>
    intro n mk v x B used hn hbit hperm hdoor hx hM hused hnew hpw hfin
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    have hv := hperm v List.mem_cons_self
    have h0 := unmarkedN CE hM hused hv (fun u hu => hnew u hu v List.mem_cons_self)
    have hdc := List.isChain_cons_cons.mp hdoor
    have hpc := List.pairwise_cons.mp hpw
    have hused' : ∀ u ∈ used ++ [v], PermW 7 u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hused u h
      · rw [List.mem_singleton.mp h]
        exact hv
    have hmk0 : mk ≠ 0 := by
      intro h
      rw [h] at hbit
      simp at hbit
    have hmk : Nat.beq mk 0 = false := beqF hmk0
    have hbit' : (mk / 2 / 2 ^ R'.length) % 2 = 1 := by
      have e : mk / 2 / 2 ^ R'.length = mk / 2 ^ (v' :: R').length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons, Nat.pow_succ, Nat.mul_comm]
      rw [e]
      exact hbit
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [CE.nx_eq v v' hv hdc.1] at hx3
    rw [walkC_succ, hmk, cond_false, hx1, h0, cond_false, hx2]
    have hsuf : SufR [] (bif Nat.beq (mk % 2) 1 then G (m + 1) (enc v) (B ||| 2 ^ crk (enc v)) []
        else some []) := sufR_cond _ (hG _ _ _ _) (sufR_some [])
    generalize (bif Nat.beq (mk % 2) 1 then G (m + 1) (enc v) (B ||| 2 ^ crk (enc v)) []
        else some []) = X at hsuf
    cases X with
    | none => rfl
    | some L1 =>
      rw [nil_of_sufR hsuf rfl, bnd_some]
      apply ih m (mk / 2) v' (x / 8388608) _ (used ++ [v]) (by simp only [List.length_cons] at hn; omega)
        hbit' (fun w hw => hperm w (List.mem_cons_of_mem _ hw)) hdc.2 hx3 (minvN_or hM v) hused'
        (by
          intro u hu w hw
          rcases List.mem_append.mp hu with h | h
          · exact hnew u h w (List.mem_cons_of_mem _ hw)
          · rw [List.mem_singleton.mp h]
            exact hpc.1 w hw)
        hpc.2
      intro B' hB'
      have e : used ++ [v] ++ v' :: R' = used ++ v :: v' :: R' := by simp
      rw [e] at hB'
      have h := hfin B' hB'
      rw [List.getLast_cons (List.cons_ne_nil v' R')] at h
      have e2 : m + 1 - (v' :: R').length = m - R'.length := by
        simp only [List.length_cons]
        omega
      rw [e2] at h
      exact h

/-- One of the successors is found: then the loop over the successors is found. -/
theorem succC_found (G : ℕ → ℕ → ℕ → List CS → Res) (hG : ∀ n e B L, SufR L (G n e B L))
    (js : Bool) (cq mk B : ℕ) :
    ∀ (n x i : ℕ), i < n →
      walkC G 6 (jsC js cq (slotX x i % 1024) mk) (slotX x i) B [] = none →
      succC G js cq mk n x B [] = none := by
  intro n
  induction n with
  | zero => intro x i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro x i hi hw
    rw [succC_succ]
    have hsuf := walkC_suffix G hG 6 (jsC js cq (x % 1024) mk) (x % P138) B []
    cases i with
    | zero =>
      have e : slotX x 0 = x % P138 := by simp [slotX]
      rw [e] at hw
      rw [Nat.mod_mod_of_dvd _ (by norm_num : (1024 : ℕ) ∣ P138)] at hw
      rw [hw]
      rfl
    | succ i =>
      generalize walkC G 6 (jsC js cq (x % 1024) mk) (x % P138) B [] = X at hsuf
      cases X with
      | none => rfl
      | some L1 =>
        rw [nil_of_sufR hsuf rfl, bnd_some]
        have e : slotX x (i + 1) = slotX (x / P138) i := by
          unfold slotX
          rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
        rw [e] at hw
        exact ih (x / P138) i (by omega) hw

variable {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
  {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {js : Bool}

/-- The mask with Rule JS keeps the bit of a row that is not refused. -/
theorem jsC_bit (CE : CEnc enc crk nx wrec ws) {last v : List ℕ} {R : List (List ℕ)}
    (hlast : PermW 7 last) (hv : PermW 7 v) {mk : ℕ} (hbit : (mk / 2 ^ R.length) % 2 = 1)
    (hjs : js = true → R ≠ [] → ¬ v ~r tau2 7 last) :
    (jsC js (crk (nx (enc last))) (crk (enc v)) mk / 2 ^ R.length) % 2 = 1 := by
  unfold jsC
  cases hj : (js && Nat.beq (crk (enc v)) (crk (nx (enc last))))
  · rw [cond_false]
    exact hbit
  · rw [cond_true]
    simp only [Bool.and_eq_true] at hj
    have hc : crk (enc v) = crk (nx (enc last)) := Nat.eq_of_beq_eq_true hj.2
    have hRnil : R = [] := by
      by_contra hR
      apply hjs hj.1 hR
      rw [CE.nx_eq last (tau2 7 last) hlast rfl] at hc
      exact CE.crk_inj v (tau2 7 last) hv (permW_tau2 (by norm_num) hlast) hc
    subst hRnil
    simp only [List.length_nil, pow_zero, Nat.div_one] at hbit ⊢
    rw [Nat.mod_mod]
    exact hbit

/-- The search finds the end of a sequence of which it has reached a prefix, if the rule holds along
the rest of the sequence and (with Rule JS) no row of the rest is refused. -/
theorem goC_complete (CE : CEnc enc crk nx wrec ws)
    (hmask : ∀ t r d j, j < 6 → code t r (d + (5 - j)) ≠ 0 → (mask t r d / 2 ^ j) % 2 = 1) :
    ∀ (fuel : ℕ) (rest : List TRow) (t r d : ℕ) (m M : ℤ) (B : ℕ) (last : List ℕ)
      (used : List (List ℕ)),
      PermW 7 last → (∀ u ∈ used, PermW 7 u) → MInvN enc crk B used → PCont 7 last used rest →
      KAlong 7 enc code fN fS cut 0 1 0 fuel t r d m M last rest →
      (js = true → NoJSAlong 7 last rest) →
      goC code mask fN fS cut wrec js fuel t r d m M (enc last) B [] = none := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro rest t r d m M B last used hlast hused hM hcont halong hjs
    rw [goC_succ]
    show bodyC code mask fN fS cut wrec js (goC code mask fN fS cut wrec js fuel) t r d m M (enc last) B []
      = none
    unfold bodyC
    cases rest with
    | nil =>
      simp only [KAlong] at halong
      have h0 : Nat.beq (code t r d) 0 = false := beqF (by omega)
      have h1 : Nat.beq (code t r d) 1 = true := beqT halong
      rw [h0, cond_false, h1, cond_true]
    | cons Q rest' =>
      obtain ⟨kd, Q⟩ := Q
      cases Q with
      | nil => exact hcont.elim
      | cons v R =>
        obtain ⟨hR, hperm, hlink, hdoor, hnew, hpw, hcont'⟩ := hcont
        unfold KAlong at halong
        obtain ⟨hkd, hcode, hcut, _, hnext, halong'⟩ := halong
        have hjs1 : js = true → R ≠ [] → ¬ v ~r tau2 7 last := fun h => (hjs h).1
        have hjs2 : js = true → NoJSAlong 7 ((v :: R).getLast (List.cons_ne_nil v R)) rest' :=
          fun h => (hjs h).2
        have h0 : Nat.beq (code t r d) 0 = false := beqF (by omega)
        have h1 : Nat.beq (code t r d) 1 = false := beqF (by omega)
        rw [h0, cond_false, h1, cond_false]
        have hv : PermW 7 v := hperm v List.mem_cons_self
        have hused' : ∀ u ∈ used ++ v :: R, PermW 7 u := by
          intro u hu
          rcases List.mem_append.mp hu with h | h
          · exact hused u h
          · exact hperm u h
        have hbit : (jsC js (crk (nx (enc last))) (crk (enc v)) (mask (t + kd) (r + 1) d)
            / 2 ^ R.length) % 2 = 1 :=
          jsC_bit CE hlast hv (hmask _ _ _ _ (by omega) hnext) hjs1
        -- the walk of the row `v :: R` from its slot
        have hwalk : ∀ (x : ℕ), OrbOK crk nx 6 (enc v) x →
            walkC (fun n e B' L' => goC code mask fN fS cut wrec js fuel (t + kd) (r + 1) (d + n)
                (min m (fK fN fS kd t r d)) (max M (fK fN fS kd t r d)) e B' L') 6
              (jsC js (crk (nx (enc last))) (crk (enc v)) (mask (t + kd) (r + 1) d)) x B [] = none := by
          intro x hx
          exact walkC_complete CE _ (fun n e B' L' => goC_suffix code mask fN fS cut wrec js _ _ _ _ _ _ _ _ _)
            R 5 _ v x B used (by omega) hbit hperm hdoor hx hM hused hnew hpw
            (by
              intro B' hB'
              exact ih rest' _ _ _ _ _ B' _ (used ++ v :: R) (hperm _ (List.getLast_mem _))
                hused' hB' hcont' halong' hjs2)
        have hcq := CE.cq last hlast
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkd with rfl | rfl
        · -- a link of weight 3
          have hcut' : cut t r d (min m (fN t r d)) (max M (fN t r d)) = true := by
            simpa [fK] using hcut
          have hcc : (!Nat.beq (code t r d) 3 && cut t r d (min m (fN t r d)) (max M (fN t r d))) = true := by
            rw [hcut', Bool.and_true]
            rcases hcode with h | h <;> rw [h] <;> rfl
          rw [hcc, cond_true]
          obtain ⟨i, hi, hD⟩ := CE.s3 last v hlast hv (hlink.1 rfl)
          have hO := slotsOK_get (CE.slots3 last hlast) hi
          rw [hD] at hO
          have hc0 : slotX (wrec (enc last) / 1024) i % 1024 = crk (enc v) := hO.1
          have hf := succC_found _ (fun n e B' L' => goC_suffix code mask fN fS cut wrec js _ _ _ _ _ _ _ _ _)
            js (wrec (enc last) % 1024) (mask t (r + 1) d) B 6 (wrec (enc last) / 1024) i hi
            (by rw [hc0, hcq]; simpa [fK] using hwalk _ hO)
          rw [hf]
          rfl
        · -- a link of weight 4
          have hcut' : cut t r d (min m (fS t r d)) (max M (fS t r d)) = true := by
            simpa [fK] using hcut
          have hcc : (!Nat.beq (code t r d) 2 && cut t r d (min m (fS t r d)) (max M (fS t r d))) = true := by
            rw [hcut', Bool.and_true]
            rcases hcode with h | h <;> rw [h] <;> rfl
          obtain ⟨i, hi, hD⟩ := CE.s4 last v hlast hv (hlink.2 rfl)
          have hO := slotsOK_get (CE.slots4 last hlast) hi
          rw [hD] at hO
          have hc0 : slotX (wrec (enc last) / 1024 / 2 ^ 828) i % 1024 = crk (enc v) := hO.1
          have hf := succC_found _ (fun n e B' L' => goC_suffix code mask fN fS cut wrec js _ _ _ _ _ _ _ _ _)
            js (wrec (enc last) % 1024) (mask (t + 1) (r + 1) d) B 24 (wrec (enc last) / 1024 / 2 ^ 828) i hi
            (by rw [hc0, hcq]; simpa [fK] using hwalk _ hO)
          have hsuf : SufR [] (bif !Nat.beq (code t r d) 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)) then
              succC (fun n e B' L' => goC code mask fN fS cut wrec js fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B' L') js
                (wrec (enc last) % 1024) (mask t (r + 1) d) 6 (wrec (enc last) / 1024) B []
              else some []) :=
            sufR_cond _ (succC_suffix _ (fun n e B' L' => goC_suffix code mask fN fS cut wrec js _ _ _ _ _ _ _ _ _)
              _ _ _ _ _ _ _) (sufR_some [])
          generalize (bif !Nat.beq (code t r d) 3 && cut t r d (min m (fN t r d)) (max M (fN t r d)) then
              succC (fun n e B' L' => goC code mask fN fS cut wrec js fuel t (r + 1) (d + n)
                (min m (fN t r d)) (max M (fN t r d)) e B' L') js
                (wrec (enc last) % 1024) (mask t (r + 1) d) 6 (wrec (enc last) / 1024) B []
              else some []) = X at hsuf
          cases X with
          | none => rfl
          | some L1 =>
            rw [nil_of_sufR hsuf rfl, bnd_some, hcc, cond_true]
            exact hf

/-- The whole search finds a sequence along which the rule holds and no row is refused. -/
theorem searchC_none (CE : CEnc enc crk nx wrec ws)
    (hmask : ∀ t r d j, j < 6 → code t r (d + (5 - j)) ≠ 0 → (mask t r d / 2 ^ j) % 2 = 1)
    (hst : enc (List.range' 1 7) = enc (List.range' 1 7)) (fuel : ℕ)
    (R1 : List (List ℕ)) (rest : List TRow)
    (hR1 : R1.length ≤ 5) (hperm : ∀ w ∈ List.range' 1 7 :: R1, PermW 7 w)
    (hdoor : List.IsChain (DoorEq 7) (List.range' 1 7 :: R1))
    (hpw : List.Pairwise (fun a b => ¬ a ~r b) (List.range' 1 7 :: R1))
    (hcont : PCont 7 ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _))
      (List.range' 1 7 :: R1) rest)
    (halong : KAlong 7 enc code fN fS cut 0 1 0 fuel 0 1 (5 - R1.length) 0 0
      ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) rest)
    (hjs : js = true → NoJSAlong 7 ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) rest) :
    searchC code mask fN fS cut wrec js ws fuel [] = none := by
  have hbit : (63 / 2 ^ R1.length) % 2 = 1 := by
    interval_cases h : R1.length <;> norm_num
  exact walkC_complete CE _ (fun n e B L => goC_suffix code mask fN fS cut wrec js _ _ _ _ _ _ _ _ _)
    R1 5 63 (List.range' 1 7) ws 0 [] hR1 hbit hperm hdoor CE.ws (minvN_zero enc crk) (by simp)
    (by simp) hpw
    (by
      intro B' hB'
      exact goC_complete CE hmask fuel rest 0 1 (5 - R1.length) 0 0 B' _ (List.range' 1 7 :: R1)
        (hperm _ (List.getLast_mem _)) hperm (by simpa using hB') hcont halong hjs)

end Engine

/-! ### The statement -/

/-- **A whole search that does not answer `none` proves `KStmt16`.** -/
theorem kstmt16_of_searchC {enc : List ℕ → ℕ} {crk nx wrec : ℕ → ℕ} {ws : ℕ}
    {code mask : ℕ → ℕ → ℕ → ℕ} {fN fS : ℕ → ℕ → ℕ → ℤ}
    {cut : ℕ → ℕ → ℕ → ℤ → ℤ → Bool} {js : Bool} {fuel : ℕ}
    (CE : CEnc enc crk nx wrec ws)
    (hmask : ∀ t r d j, j < 6 → code t r (d + (5 - j)) ≠ 0 → (mask t r d / 2 ^ j) % 2 = 1)
    (hs : searchC code mask fN fS cut wrec js ws fuel [] ≠ none) :
    KStmt16 7 js code fN fS cut := by
  intro x0 rest0 hL hjs hrule
  obtain ⟨kd0, Q0⟩ := x0
  have hQ0 : Q0 ≠ [] := hL.pieces_ne (kd0, Q0) List.mem_cons_self
  obtain ⟨v0, R0, rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hv0 : PermW 7 v0 := hL.words _ List.mem_cons_self v0 List.mem_cons_self
  have hL' := hL.relabel hv0
  have hrule' := KS.ruleK_relab v0 rest0 _ _ _ _ _ hrule
  have hjsA : js = true → NoJSAlong 7 ((v0 :: R0).getLast (List.cons_ne_nil _ _)) rest0 :=
    fun h => K16.noJSAlong_of_noJS rest0 (kd0, v0 :: R0) (List.cons_ne_nil _ _)
      (fun y hy => hL.pieces_ne y (List.mem_cons_of_mem _ hy)) (hjs h)
  have hg : v0.map (S.relab v0) = List.range' 1 7 := by
    rw [S.map_relab_self hv0.1, hv0.2.1]
  have hjsR : js = true → NoJSAlong 7
      ((List.range' 1 7 :: R0.map (List.map (S.relab v0))).getLast (List.cons_ne_nil _ _))
      (relabSeq v0 rest0) := by
    intro h
    rw [← hg, K16.getLast_map_cons]
    exact K16.noJSAlong_relab (by omega) hv0 rest0 _
      (hL.words _ List.mem_cons_self _ (List.getLast_mem _))
      (fun y hy => hL.words y (List.mem_cons_of_mem _ hy)) (hjsA h)
  have hshape : relabSeq v0 ((kd0, v0 :: R0) :: rest0) =
      (kd0, List.range' 1 7 :: R0.map (List.map (S.relab v0))) :: relabSeq v0 rest0 := by
    simp [relabSeq, S.map_relab_self hv0.1, hv0.2.1]
  rw [hshape] at hL'
  have elen : 7 - 1 - (kd0, v0 :: R0).2.length = 5 - (R0.map (List.map (S.relab v0))).length := by
    simp only [List.length_cons, List.length_map]
    omega
  rw [elen] at hrule'
  generalize R0.map (List.map (S.relab v0)) = R1 at hL' hrule' hjsR
  generalize relabSeq v0 rest0 = rest1 at hL' hrule' hjsR
  have hperm : ∀ w ∈ List.range' 1 7 :: R1, PermW 7 w :=
    hL'.words (kd0, List.range' 1 7 :: R1) List.mem_cons_self
  have hcl : List.Pairwise (fun a b => ¬ a ~r b)
      ((List.range' 1 7 :: R1) ++ (rest1.map Prod.snd).flatten) := by
    have := hL'.classes
    simp only [List.map_cons, List.flatten_cons] at this
    exact this
  have hcl' := List.pairwise_append.mp hcl
  have hsz := hL'.size_le (kd0, List.range' 1 7 :: R1) List.mem_cons_self
  have hR1 : R1.length ≤ 5 := by
    simp only [List.length_cons] at hsz
    omega
  have hdoor := S.door_chain (by norm_num) _ hperm
    (hL'.doors (kd0, List.range' 1 7 :: R1) List.mem_cons_self) hcl'.1
  have hcont := PS.pcont_of_seq (by norm_num) rest1 (kd0, List.range' 1 7 :: R1) (List.range' 1 7 :: R1)
    (List.cons_ne_nil _ _) hL' hcl'.2.2
  have hne1 : ∀ y ∈ rest1, y.2 ≠ [] :=
    fun y hy => hL'.pieces_ne y (List.mem_cons_of_mem _ hy)
  have hP := KS.kalong_of_rule (enc := enc) 0 rest1 fuel _ _ _ _ _
    ((List.range' 1 7 :: R1).getLast (List.cons_ne_nil _ _)) hne1 hrule'
  exact hs (searchC_none CE hmask rfl fuel R1 rest1 hR1 hperm hdoor hcl'.1 hcont hP hjsR)

end Cert
end SuperpermLowerBounds
