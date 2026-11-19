import Cert.Cut

/-!
# Putting the evaluated lemmas together

The evaluated lemmas have the form `(goC … L).isSome = true` (a search below a prefix with the list `L` of
the prefixes below it that other lemmas take care of).  `full_of_isSome` (empty list) and `full_of_cut`
turn them into `FullC`; `allC_cons`, `allC_nil` build the hypothesis on a list; `searchC_ok` gives the whole
search.
-/

namespace SuperpermLowerBounds
namespace Cert

section

variable {code mask : Nat → Nat → Nat → Nat} {fN fS : Nat → Nat → Nat → Int}
  {cut : Nat → Nat → Nat → Int → Int → Bool} {wrec : Nat → Nat} {js : Bool}

theorem full_of_isSome {f t r d : Nat} {m M : Int} {q B : Nat}
    (h : (goC code mask fN fS cut wrec js f t r d m M q B []).isSome = true) :
    FullC code mask fN fS cut wrec js ⟨f, t, r, d, m, M, q, B⟩ := by
  intro h0
  rw [show goC code mask fN fS cut wrec js f t r d m M q B [] = none from h0] at h
  cases h

theorem full_of_cut {f t r d : Nat} {m M : Int} {q B : Nat} {L : List CS}
    (h : (goC code mask fN fS cut wrec js f t r d m M q B L).isSome = true)
    (hL : ∀ s ∈ L, FullC code mask fN fS cut wrec js s) :
    FullC code mask fN fS cut wrec js ⟨f, t, r, d, m, M, q, B⟩ := by
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp h
  exact goC_cut code mask fN fS cut wrec js f t r d m M q B L L' hL' hL

theorem allC_nil (P : CS → Prop) : ∀ s ∈ ([] : List CS), P s := fun _ h => by cases h

theorem allC_cons {P : CS → Prop} {s : CS} {L : List CS} (h1 : P s) (h2 : ∀ x ∈ L, P x) :
    ∀ x ∈ s :: L, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1
  · exact h2 x hx

theorem searchC_ok {ws fuel : Nat} {L : List CS}
    (h : (searchC code mask fN fS cut wrec js ws fuel L).isSome = true)
    (hL : ∀ s ∈ L, FullC code mask fN fS cut wrec js s) :
    searchC code mask fN fS cut wrec js ws fuel [] ≠ none := by
  obtain ⟨L', hL'⟩ := Option.isSome_iff_exists.mp h
  exact searchC_cut code mask fN fS cut wrec js hL' hL

end

end Cert
end SuperpermLowerBounds
