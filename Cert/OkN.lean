import Cert.KEngineN
import Cert.RDefs

/-!
# The statement of an evaluated lemma of F0 to F5

`okN … s L`: the potentials of the prefix `s` are above `-off`, and the search below `s` with the prefixes of `L`
skipped does not find. The kernel evaluates the three parts in one declaration, so the prefix is computed once.
`AssembleN.lean` turns `okN … = true` into `FullC`. This file imports only the engine, so that the evaluated
modules stay small.
-/

namespace SuperpermLowerBounds
namespace Cert

/-- What an evaluated lemma of F0 to F5 states. -/
noncomputable def okN (rl : Nat → Nat → Nat → Nat) (A R C a b h : Nat) (wrec : Nat → Nat) (js : Bool) (s : CS)
    (L : List CS) : Bool :=
  decide (-(offN : Int) ≤ s.m) && decide (-(offN : Int) ≤ s.M) &&
    (goN (codeR rl A R C) (maskR rl A R C) rl A R C a b h wrec js s.f s.t s.r s.d s.m s.M s.q s.B L).isSome

end Cert
end SuperpermLowerBounds
