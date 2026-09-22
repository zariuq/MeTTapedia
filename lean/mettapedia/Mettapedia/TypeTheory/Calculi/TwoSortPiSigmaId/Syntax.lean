import Lean

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax

/-- Kernel-level global declaration name. -/
abbrev DeclName := Lean.Name

/-- Scoped syntax for a fixed two-sort dependent-calculus fragment.

This syntax originates in the historical MeTTa-Pure experiment; it is not
an adoption of that experiment as MeTTa or Prime. The heads are a
distinguished ground type `u0` and an untyped
formation marker `u1`. The regular judgment has `u0 : u1` and uses
`u1` at domain, codomain and result in product/sum formation. Identity
formation and reflexivity are present; an identity eliminator, cumulative
universes and quantification over a universe of types are absent.

`Permissive.Typing.HasType` is an older permissive judgment with missing formation
premises. `Regular.RegularJudgment` separately requires a
regular context and presupposition-closed, declaration-free typing.
Their inequivalence is proved. Results about one are not results about the
other, nor about the separate cumulative-tower candidate.

The representation is intrinsically scoped by de Bruijn depth, not
intrinsically typed. Constants belong to the raw grammar and separate
declaration-aware experiments; the regular normalization theorem excludes
them. Keep the fixed heads unchanged when reusing this fragment. -/
inductive ScopedTerm : Nat → Type where
  | var : Fin n → ScopedTerm n
  | const : DeclName → ScopedTerm n
  /-- Sealed fragment: the distinguished ground type (see module notice
  above; not a Russell `Type 0`). -/
  | u0 : ScopedTerm n
  /-- Sealed fragment: the untyped formation marker with `u0 : u1`
  (see module notice above; not a Russell `Type 1`). -/
  | u1 : ScopedTerm n
  | pi : ScopedTerm n → ScopedTerm (n + 1) → ScopedTerm n
  | sigma : ScopedTerm n → ScopedTerm (n + 1) → ScopedTerm n
  | id : ScopedTerm n → ScopedTerm n → ScopedTerm n → ScopedTerm n
  | lam : ScopedTerm (n + 1) → ScopedTerm n
  | app : ScopedTerm n → ScopedTerm n → ScopedTerm n
  | pair : ScopedTerm n → ScopedTerm n → ScopedTerm n
  | fst : ScopedTerm n → ScopedTerm n
  | snd : ScopedTerm n → ScopedTerm n
  | refl : ScopedTerm n → ScopedTerm n
deriving DecidableEq, Repr

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
