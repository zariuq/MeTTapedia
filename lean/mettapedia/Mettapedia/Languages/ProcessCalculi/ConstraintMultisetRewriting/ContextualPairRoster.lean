import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSumRoster
import Mathlib.Data.Fintype.BigOperators

/-!
# Two selected declaration ports and their actual finite roster

Both selected ports occur in the source equation. Its roster is therefore
exactly those two ports together with the active unselected declarations.
Splitting the image potential uses only the finite pair, not a finite
ambient declaration carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairRoster

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActiveSupport
open scoped BigOperators

variable {S : Signature} {Other Next : Type}
  {first : Bool → MetaArity S} {other : Other → MetaArity S} {next : Next → MetaArity S}

theorem pair_roster (roster : Finset (Bool ⊕ Other))
    (left : .inl false ∈ roster) (right : .inl true ∈ roster) :
    roster = Finset.univ.disjSum roster.toRight := by
  ext identity
  cases identity with
  | inl marker => cases marker <;> simp [left, right]
  | inr identity => simp

theorem pair_potential (candidate : Assignment (sumDeclarations first other) next)
    (roster : Finset (Bool ⊕ Other)) (left : .inl false ∈ roster) (right : .inl true ∈ roster) :
    potential candidate roster =
      termSize (candidate (.inl false)) + termSize (candidate (.inl true)) +
      ∑ identity ∈ roster.toRight, termSize (candidate (.inr identity)) := by
  conv_lhs => rw [pair_roster roster left right]
  rw [ContextualSumRoster.potential_disjSum, Fintype.sum_bool]
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairRoster
