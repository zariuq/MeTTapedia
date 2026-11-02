import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations
import Mathlib.Data.Finset.Sum

/-!
# Finite active rosters at a distinguished declaration port

Splitting a selected declaration from the others also splits its finite
active-image sum. The remaining carrier can be infinite. These equalities
connect local fresh-helper progress laws to the roster of an actual queue.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSumRoster

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActiveSupport
open scoped BigOperators

variable {S : Signature} {First Other Next : Type}
  {first : First → MetaArity S} {other : Other → MetaArity S} {next : Next → MetaArity S}

theorem potential_disjSum (candidate : Assignment (sumDeclarations first other) next)
    (left : Finset First) (right : Finset Other) :
    potential candidate (left.disjSum right) =
      (∑ identity ∈ left, termSize (candidate (.inl identity))) +
      ∑ identity ∈ right, termSize (candidate (.inr identity)) :=
  Finset.sum_disjSum left right _

theorem unit_roster (roster : Finset (Unit ⊕ Other)) (selected : .inl () ∈ roster) :
    roster = ({()} : Finset Unit).disjSum roster.toRight := by
  ext identity
  cases identity with
  | inl marker => cases marker; simp [selected]
  | inr identity => simp

theorem unit_potential {parameters : Ctx S} {result : S.Srt}
    (candidate : Assignment (sumDeclarations (fun _ : Unit => (parameters, result)) other) next)
    (roster : Finset (Unit ⊕ Other)) (selected : .inl () ∈ roster) :
    potential candidate roster = termSize (candidate (.inl ())) +
      ∑ identity ∈ roster.toRight, termSize (candidate (.inr identity)) := by
  conv_lhs => rw [unit_roster roster selected]
  rw [potential_disjSum]
  simp only [Finset.sum_singleton]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSumRoster
