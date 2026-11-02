import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSumRoster

/-!
# Finite active parameter interfaces as a secondary solver measure

The cost is the sum of declared parameter counts on an actual finite roster.
It is monotone under roster inclusion and unchanged by an arity-preserving
declaration equivalence. A distinguished port splits from its active others
without imposing finiteness on their ambient carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInterfacePotential

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open scoped BigOperators

variable {S : Signature} {V W Other : Type}

def cost (source : V → MetaArity S) (roster : Finset V) : Nat :=
  ∑ identity ∈ roster, (source identity).1.length

theorem monotone (source : V → MetaArity S) {small large : Finset V} (included : small ⊆ large) :
    cost source small ≤ cost source large :=
  Finset.sum_le_sum_of_subset included

theorem unit_roster_cost (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (roster : Finset (Unit ⊕ Other)) :
    cost (sumDeclarations (fun _ : Unit => (parameters, result)) others)
      (({()} : Finset Unit).disjSum roster.toRight) =
      parameters.length + ∑ identity ∈ roster.toRight, (others identity).1.length := by
  unfold cost
  rw [Finset.sum_disjSum, Finset.sum_singleton]

theorem selected_unit_cost (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S)
    (roster : Finset (Unit ⊕ Other)) (selected : .inl () ∈ roster) :
    cost (sumDeclarations (fun _ : Unit => (parameters, result)) others) roster =
      parameters.length + ∑ identity ∈ roster.toRight, (others identity).1.length := by
  conv_lhs => rw [ContextualSumRoster.unit_roster roster selected]
  exact unit_roster_cost parameters result others roster

theorem reindex_exact [DecidableEq V] [DecidableEq W]
    (source : V → MetaArity S) (target : W → MetaArity S) (equivalence : V ≃ W)
    (forward : ∀ identity, target (equivalence identity) = source identity)
    (backward : ∀ identity, source (equivalence.symm identity) = target identity) (problem : Problem source) :
    cost target (active (mapProblem (reindex equivalence forward) problem)) = cost source (active problem) := by
  rw [ContextualActiveReindex.active_reindex_exact equivalence forward backward]
  unfold cost
  rw [Finset.sum_image (fun _ _ _ _ same => equivalence.injective same)]
  apply Finset.sum_congr rfl
  intro identity _
  rw [forward identity]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInterfacePotential
