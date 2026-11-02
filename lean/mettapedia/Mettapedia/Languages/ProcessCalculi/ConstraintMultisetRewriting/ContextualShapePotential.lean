import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverMeasure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPairRoster

/-!
# Finite shape image sizes measure contextual solver work

Only declarations occurring in the actual queue contribute. First-order
shape images may use any target name family; neither ambient family is
required to be finite. The remaining coordinates are the existing active
interface cost and equation-tree weight.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapePotential

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualShapeErasure
open ContextualSolverMeasure
open scoped BigOperators

variable {S : Signature} {V W Next Other : Type} {source : V → MetaArity S} {target : W → MetaArity S}

def potential (images : ShapeAssignment S V Next) (roster : Finset V) : Nat :=
  ∑ identity ∈ roster, (images identity).size

theorem monotone (images : ShapeAssignment S V Next) {small large : Finset V} (included : small ⊆ large) :
    potential images small ≤ potential images large := Finset.sum_le_sum_of_subset included

theorem disjSum {First : Type} (images : ShapeAssignment S (First ⊕ Other) Next)
    (left : Finset First) (right : Finset Other) :
    potential images (left.disjSum right) =
      (∑ identity ∈ left, (images (.inl identity)).size) + ∑ identity ∈ right, (images (.inr identity)).size :=
  Finset.sum_disjSum left right _

theorem unit (images : ShapeAssignment S (Unit ⊕ Other) Next) (roster : Finset (Unit ⊕ Other))
    (selected : .inl () ∈ roster) :
    potential images roster = (images (.inl ())).size + ∑ identity ∈ roster.toRight, (images (.inr identity)).size := by
  conv_lhs => rw [ContextualSumRoster.unit_roster roster selected]
  rw [disjSum, Finset.sum_singleton]

theorem pair (images : ShapeAssignment S (Bool ⊕ Other) Next) (roster : Finset (Bool ⊕ Other))
    (left : .inl false ∈ roster) (right : .inl true ∈ roster) :
    potential images roster = (images (.inl false)).size + (images (.inl true)).size +
      ∑ identity ∈ roster.toRight, (images (.inr identity)).size := by
  conv_lhs => rw [ContextualPairRoster.pair_roster roster left right]
  rw [disjSum, Fintype.sum_bool]
  omega

theorem reindex_exact [DecidableEq V] [DecidableEq W] (equivalence : V ≃ W)
    (forward : ∀ identity, target (equivalence identity) = source identity)
    (backward : ∀ identity, source (equivalence.symm identity) = target identity)
    (problem : Problem source) (images : ShapeAssignment S V Next) :
    potential (fun identity => images (equivalence.symm identity)) (active (mapProblem (reindex equivalence forward) problem)) =
      potential images (active problem) := by
  rw [ContextualActiveReindex.active_reindex_exact equivalence forward backward]
  unfold potential
  rw [Finset.sum_image (fun _ _ _ _ same => equivalence.injective same)]
  apply Finset.sum_congr rfl
  intro identity _
  change (images (equivalence.symm (equivalence identity))).size = (images identity).size
  rw [equivalence.symm_apply_apply]

theorem permutation [DecidableEq V] (images : ShapeAssignment S V Next) {first second : Problem source}
    (permuted : first.Perm second) : potential images (active first) = potential images (active second) := by
  rw [ContextualProblemPermutation.active_permutation permuted]

def measure [DecidableEq V] (images : ShapeAssignment S V Next) (problem : Problem source) : Work :=
  (potential images (active problem), ContextualInterfacePotential.cost source (active problem),
    ContextualEquationWeight.weight problem)

theorem normalization_bounds [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem result : Problem source} (computed : ContextualRigidSolver.normalize problem = some result)
    (images : ShapeAssignment S V Next) :
    (measure images result).1 ≤ (measure images problem).1 ∧
      (measure images result).2.1 ≤ (measure images problem).2.1 ∧
      (measure images result).2.2 ≤ (measure images problem).2.2 :=
  ⟨monotone images (ContextualRigidSupport.normalization_active_subset computed),
    ContextualRigidWeight.normalization_interface_cost computed, ContextualRigidWeight.normalization_weight problem computed⟩

theorem smaller_after_normalization [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {problem result : Problem source} (computed : ContextualRigidSolver.normalize problem = some result)
    (images : ShapeAssignment S V Next) {after : Work} (strict : Smaller after (measure images result)) :
    Smaller after (measure images problem) := by
  have bounded := normalization_bounds computed images
  exact strict_then_bounds strict bounded.1 bounded.2.1 bounded.2.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapePotential
