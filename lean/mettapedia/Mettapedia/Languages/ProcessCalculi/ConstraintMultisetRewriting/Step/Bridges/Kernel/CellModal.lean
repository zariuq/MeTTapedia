import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellProposals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

/-!
# Finitary modal adequacy for the checked cell step

The finite edge table and finite word outputs give finitely many successor
states, despite infinitely many raw proposal functions and unbounded logical
occurrence generations. The existing Hennessy--Milner theorem therefore
applies to this actual step for every declared state observation.

This is modal adequacy, not a decision procedure for equivalence of arbitrary
unbounded executions. As in the underlying successor logic, event origins
and multiplicity are not recovered from the successor relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellModal

open Mettapedia.Machines.TIsa Control
open CellOccurrences
open LogicOverTheStep.StepSpan

universe u
variable {Key : Type u} [DecidableEq Key] {Atom : Type}

theorem image_finite (edges : List (Edge Key)) (observes : Atom → State Key → Prop) :
    (stepSystem (step edges) observes).ImageFiniteModulo := by
  intro _ state
  refine ⟨{after : State Key | ∃ firing : Firing edges,
      (step edges).Admits (s := state) firing ∧ result state firing = after},
    CellProposals.successor_states_finite edges state, ?_⟩
  intro after moved
  obtain ⟨firing, admitted, endpoint⟩ := moved
  exact ⟨after, ⟨firing, admitted, endpoint⟩, rfl⟩

theorem logical_equivalence_iff_bisimilar (edges : List (Edge Key))
    (observes : Atom → State Key → Prop) (left right : State Key) :
    (stepSystem (step edges) observes).LogicallyEquivalent left right ↔
      (stepSystem (step edges) observes).Bisimilar left right :=
  (stepSystem (step edges) observes).logicallyEquivalent_iff_bisimilar
    (image_finite edges observes) left right

#print axioms image_finite
#print axioms logical_equivalence_iff_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellModal
