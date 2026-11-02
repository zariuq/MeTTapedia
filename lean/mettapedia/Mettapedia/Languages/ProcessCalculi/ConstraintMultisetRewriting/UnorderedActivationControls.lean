import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedTensorProofs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivationControls

/-!
# Computed occurrence order retains two fresh schema activation origins

The same installed source schema has two actual uses at distinct scopes.
Their independently indexed graph is ordered by Kahn's service; the resulting
conventional tensor proof retains the two computed activation receipts and
the complete physical residual boundary under one shared assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedActivationControls

open Mettapedia.Logic.LP
open Mettapedia.Logic.LinearLogic
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open FirstOrderHornActivations
open FirstOrderHornActivationControls
open UnorderedOccurrenceConnections
open PositiveResourceProjection

def selectedAt (index : Fin 2) : ActivatedHornProofs.Selected (O := Nat) activate installed :=
  if index.val = 0 then (origin installed schema (Set.mem_singleton _) 0, pickFirst)
    else (origin installed schema (Set.mem_singleton _) 1, pickSecond)

def indexedEvents := activatedEvents activate installed selectedAt

theorem indexed_roster_keeps_both_uses : roster indexedEvents = events 0 1 := rfl

theorem actual_occurrence_order_is_computed : order? indexedEvents = some [0, 1] := by decide

theorem certificate_from_actual_scoped_model (assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)))
    (solves : ∀ use : Fin 2, ScopedSolutionGluing.Solves assignment use.val (ScopedSolutionGluing.twoUses use)) :
    Certificate action concreteProgram assignment (labelAt 0 1) before indexedEvents := by
  have layout := certificate_from_scoped_solution assignment solves
  exact certificate_of_execution indexedEvents [0, 1] (by decide) layout.executes.1 layout.fresh_from
    layout.unique_makers layout.pure layout.declared layout.executes.2

theorem computed_occurrences_retain_both_actual_activation_scopes :
    ∃ assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)),
      ∃ proof : TensorSequentAdequacy.ActivatedProof action activate installed assignment
          (labels (realized action assignment (labelAt 0 1)) before.present)
          (TensorSequent.Formula.ofMultiset (labels (realized action assignment (labelAt 0 1))
            (LinearConnectionLayout.residual before.present (roster indexedEvents)))),
        proof.uses.map (fun entry => (ActivatedHornProofs.originOf action activate installed assignment entry).inputs) = [0, 1] := by
  classical
  obtain ⟨assignment, solves⟩ := ScopedSolutionGluing.distinct_scopes_glue
  have certificate := certificate_from_actual_scoped_model assignment solves
  obtain ⟨order, computed, proof, origins⟩ := activated_tensor_proof activate installed selectedAt certificate rfl
  have same : order = [0, 1] := Option.some.inj (computed.symm.trans actual_occurrence_order_is_computed)
  subst order
  refine ⟨assignment, proof, ?_⟩
  have scopes := congrArg (List.map fun actual : ActivatedHornProofs.Origin activate installed => actual.inputs) origins
  simp only [List.map_map] at scopes
  simp only [Function.comp_def] at scopes
  simp [selectedAt, origin] at scopes
  exact scopes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedActivationControls
