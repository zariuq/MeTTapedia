import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjectionControls

/-!
# Tensor sequents retain actual schema scopes and physical CMR results

One installed first-order schema has two actual fresh uses in the conventional
tensor-sequent presentation. A duplicate-valued physical receipt passes into
that presentation and back through its logical converse, preserving the
complete result and activation origin under the same assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentControls

open Mettapedia.Logic.LP
open Mettapedia.Logic.LinearLogic
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection

namespace ScopedExample

open FirstOrderHornActivations
open FirstOrderHornActivationControls

theorem one_schema_has_two_fresh_tensor_sequent_uses :
    ∃ assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)),
      ∃ proof : TensorSequentAdequacy.ActivatedProof action activate installed assignment
          (labels (realized action assignment (labelAt 0 1)) before.present)
          (TensorSequent.Formula.ofMultiset (labels (realized action assignment (labelAt 0 1))
            (ConditionalSchedule.follow (labelAt 0 1) before (events 0 1)).present)),
        proof.uses.map (fun entry => (ActivatedHornProofs.originOf action activate installed assignment entry).inputs) = [0, 1] := by
  classical
  obtain ⟨assignment, solves⟩ := ScopedSolutionGluing.distinct_scopes_glue
  have layout := certificate_from_scoped_solution assignment solves
  obtain ⟨proof, origins⟩ := TensorSequentAdequacy.activated_schedule_to_sequent action activate installed assignment
    (labelAt 0 1) rfl (selected 0 1) before layout.executes.1 layout.pure layout.executes.2
  refine ⟨assignment, proof, ?_⟩
  have scopes := congrArg (List.map fun actual : ActivatedHornProofs.Origin activate installed => actual.inputs) origins
  simp only [List.map_map, selected, List.map_cons, List.map_nil, origin] at scopes
  simp only [Function.comp_def] at scopes
  exact scopes

end ScopedExample

namespace PhysicalRoundTrip

open ConstraintMultisetRewriting.Controls
open PositiveResourceProjection.Controls

noncomputable section

local instance : DecidableEq (Term signature) := Classical.decEq _

def activate (_ : Unit) (_ : Unit) : Option (RuleInstance (Term signature)) := some duplicateOutputs
def installed : Set Unit := Set.univ
def sourceOrigin : ActivatedHornProofs.Origin activate installed := ⟨(), Set.mem_univ _, (), duplicateOutputs, rfl⟩

theorem a_real_receipt_survives_tensor_sequent_translation_and_back :
    ∃ selected : List (ActivatedHornProofs.Selected (O := Id) activate installed),
      ConditionalSchedule.Executable A indexedLabel indexedBefore (selected.map (ActivatedHornProofs.ordinary activate installed)) ∧
      A.Models both (ConditionalSchedule.follow indexedLabel indexedBefore
        (selected.map (ActivatedHornProofs.ordinary activate installed))).equations ∧
      labels (realized A both indexedLabel) (ConditionalSchedule.follow indexedLabel indexedBefore
        (selected.map (ActivatedHornProofs.ordinary activate installed))).present =
          ({Term.const (σ := signature) 1, Term.const (σ := signature) 1, Term.const (σ := signature) 1} : Multiset (Term signature)) ∧
      selected.map Prod.fst = [sourceOrigin] := by
  obtain ⟨selection, valid, solved, _, _, _, observed⟩ := an_actual_selection_realizes_the_bag_frame
  let sourceSelected : List (ActivatedHornProofs.Selected (O := Id) activate installed) := [(sourceOrigin, selection)]
  have executes : ConditionalSchedule.Executable A indexedLabel indexedBefore
      (sourceSelected.map (ActivatedHornProofs.ordinary activate installed)) := ⟨valid, both, solved⟩
  have pure : LinearHornAdequacy.Pure (sourceSelected.map (ActivatedHornProofs.ordinary activate installed)) := by
    intro event member
    have same := List.mem_singleton.mp member
    subst event
    exact ⟨rfl, rfl⟩
  obtain ⟨proof, origins⟩ := TensorSequentAdequacy.activated_schedule_to_sequent A activate installed both indexedLabel
    rfl sourceSelected indexedBefore executes pure solved
  have supply : ∀ (used : Finset Id) (value : Term signature),
      ∃ occurrence, occurrence ∉ used ∧ indexedLabel occurrence = value := IndexedOccurrences.supply
  obtain ⟨selected, selectedRuns, _, finalModel, boundary, selectedOrigins⟩ :=
    TensorSequentAdequacy.activated_sequent_to_schedule A activate installed both indexedLabel rfl supply
      indexedBefore (A.models_nil both) _ proof
  rw [TensorSequent.Formula.atoms_ofMultiset] at boundary
  exact ⟨selected, selectedRuns, finalModel, boundary.trans observed, selectedOrigins.trans origins⟩

end
end PhysicalRoundTrip

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentControls
