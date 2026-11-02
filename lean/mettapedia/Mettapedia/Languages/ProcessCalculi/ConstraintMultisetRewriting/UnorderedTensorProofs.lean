import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedConnectionCompleteness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentAdequacy

/-!
# Unordered connections compute origin-retaining tensor proofs

The existing Kahn service chooses the actual occurrence order. Its selected
CMR execution supplies an independent conventional tensor-sequent proof over
the complete residual boundary. The activated adapter retains the installed
source schema and computed activation receipt for each indexed use.

No total order is supplied as a premise. Shared reads, guards, contextual
schema views, native execution and a full mating equivalence remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections

open Mettapedia.Logic.LinearLogic
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open LinearConnectionLayout
open PositiveResourceProjection

universe uT uS uO uR uX
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}
  {A : SubstitutionAction T S} {program : Set (RuleInstance T)} {assignment : S}
  {label : O → T} {before : Configuration T O} {events : Fin n → Event T O}

theorem Certificate.tensor_proof [DecidableEq T]
    (certificate : Certificate A program assignment label before events) (structural : A.E = Eq) :
    ∃ order : List (Fin n), order? events = some order ∧
      ∃ proof : TensorSequentAdequacy.Proof A program assignment
          (labels (realized A assignment label) before.present)
          (TensorSequent.Formula.ofMultiset
            (labels (realized A assignment label) (LinearConnectionLayout.residual before.present (roster events)))),
        proof.uses.map (LinearHornAdequacy.rawRule A program assignment) = order.map (fun index => (events index).1) := by
  obtain ⟨order, computed⟩ := exists_computed_order events certificate.acyclic
  have spec := order?_spec events computed
  have layout := certificate.conditions.layout_of_enumeration spec.1 spec.2
  obtain ⟨diagram, rawUses⟩ := layout.logical_proof structural
  obtain ⟨proof, sameUses⟩ := TensorSequent.ofHornAtomic diagram
  have perm : (order.map events).Perm (roster events) := (order?_perm events computed).map events
  obtain ⟨packed, packedUses⟩ := TensorSequent.Derives.repackageGoal proof
    (right := TensorSequent.Formula.ofMultiset
      (labels (realized A assignment label) (LinearConnectionLayout.residual before.present (roster events))))
    (by simpa only [TensorSequent.Formula.atoms_ofMultiset] using
      congrArg (labels (realized A assignment label)) (residual_eq_of_perm before.present perm))
  refine ⟨order, computed, packed, ?_⟩
  have uses := (congrArg (List.map (LinearHornAdequacy.rawRule A program assignment))
    (packedUses.trans sameUses)).trans rawUses
  simp only [List.map_map] at uses
  simp only [Function.comp_def] at uses
  exact uses

variable {R : Type uR} {X : Type uX}

def activatedEvents (activate : R → X → Option (RuleInstance T)) (installed : Set R)
    (selected : Fin n → ActivatedHornProofs.Selected (O := O) activate installed) : Fin n → Event T O :=
  fun index => ActivatedHornProofs.ordinary activate installed (selected index)

/-- Typed activation receipts keep installed-schema origin while graph
vertices remain distinct occurrence indices. The returned proof's origin
list is the actual computed order, rather than an inferred rule-value list. -/
theorem activated_tensor_proof [DecidableEq T] (activate : R → X → Option (RuleInstance T)) (installed : Set R)
    (selected : Fin n → ActivatedHornProofs.Selected (O := O) activate installed)
    (certificate : Certificate A program assignment label before (activatedEvents activate installed selected))
    (structural : A.E = Eq) :
    ∃ order : List (Fin n), order? (activatedEvents activate installed selected) = some order ∧
      ∃ proof : TensorSequentAdequacy.ActivatedProof A activate installed assignment
          (labels (realized A assignment label) before.present)
          (TensorSequent.Formula.ofMultiset (labels (realized A assignment label)
            (LinearConnectionLayout.residual before.present (roster (activatedEvents activate installed selected))))),
        proof.uses.map (ActivatedHornProofs.originOf A activate installed assignment) = order.map (fun index => (selected index).1) := by
  obtain ⟨order, computed, executes, solved, rows⟩ := certificate.conditions.sequentialize certificate.acyclic
  have same : (order.map selected).map (ActivatedHornProofs.ordinary activate installed) =
      order.map (activatedEvents activate installed selected) := by rw [List.map_map]; rfl
  have actualExecution : ConditionalSchedule.Executable A label before
      ((order.map selected).map (ActivatedHornProofs.ordinary activate installed)) := same.symm ▸ executes
  have actualPure : LinearHornAdequacy.Pure ((order.map selected).map (ActivatedHornProofs.ordinary activate installed)) :=
    same.symm ▸ certificate.conditions.pure_order order
  have actualModel : A.Models assignment (ConditionalSchedule.follow label before
      ((order.map selected).map (ActivatedHornProofs.ordinary activate installed))).equations := same.symm ▸ solved
  obtain ⟨proof, origins⟩ := TensorSequentAdequacy.activated_schedule_to_sequent A activate installed assignment label
    structural (order.map selected) before actualExecution actualPure actualModel
  have actualRows : (ConditionalSchedule.follow label before
      ((order.map selected).map (ActivatedHornProofs.ordinary activate installed))).present =
        LinearConnectionLayout.residual before.present (roster (activatedEvents activate installed selected)) := by
    simpa only [same] using rows
  obtain ⟨packed, packedUses⟩ := TensorSequent.Derives.repackageGoal proof
    (right := TensorSequent.Formula.ofMultiset (labels (realized A assignment label)
      (LinearConnectionLayout.residual before.present (roster (activatedEvents activate installed selected)))))
    (by simpa only [TensorSequent.Formula.atoms_ofMultiset] using congrArg (labels (realized A assignment label)) actualRows)
  refine ⟨order, computed, packed, ?_⟩
  have actualOrigins := (congrArg (List.map (ActivatedHornProofs.originOf A activate installed assignment)) packedUses).trans origins
  simp only [List.map_map] at actualOrigins
  simp only [Function.comp_def] at actualOrigins
  exact actualOrigins

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedOccurrenceConnections
