import Mettapedia.GSLT.Causality.ResourceTensorSequent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ActivatedHornProofs

/-!
# Ordinary CMR has the positive tensor-sequent proof presentation

The independent tensor calculus has the conventional left/right and formula
cut rules. Its exact equivalence with multiplicative Horn diagrams lifts to
the existing pure CMR schedule comparison. Installed schema activation
receipts and the complete residual resource boundary remain explicit.

The comparison uses one global complete-store model. Reads, checks,
contextual stored-schema views, arbitrary MLL formulas and native execution
are outside this result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentAdequacy

open Mettapedia.Logic.LinearLogic
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection

universe uT uS uO uR uX
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq T] [DecidableEq O]
  (A : SubstitutionAction T S) (program : Set (RuleInstance T))

abbrev Proof (assignment : S) (before : Multiset T) (goal : TensorSequent.Formula T) :=
  (LinearHornAdequacy.system A program assignment).TensorProof (TensorSequent.atomContext before) goal

theorem pure_schedule_iff_tensor_sequent (assignment : S) (label : O → T) (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations) (goal : TensorSequent.Formula T) :
    (∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label before schedule ∧ LinearHornAdequacy.Pure schedule ∧
      LinearHornAdequacy.Declared program schedule ∧
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations ∧
      labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present = goal.atoms) ↔
        Nonempty (Proof A program assignment (labels (realized A assignment label) before.present) goal) := by
  have source := LinearHornAdequacy.pure_schedule_iff_horn_proof A program assignment label structural supply
    before oldModel goal.atoms
  have target := TensorSequent.provable_iff_horn
    (premises := fun entry : (LinearHornAdequacy.system A program assignment).Entry =>
      (LinearHornAdequacy.system A program assignment).consume entry.2)
    (conclusions := fun entry : (LinearHornAdequacy.system A program assignment).Entry =>
      (LinearHornAdequacy.system A program assignment).produce entry.2)
    (TensorSequent.atomContext (labels (realized A assignment label) before.present)) goal
  simp only [TensorSequent.contextAtoms_atomContext] at target
  exact source.trans target.symm

variable {R : Type uR} {X : Type uX}
  (activate : R → X → Option (RuleInstance T)) (installed : Set R)

abbrev ActivatedProof (assignment : S) (before : Multiset T) (goal : TensorSequent.Formula T) :=
  (ActivatedHornProofs.system A activate installed assignment).TensorProof (TensorSequent.atomContext before) goal

theorem activated_schedule_to_sequent (assignment : S) (label : O → T) (structural : A.E = Eq)
    (selected : List (ActivatedHornProofs.Selected (O := O) activate installed)) (before : Configuration T O)
    (executes : ConditionalSchedule.Executable A label before (selected.map (ActivatedHornProofs.ordinary activate installed)))
    (pure : LinearHornAdequacy.Pure (selected.map (ActivatedHornProofs.ordinary activate installed)))
    (solved : A.Models assignment
      (ConditionalSchedule.follow label before (selected.map (ActivatedHornProofs.ordinary activate installed))).equations) :
    ∃ proof : ActivatedProof A activate installed assignment (labels (realized A assignment label) before.present)
        (TensorSequent.Formula.ofMultiset (labels (realized A assignment label)
          (ConditionalSchedule.follow label before (selected.map (ActivatedHornProofs.ordinary activate installed))).present)),
      proof.uses.map (ActivatedHornProofs.originOf A activate installed assignment) = selected.map Prod.fst := by
  obtain ⟨diagram, origins⟩ := ActivatedHornProofs.proof_of_schedule A activate installed assignment label structural
    selected before executes pure solved
  obtain ⟨proof, sameUses⟩ := TensorSequent.ofHornAtomic diagram
  exact ⟨proof, (congrArg (List.map (ActivatedHornProofs.originOf A activate installed assignment)) sameUses).trans origins⟩

/-- The formula-sequent proof is materially sequentialized back to actual
CMR selections. Its installed-schema/activation-origin list is retained. -/
theorem activated_sequent_to_schedule (assignment : S) (label : O → T) (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (before : Configuration T O) (oldModel : A.Models assignment before.equations)
    (goal : TensorSequent.Formula T)
    (proof : ActivatedProof A activate installed assignment (labels (realized A assignment label) before.present) goal) :
    ∃ selected : List (ActivatedHornProofs.Selected (O := O) activate installed),
      ConditionalSchedule.Executable A label before (selected.map (ActivatedHornProofs.ordinary activate installed)) ∧
      LinearHornAdequacy.Pure (selected.map (ActivatedHornProofs.ordinary activate installed)) ∧
      A.Models assignment
        (ConditionalSchedule.follow label before (selected.map (ActivatedHornProofs.ordinary activate installed))).equations ∧
      labels (realized A assignment label)
        (ConditionalSchedule.follow label before (selected.map (ActivatedHornProofs.ordinary activate installed))).present = goal.atoms ∧
      selected.map Prod.fst = proof.uses.map (ActivatedHornProofs.originOf A activate installed assignment) := by
  obtain ⟨diagram, sameUses⟩ := TensorSequent.toHornAtomic proof
  obtain ⟨selected, executes, pure, solved, boundary, origins⟩ :=
    ActivatedHornProofs.schedule_of_proof A activate installed assignment label structural supply before oldModel goal.atoms diagram
  exact ⟨selected, executes, pure, solved, boundary,
    origins.trans (congrArg (List.map (ActivatedHornProofs.originOf A activate installed assignment)) sameUses)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TensorSequentAdequacy
