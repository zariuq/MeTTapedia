import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublication
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls

/-!
# Independent source extraction from the complete actual coupled firing

Only the selected protected existence theorem supplies proof authority. The
canonical successor registry and both output theorems are independently
justified after the physical interaction. A client retains no private take
or publication authority merely by possessing the public command data.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublicationControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.MeTTa
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (action)
open DefinitionAdapters.ContextControls ProofExecution.Registered.Controls
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation HOLLightSnapshotExecution
open HOLLightSnapshotControls HOLLightSnapshotPhysicalControls
open HOLLightSnapshotPublication

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

theorem before_snapshot_valid : Valid coreContext emptyAxiomPolicy coreContext beforeSnapshot :=
  initial_valid coreContext emptyAxiomPolicy coreContext DeclarationTable.core

theorem coupled_firing_earns_independent_source :
    Valid coreContext emptyAxiomPolicy coreContext prepared.snapshot ∧
      TheoryDerives emptyAxiomPolicy definedType.context definedType.output.abstractionRepresentationTheorem ∧
      TheoryDerives emptyAxiomPolicy definedType.context definedType.output.representationAbstractionTheorem := by
  obtain ⟨picked, _, qualified⟩ := actual_selection_computed
  obtain ⟨assignment, solved⟩ := qualified.consistent
  have incoming : ∀ sourceContext, context beforeSnapshot 0 = some sourceContext → ∀ occurrence ∈ picked.read,
      location occurrence = judgments → ∀ fact,
        action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload 0 fact →
          TheoryDerives emptyAxiomPolicy sourceContext fact := by
    intro sourceContext contextKnown occurrence selected atJudgments fact observed
    have sameContext : sourceContext = coreContext := Option.some.inj (contextKnown.symm.trans (initial_context DeclarationTable.core))
    subst sourceContext
    have present := qualified.occurrences.kept_subset (by simpa [Selection.commit] using selected)
    have cases : occurrence = snapshotOccurrence ∨ occurrence = requestOccurrence ∨ occurrence = existenceOccurrence ∨
        occurrence = rootOccurrence ∨ occurrence = runOccurrence := by simpa [initialWorld] using present
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · cases atJudgments
    · cases atJudgments
    · change action.apply assignment (HOLLightContextActivation.theoremPayload 0 identityExistence) =
        HOLLightContextActivation.theoremPayload 0 fact at observed
      rw [HOLLightContextActivation.theoremPayload_fixed] at observed
      have sameFact := (HOLLightContextActivation.theoremPayload_injective observed).2
      subst fact
      exact withExistence_valid identityExistence (by simp [withExistence])
    · cases atJudgments
    · cases atJudgments
  have publication := coupled_publication_preserves_source_authority coreContext emptyAxiomPolicy coreContext beforeSnapshot
    before_snapshot_valid 0 HOLLightFiniteCommandControls.typeData #[identityExistence] preparation_computed
    location payload qualified assignment solved incoming
  have produced : ∀ fact ∈ output.theorems, TheoryDerives emptyAxiomPolicy definedType.context fact := by
    intro fact member
    have outputMember : (judgments, HOLLightContextActivation.theoremPayload prepared.after fact) ∈
        (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared).produce :=
      List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨fact, member, rfl⟩))
    rw [← qualified.outputs] at outputMember
    obtain ⟨occurrence, made, same⟩ := List.mem_map.mp outputMember
    have place : location occurrence = judgments := congrArg Prod.fst same
    have observed : action.apply assignment (payload occurrence) = HOLLightContextActivation.theoremPayload prepared.after fact := by
      change action.apply assignment (label occurrence).2 = _
      rw [congrArg Prod.snd same, HOLLightContextActivation.theoremPayload_fixed]
    obtain ⟨sourceContext, contextKnown, _, proof⟩ := publication.2.2 occurrence made place prepared.after fact observed
    have sameContext : sourceContext = definedType.context := Option.some.inj (contextKnown.symm.trans exact_new_context)
    exact sameContext ▸ proof
  exact ⟨publication.1, produced _ (by simp [output, HOLLightContextControls.TypeDefinition.output]),
    produced _ (by simp [output, HOLLightContextControls.TypeDefinition.output])⟩

theorem every_client_step_retains_private_snapshot {before after : Configuration Value Occurrence}
    (stepped : InteractionFormation.SchemaStep authority (activate emptyAxiomPolicy) action payload false before after)
    (present : snapshotOccurrence ∈ before.present) : snapshotOccurrence ∈ after.present :=
  InteractionFormation.no_receive_retains_occurrence stepped snapshotOccurrence present rfl

theorem client_cannot_publish_coupled_result (world : Configuration Value Occurrence) (picked : Selection Occurrence)
    (qualified : picked.Valid locatedAction label
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) world) :
    ¬InteractionFormation.Formed clientRights label picked
      (installRule beforeSnapshot 0 HOLLightFiniteCommandControls.typeData #[identityExistence] prepared) :=
  denied_send_cannot_publish_successor clientRights location payload beforeSnapshot 0 HOLLightFiniteCommandControls.typeData
    #[identityExistence] prepared world picked qualified rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublicationControls
