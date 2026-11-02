import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPublishedInstantiation
import Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotPhysicalControls
import Mettapedia.Languages.HOLLight.RegisteredSubstitution

/-!
# A genuinely changed source instance installs from an actual publication

The existing polymorphic reflexivity source control is published through the
actual private snapshot interaction. Its source type substitution changes the
conclusion and has an actual subsequent finite catalog activation. An unused
unregistered type maplet remains rejected by the original formation check.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotInstantiationControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (action)
open DefinitionAdapters.ContextControls
open HOLLightSnapshotData HOLLightSnapshotAdmission HOLLightSnapshotActivation HOLLightSnapshotExecution
open HOLLightSnapshotPhysicalControls
open HOLLightSnapshotAdmissionCompleteness HOLLightSnapshotPublishedInstantiation

local instance : DecidablePred emptyAxiomPolicy := fun _ => .isFalse id

abbrev sourceCommand := RegisteredSubstitution.Controls.inputCommand
abbrev sourceFact := RegisteredSubstitution.Controls.inputFact
abbrev sourceNode := RegisteredSubstitution.Controls.inputNode

theorem original_command_checked : sourceCommand.check emptyAxiomPolicy coreContext #[] =
    some ⟨coreContext, [sourceFact]⟩ := by
  have gate : requestFormedB coreContext.signature (ExportReplay.instanceCertificates coreContext.signature) sourceNode.witness = true ∧
      theoremFormedB coreContext.signature (ExportReplay.instanceCertificates coreContext.signature) sourceNode.conclusion = true :=
    ⟨RegisteredSubstitution.Controls.input_parameters, RegisteredSubstitution.Controls.input_result_formed⟩
  simp only [RegisteredSubstitution.Controls.inputCommand, Command.check, RegisteredSubstitution.Controls.input_replayed,
    Bind.bind, Option.bind]
  rw [if_pos gate]
  rfl

theorem exists_actual_polymorphic_publication :
    ∃ publication : Publication coreContext emptyAxiomPolicy coreContext location payload,
      publication.fact = sourceFact ∧ publication.sourceContext = coreContext := by
  let output : Output := ⟨coreContext, [sourceFact]⟩
  let data := HOLLightFiniteCommandData.encode sourceCommand (HOLLightFiniteCommandWitnesses.sampleCommand sourceCommand output)
  obtain ⟨prepared, computed, outputSame, _, parentSame⟩ := every_checked_command_installs emptyAxiomPolicy
    HOLLightSnapshotControls.beforeSnapshot 0 coreContext (initial_context MeTTa.DeclarationTable.core) rfl #[] sourceCommand output original_command_checked
  have parentLookup := prepare_origin emptyAxiomPolicy HOLLightSnapshotControls.beforeSnapshot 0 data #[] computed
  obtain ⟨_, _, command, _, _, parents, _, _, _, _, selected, samePrepared⟩ := parentLookup
  have actualLookup : Mettapedia.Logic.DerivationGraph.lookupPremises (#[] : Array Theorem) prepared.command.parents = some prepared.parents := by
    rw [samePrepared]
    exact selected
  have noParents : prepared.parents = [] := by
    rw [parentSame] at actualLookup
    exact (Option.some.inj actualLookup).symm
  let request : Occurrence := (12, requests, installRequest 0 data #[])
  let world : Configuration Value Occurrence := ⟨[], {snapshotOccurrence, request, rootOccurrence}⟩
  have background : locatedAction.Consistent world.equations := ⟨action.identity, by simp [world]⟩
  obtain ⟨picked, _, qualified⟩ := install_selection HOLLightSnapshotControls.beforeSnapshot 0 data #[] prepared world background
    snapshotOccurrence request (by simp [world]) (by simp [world]) rfl rfl (by
      intro fact member
      rw [noParents] at member
      cases member)
  obtain ⟨assignment, solved⟩ := qualified.consistent
  have outputMember : (judgments, HOLLightContextActivation.theoremPayload prepared.after sourceFact) ∈
      (installRule HOLLightSnapshotControls.beforeSnapshot 0 data #[] prepared).produce := by
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨sourceFact, by rw [outputSame]; simp [output], rfl⟩
  rw [← qualified.outputs] at outputMember
  obtain ⟨occurrence, made, same⟩ := List.mem_map.mp outputMember
  have readEmpty : picked.read = [] := List.length_eq_zero_iff.mp (by
    simpa [installRule, noParents] using qualified.read_length.symm)
  let publication : Publication coreContext emptyAxiomPolicy coreContext location payload :=
    { snapshot := HOLLightSnapshotControls.beforeSnapshot
      valid := HOLLightSnapshotPublication.initial_valid coreContext emptyAxiomPolicy coreContext MeTTa.DeclarationTable.core
      beforeId := 0
      data := data
      cache := #[]
      prepared := prepared
      computed := computed
      world := world
      picked := picked
      qualified := qualified
      assignment := assignment
      solved := solved
      incoming := by
        intro sourceContext contextKnown item member
        rw [readEmpty] at member
        cases member
      occurrence := occurrence
      made := made
      protectedHere := congrArg Prod.fst same
      contextId := prepared.after
      fact := sourceFact
      observed := by
        change action.apply assignment (label occurrence).2 = _
        rw [congrArg Prod.snd same, HOLLightContextActivation.theoremPayload_fixed] }
  refine ⟨publication, rfl, ?_⟩
  change prepared.output.context = coreContext
  rw [outputSame]

def middle := substituteTheorem (RegisteredSubstitution.typePart RegisteredSubstitution.Controls.substitution) sourceFact

theorem type_instance_changes_conclusion : middle.sequent.concl ≠ sourceFact.sequent.concl := by decide +kernel

theorem changed_type_instance_really_installs :
    ∃ (publication : Publication coreContext emptyAxiomPolicy coreContext location payload)
      (data : Mettapedia.OSLF.Binding.WireCodec.Data) (next : Prepared),
      publication.fact = sourceFact ∧
      prepare emptyAxiomPolicy publication.prepared.snapshot publication.contextId data #[publication.fact] = some next ∧
      next.output.theorems = [middle] ∧ middle.sequent.concl ≠ sourceFact.sequent.concl := by
  obtain ⟨publication, factSame, contextSame⟩ := exists_actual_polymorphic_publication
  let maplets := PrimitiveTransport.typeEntries RegisteredSubstitution.Controls.substitution.raw.types
  have checked : (InferenceRequest.instType maplets publication.fact).check = some middle := by
    rw [factSame]
    exact RegisteredSubstitution.first_checked _ _
  have arguments : InferenceFormation.Formed publication.sourceContext.signature (.instType maplets publication.fact) := by
    rw [contextSame, factSame]
    exact RegisteredSubstitution.Controls.closed_type_parameters
  have formed : TheoremFormed publication.sourceContext.signature middle := by
    rw [contextSame]
    exact RegisteredSubstitution.Controls.closed_type_stage
  obtain ⟨data, next, computed, _, outputSame, _⟩ := publication.every_type_instance_installs maplets middle ("coupled-instance", 1) checked arguments formed
  exact ⟨publication, data, next, factSame, computed, outputSame, type_instance_changes_conclusion⟩

theorem unused_unregistered_type_refused (certificates : SignatureFormation.InstanceWitnesses) :
    requestFormedB coreContext.signature certificates
      (.inference (.instType [(RegisteredSubstitution.Controls.unsupported, .var (Name.global "unused"))] sourceFact)) = false := by
  have unformed : SignatureFormation.typeFormedB coreContext.signature RegisteredSubstitution.Controls.unsupported = false := by decide +kernel
  simp [requestFormedB, InferenceFormation.check, InferenceFormation.types, unformed]

end Mettapedia.Logic.TierZero.Adequacy.HOLLightSnapshotInstantiationControls
