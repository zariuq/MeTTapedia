import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.PacketQuotationExtensions

/-!
# Isolated policy, substitution-ledger and declaration controls

These closed source-kernel histories exercise the extension helpers. They
are not imports of the native packet's later AXIOM or TYPE_DEFINITION rows.
The staged real packet prefix separately qualifies its actual INST_TYPE.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationExtensionControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation

namespace IsolatedAxiom

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def selected : Sequent := SourceProfileModels.commitments[0]

theorem selected_bool : selected.IsBool := by
  apply (Sequent.isBoolB_eq_true_iff _).mp
  decide +kernel

theorem selected_allowed : SourceProfileModels.policy selected := by decide +kernel

def fact : Theorem := Theorem.axiomResult selected selected_bool
def request : RuleRequest := .axiom selected

theorem requested : request.check SourceProfileModels.policy = some fact :=
  PacketQuotationExtensions.axiom_request_checked SourceProfileModels.policy selected rfl
    selected_allowed selected_bool

def instances : InstanceWitnesses :=
  ExportReplay.instanceCertificates SourceProfileModels.referenceState.context.signature
def node : Receipt := ⟨fact, request, [], ("isolated-axiom-quotation", 0)⟩
def command : Registered.Command := .proof node instances

theorem checked : command.check SourceProfileModels.policy
    SourceProfileModels.referenceState.context SourceProfileModels.referenceState.cache =
      some ⟨SourceProfileModels.referenceState.context, [fact]⟩ := by
  have replayed : node.replay (ruleWitness SourceProfileModels.policy)
      SourceProfileModels.referenceState.cache =
        some (SourceProfileModels.referenceState.cache.push fact) := by
    apply (ProofSystem.node_replay_iff SourceProfileModels.policy _ _ _).mpr
    exact ⟨rfl, requested, rfl⟩
  have shaped : theoremFormedB SourceProfileModels.referenceState.context.signature instances fact = true := by
    decide +kernel
  have parameters : Registered.requestFormedB SourceProfileModels.referenceState.context.signature
      instances node.witness = true := rfl
  change (do
    let _ ← node.replay (ruleWitness SourceProfileModels.policy) SourceProfileModels.referenceState.cache
    if Registered.requestFormedB SourceProfileModels.referenceState.context.signature instances node.witness = true ∧
        theoremFormedB SourceProfileModels.referenceState.context.signature instances node.conclusion = true then
      some (⟨SourceProfileModels.referenceState.context, [node.conclusion]⟩ : Registered.Output)
    else none) = _
  rw [replayed]
  change (if Registered.requestFormedB SourceProfileModels.referenceState.context.signature instances node.witness = true ∧
      theoremFormedB SourceProfileModels.referenceState.context.signature instances node.conclusion = true then
    some (⟨SourceProfileModels.referenceState.context, [node.conclusion]⟩ : Registered.Output)
    else none) = _
  rw [if_pos ⟨parameters, shaped⟩]
  rfl

def after : Registered.State :=
  ⟨SourceProfileModels.referenceState.context, SourceProfileModels.referenceState.cache ++ #[fact],
    SourceProfileModels.referenceState.receipts.push ⟨command, [fact]⟩⟩

theorem applied : Registered.apply SourceProfileModels.policy SourceProfileModels.referenceState command =
    some after :=
  PacketQuotation.apply_checked_cache SourceProfileModels.policy SourceProfileModels.referenceState
    command _ _ checked rfl

theorem reference_policy : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) SourceProfileModels.referenceCommands =
      some SourceProfileModels.referenceState := by
  rw [← Registered.replayFrom_policy_congr emptyAxiomPolicy SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext) SourceProfileModels.referenceCommands]
  · exact SourceProfileModels.reference_replayed
  · intro current member sequent asked
    simp only [SourceProfileModels.referenceCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases asked

theorem closed_history : Registered.replayFrom SourceProfileModels.policy
    (Registered.empty SourceProfile.primitiveContext)
    (SourceProfileModels.referenceCommands ++ [command]) = some after := by
  apply Registered.replayFrom_append_accepted SourceProfileModels.policy reference_policy
  simp only [Registered.replayFrom, applied, bind, Option.bind]

theorem dependency_is_retained : fact.axioms = {selected} := rfl

def unlisted : Sequent := ⟨∅, Mettapedia.Languages.OpenTheory.falsity⟩
theorem unlisted_refused : (RuleRequest.axiom unlisted).check SourceProfileModels.policy = none := by
  decide +kernel

def erased : Theorem := Theorem.emptyResult selected.hyp selected.concl
def erasedNode : Receipt := { node with conclusion := erased }
theorem erased_ledger_refused : (Registered.Command.proof erasedNode instances).check
    SourceProfileModels.policy SourceProfileModels.referenceState.context
    SourceProfileModels.referenceState.cache = none := by decide +kernel

end IsolatedAxiom

namespace IsolatedSubstitutionLedger

def entries : List (Ty × Ty) := [(Ty.bool, .var (.global "A"))]
def result : Theorem := substituteTheorem (SourceSubstitution.typeOnlySubstitution entries) IsolatedAxiom.fact

theorem checked : (InferenceRequest.instType entries IsolatedAxiom.fact).check = some result := rfl
theorem original_tags : result.axioms = IsolatedAxiom.fact.axioms := rfl
theorem current_sequent_changes : result.sequent ≠ IsolatedAxiom.fact.sequent := by decide +kernel
theorem tags_are_not_rewritten : result.axioms ≠ {result.sequent} := by decide +kernel

end IsolatedSubstitutionLedger

namespace IsolatedTypeDefinition

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def before : Registered.State := Registered.Controls.withExistence
def request : TypeOperatorDefinitionRequest := ContextControls.identityTypeRequest
def result : SourceTypeDefinitionResult := Registered.Controls.definedType
def instances : InstanceWitnesses := ExportReplay.instanceCertificates result.context.signature

theorem available : (admitSourceTypeInTheory before.context instances request).isSome = true := by
  decide +kernel
theorem formed : theoremFormedB result.context.signature instances
    result.output.abstractionRepresentationTheorem = true ∧
    theoremFormedB result.context.signature instances result.output.representationAbstractionTheorem = true := by
  decide +kernel

def command : Registered.Command := .typeDefinition ("isolated-type-quotation", 0) request 0 instances

theorem checked : command.check emptyAxiomPolicy before.context before.cache =
    some ⟨result.context, [result.output.abstractionRepresentationTheorem,
      result.output.representationAbstractionTheorem]⟩ :=
  PacketQuotationExtensions.type_definition_checked emptyAxiomPolicy before Registered.Controls.certificates
    request result 0 ("isolated-type-quotation", 0) Registered.Controls.defined_type_admitted
    available rfl formed

def after : Registered.State :=
  ⟨result.context, before.cache ++ #[result.output.abstractionRepresentationTheorem,
    result.output.representationAbstractionTheorem],
    before.receipts.push ⟨command, [result.output.abstractionRepresentationTheorem,
      result.output.representationAbstractionTheorem]⟩⟩

theorem applied : Registered.apply emptyAxiomPolicy before command = some after :=
  PacketQuotationExtensions.type_definition_apply emptyAxiomPolicy before Registered.Controls.certificates
    request result 0 ("isolated-type-quotation", 0) _ Registered.Controls.defined_type_admitted
    available rfl formed rfl

theorem closed_history : Registered.replayFrom emptyAxiomPolicy
    (Registered.empty ContextControls.coreContext) [Registered.Controls.existenceCommand, command] = some after := by
  have step : Registered.apply emptyAxiomPolicy Registered.Controls.withExistence command = some after := by
    simpa only [before] using applied
  simp only [Registered.replayFrom, Registered.Controls.existence_applied, step, bind, Option.bind]

theorem both_positions : after.cache[1]? = some result.output.abstractionRepresentationTheorem ∧
    after.cache[2]? = some result.output.representationAbstractionTheorem := by constructor <;> rfl

theorem missing_existence_refused : command.check emptyAxiomPolicy before.context #[] = none := rfl
theorem wrong_existence_address_refused :
    (Registered.Command.typeDefinition ("isolated-wrong-existence", 0) request 1 instances).check
      emptyAxiomPolicy before.context before.cache = none := rfl
theorem swapped_outputs_refused : ExportReplay.claimsSame
    [result.output.representationAbstractionTheorem.sequent, result.output.abstractionRepresentationTheorem.sequent]
    [result.output.abstractionRepresentationTheorem, result.output.representationAbstractionTheorem] = false := by
  decide +kernel

end IsolatedTypeDefinition

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationExtensionControls
