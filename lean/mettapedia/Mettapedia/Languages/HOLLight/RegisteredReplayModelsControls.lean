import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.RegisteredPointedModels
import Mettapedia.Languages.HOLLight.DefinitionReplayModels
import Mettapedia.Languages.HOLLight.CheckedInferenceTrace

/-!
# Replay-to-model controls

Relative transitivity retains both actual source hypotheses. The constructed
model theorem consumes the existing two-constant replay and the actual pointed
type program. An independently translated falsity theorem is excluded from
that interpreted cache. These controls do not interpret the retained source
profile's additional axiom commitments.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredReplayModels.Controls
open ProofExecution Registered DefinitionModelFamily
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation TypeFamilySemantics
open ModelInterpretation DefinitionModelFamily
open MixedDefinitionModelFamily.Controls (primitives)

attribute [local instance] PointedPredicateTemplate.instDecidablePredSequentEmptyAxiomPolicy

def first : CanonicalTerm := CanonicalTerm.free ⟨Name.global "relativeFirst",Ty.bool⟩
def middle : CanonicalTerm := CanonicalTerm.free ⟨Name.global "relativeMiddle",Ty.bool⟩
def last : CanonicalTerm := CanonicalTerm.free ⟨Name.global "relativeLast",Ty.bool⟩
def firstEquality : CanonicalTerm := CanonicalTerm.equalityOfSameType first middle rfl
def secondEquality : CanonicalTerm := CanonicalTerm.equalityOfSameType middle last rfl
def resultEquality : CanonicalTerm := CanonicalTerm.equalityOfSameType first last rfl
def left : Theorem := Theorem.emptyResult {firstEquality} firstEquality
def right : Theorem := Theorem.emptyResult {secondEquality} secondEquality
def combined : Theorem := Theorem.emptyResult ({firstEquality} ∪ {secondEquality}) resultEquality
def droppedHypotheses : Theorem := Theorem.emptyResult ∅ resultEquality

theorem trans_checked : checkTrans left right = some combined := by decide +kernel

theorem left_proven : TranslatedProvable ∅ left.sequent :=
  (translatedProvable_iff_compositionallyProvable _ _).mpr (compositionallyProvable_assume rfl)

theorem right_proven : TranslatedProvable ∅ right.sequent :=
  (translatedProvable_iff_compositionallyProvable _ _).mpr (compositionallyProvable_assume rfl)

theorem trans_proven : TranslatedProvable ∅ combined.sequent :=
  InferenceInterpretation.trans ((checkTrans_eq_some_iff _ _ _).mp trans_checked) left_proven right_proven

theorem inference_proven : TranslatedProvable ∅ combined.sequent := by
  apply InferenceInterpretation.inference variableFreeSubstitutionClosed_empty
    (request := .trans left right) ((checkTrans_eq_some_iff _ _ _).mp trans_checked)
  · intro input member
    simp only [InferenceRequest.premises,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact left_proven
    · exact right_proven
  · simp [combined,Theorem.emptyResult]

theorem dropped_hypotheses_refused : checkTrans left right ≠ some droppedHypotheses := by decide +kernel

theorem pointed_models (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      model.FullDomains ∧
      (∃ formula, Translates [] RegisteredPointedTypeDefinition.Controls.emptyResult.definition.output.abstractionRepresentationTheorem.sequent.concl.term .prop formula ∧ model.models formula) ∧
      (∃ formula, Translates [] RegisteredPointedTypeDefinition.Controls.emptyResult.definition.output.representationAbstractionTheorem.sequent.concl.term .prop formula ∧ model.models formula) :=
  RegisteredPointedModels.introduce_laws_models
    RegisteredPointedTypeDefinition.Controls.emptyProperty
    RegisteredPointedTypeDefinition.Controls.typeName
    RegisteredPointedTypeDefinition.Controls.abstractionName
    RegisteredPointedTypeDefinition.Controls.representationName
    ContextControls.coreContext primitives
    RegisteredPointedTypeDefinition.Controls.emptyResult_received other assignment

theorem pointed_available_models (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    ∃ result, RegisteredPointedTypeDefinition.introduce RegisteredPointedTypeDefinition.Controls.emptyProperty
      RegisteredPointedTypeDefinition.Controls.typeName RegisteredPointedTypeDefinition.Controls.abstractionName
      RegisteredPointedTypeDefinition.Controls.representationName ContextControls.coreContext = some result ∧
      ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
        model.FullDomains ∧
        (∃ formula, Translates [] result.definition.output.abstractionRepresentationTheorem.sequent.concl.term .prop formula ∧ model.models formula) ∧
        (∃ formula, Translates [] result.definition.output.representationAbstractionTheorem.sequent.concl.term .prop formula ∧ model.models formula) :=
  RegisteredPointedModels.introduce_available_models
    RegisteredPointedTypeDefinition.Controls.emptyProperty
    RegisteredPointedTypeDefinition.Controls.typeName
    RegisteredPointedTypeDefinition.Controls.abstractionName
    RegisteredPointedTypeDefinition.Controls.representationName
    ContextControls.coreContext primitives ⟨fun _ _ h => h,fun _ _ h => h⟩
    RegisteredPointedPredicate.Controls.boolean_formed RegisteredPointedPredicate.Controls.empty_property_formed
    RegisteredPointedTypeDefinition.Controls.names_fresh RegisteredPointedTypeDefinition.Controls.property_closed other assignment

theorem pointed_frame_exists : Nonempty (Frame.{0} ContextControls.coreContext emptyAxiomPolicy
    RegisteredPointedTypeDefinition.Controls.emptyResult.state.context
    RegisteredPointedTypeDefinition.Controls.emptyResult.state.cache) :=
  RegisteredPointedModels.introduce_frame
    RegisteredPointedTypeDefinition.Controls.emptyProperty
    RegisteredPointedTypeDefinition.Controls.typeName
    RegisteredPointedTypeDefinition.Controls.abstractionName
    RegisteredPointedTypeDefinition.Controls.representationName
    ContextControls.coreContext primitives RegisteredPointedTypeDefinition.Controls.emptyResult_received

noncomputable def pointedFrame : Frame.{0} ContextControls.coreContext emptyAxiomPolicy
    RegisteredPointedTypeDefinition.Controls.emptyResult.state.context
    RegisteredPointedTypeDefinition.Controls.emptyResult.state.cache :=
  Classical.choice pointed_frame_exists

def falseFact : Theorem := Theorem.emptyResult ∅ Mettapedia.Languages.OpenTheory.falsity

theorem pointed_falsity_refused (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    falseFact ∉ RegisteredPointedTypeDefinition.Controls.emptyResult.state.cache :=
  pointedFrame.cached_falsity_refused other assignment falseFact rfl PrimitiveSentences.falsityDB_translates

theorem constant_models (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    ∃ model : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      model.FullDomains ∧ ∀ fact ∈ DefinitionReplayModels.Controls.after.cache,
        ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
          ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) :=
  replay_models SourceProfile.primitiveContext SourceProfileModels.primitives
    DefinitionReplayModels.Controls.commands DefinitionReplayModels.Controls.after
    DefinitionReplayModels.Controls.commands_replayed other assignment

def retentionNode : Receipt :=
  ⟨ContextControls.identityExistence,.inference (.refl DefinitionAdapters.Controls.identityTerm),[],("model-retention",0)⟩

def retentionInstances : InstanceWitnesses := ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature

theorem retention_available :
    ((Command.proof retentionNode retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[]).isSome = true := by
  decide +kernel

def retentionOutput : Output :=
  ((Command.proof retentionNode retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[]).get retention_available

theorem retention_accepted :
    (Command.proof retentionNode retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[] = some retentionOutput :=
  (Option.some_get retention_available).symm

noncomputable def retentionFrame : Frame.{0} SourceProfile.primitiveContext emptyAxiomPolicy SourceProfile.primitiveContext #[] :=
  Frame.empty SourceProfileModels.primitives (by intro sequent forbidden; cases forbidden)

theorem retention_model (other : OperatorFamilies.{0}) (assignment : Assignment.{0}) :
    (Frame.proof retentionFrame retentionNode retentionInstances retentionOutput retention_accepted).family.model other assignment =
      retentionFrame.family.model other assignment :=
  Frame.proof_model retentionFrame retentionNode retentionInstances retentionOutput retention_accepted other assignment

theorem retention_cache_grows : retentionOutput.theorems.length = 1 := by decide +kernel

def forgedRetention : Receipt := { retentionNode with conclusion := Theorem.emptyResult ∅ Mettapedia.Languages.OpenTheory.falsity }

theorem forged_retention_refused :
    (Command.proof forgedRetention retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[] = none := by
  decide +kernel

private def reflexiveRequest : InferenceRequest := .refl DefinitionAdapters.Controls.identityTerm
private def repeatedRequest : InferenceRequest :=
  .trans ContextControls.identityExistence ContextControls.identityExistence

private def formRetention (request : RuleRequest) (fact : Theorem) : Bool :=
  let signature := SourceProfile.primitiveContext.signature
  requestFormedB signature retentionInstances request &&
    theoremFormedB signature retentionInstances fact

checked_hol_trace repeated emptyAxiomPolicy formRetention ("repeated-premise", 0) [
  ContextControls.identityExistence reflexiveRequest [],
  ContextControls.identityExistence repeatedRequest [0, 0],
  ContextControls.identityExistence repeatedRequest [0, 0]
]

example : repeated_suffix0.map (·.parents) = [[], [0, 0], [0, 0]] := rfl

example : repeated_suffix0.all (fun node => formRetention node.witness node.conclusion) = true :=
  repeated_trace0.formed

private def futurePremise : Receipt := { repeated_node1 with parents := [1, 1] }

example : futurePremise.replay (ruleWitness emptyAxiomPolicy) repeated_cache1 = none := rfl


def verdicts : List (String × Bool) :=
  [("registered-models/proof-received", (Command.proof retentionNode retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[] |>.isSome),
   ("registered-models/proof-cache-grows", decide (retentionOutput.theorems.length = 1)),
   ("registered-models/forged-proof-refused", (Command.proof forgedRetention retentionInstances).check emptyAxiomPolicy SourceProfile.primitiveContext #[] |>.isNone),
   ("relative-trans/retained-hypotheses",decide (checkTrans left right = some combined)),
   ("relative-trans/dropped-hypotheses-refused",decide (checkTrans left right ≠ some droppedHypotheses))]

#print axioms trans_proven
#print axioms inference_proven
#print axioms dropped_hypotheses_refused
#print axioms pointed_models
#print axioms pointed_falsity_refused
#print axioms constant_models
end Mettapedia.Languages.HOLLight.RegisteredReplayModels.Controls
