import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics

/-!
# The hot call-guard ABI: state-carrying StructuredC semantics of the executor

The executor state travels as one ABI value in the `state` slot of the
StructuredC environment.  The external primitives are of four kinds:

* projections read one slot of the current state;
* frame queries decide the structural branch the generated dispatcher takes;
* decisions answer the thirteen relation premises of the hot rules on
  supplied operands;
* deltas write the next state from supplied operands, and only when those
  operands agree with the current state.

Every primitive has one exactness lemma against the executor's own
definitions.  Nothing here reads a transition table: the deltas are the
right-hand sides of the hot rules, one per shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
  (abiValue abiPayload? decodeAbiWith? valueUnit readyReceipt externalReceipt)

/-! ## The state value -/

def stateValue (control : ExecuteControl) : Pattern :=
  abiValue (encodeExecuteControl control)

def decodeStateValue? (value : Pattern) : Option ExecuteControl :=
  decodeAbiWith? decodeExecuteControl? value

@[simp] theorem decodeStateValue_stateValue (control : ExecuteControl) :
    decodeStateValue? (stateValue control) = some control := by
  simp [decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]

def initialEnvironment (control : ExecuteControl) : Pattern :=
  bindName "state" (stateValue control) environmentEmpty

/-- The supplied state operand must be the state bound in the environment. -/
def currentStateArgument? (environment supplied : Pattern) : Option ExecuteControl := do
  let stored ← lookup? environment (identifier "state")
  if stored = supplied then decodeStateValue? supplied else none

theorem currentStateArgument?_exact (control : ExecuteControl) (environment : Pattern)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    currentStateArgument? environment (stateValue control) = some control := by
  simp [currentStateArgument?, stored]

/-! ## Operand values -/

def ownerValue (owner : SpaceOwner) : Pattern := abiValue (encodeOwner owner)
def natValue (value : Nat) : Pattern := abiValue (encodeNat value)
def nameValue (name : String) : Pattern := abiValue (encodeName name)
def termValue (term : Term) : Pattern := abiValue (encodeTerm term)
def termsValue (terms : List Term) : Pattern := abiValue (encodeTerms terms)
def snapshotValue (snapshot : Snapshot) : Pattern := abiValue (encodeSnapshot snapshot)
def callValue (call : Call) : Pattern := abiValue (encodeCall call)
def plansValue (plans : List GuardPlan) : Pattern := abiValue (encodeHotPlans plans)
def modesValue (modes : List ArgMode) : Pattern := abiValue (encodeModes modes)
def resultModeValue (mode : ResultMode) : Pattern := abiValue (encodeResultMode mode)
def acceptedValue (accepted : List ArrowDeclaration) : Pattern :=
  abiValue (encodeAccepted accepted)
def eventsValue (events : List ControlEvent) : Pattern := abiValue (encodeEvents events)
def indexValue (index : Nat) : Pattern := abiValue (encodeIndex index)

def decodeOwnerValue? : Pattern → Option SpaceOwner := decodeAbiWith? decodeOwner?
def decodeNatValue? : Pattern → Option Nat := decodeAbiWith? decodeNat?
def decodeNameValue? : Pattern → Option String := decodeAbiWith? decodeName?
def decodeTermValue? : Pattern → Option Term := decodeAbiWith? decodeTerm?
def decodeTermsValue? : Pattern → Option (List Term) := decodeAbiWith? decodeTerms?
def decodeSnapshotValue? : Pattern → Option Snapshot := decodeAbiWith? decodeSnapshot?
def decodeCallValue? : Pattern → Option Call := decodeAbiWith? decodeCall?
def decodePlansValue? : Pattern → Option (List GuardPlan) := decodeAbiWith? decodeHotPlans?
def decodeModesValue? : Pattern → Option (List ArgMode) := decodeAbiWith? decodeModes?
def decodeResultModeValue? : Pattern → Option ResultMode := decodeAbiWith? decodeResultMode?
def decodeAcceptedValue? : Pattern → Option (List ArrowDeclaration) :=
  decodeAbiWith? decodeAccepted?
def decodeEventsValue? : Pattern → Option (List ControlEvent) := decodeAbiWith? decodeEvents?
def decodeIndexValue? : Pattern → Option Nat := decodeAbiWith? decodeIndex?

@[simp] theorem decodeOwnerValue_ownerValue (owner : SpaceOwner) :
    decodeOwnerValue? (ownerValue owner) = some owner := by
  simp [decodeOwnerValue?, ownerValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeNatValue_natValue (value : Nat) :
    decodeNatValue? (natValue value) = some value := by
  simp [decodeNatValue?, natValue, decodeAbiWith?, abiPayload?, abiValue, StructuredC.Builder.node]
@[simp] theorem decodeNameValue_nameValue (name : String) :
    decodeNameValue? (nameValue name) = some name := by
  simp [decodeNameValue?, nameValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeTermValue_termValue (term : Term) :
    decodeTermValue? (termValue term) = some term := by
  simp [decodeTermValue?, termValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeTermsValue_termsValue (terms : List Term) :
    decodeTermsValue? (termsValue terms) = some terms := by
  simp [decodeTermsValue?, termsValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeSnapshotValue_snapshotValue (snapshot : Snapshot) :
    decodeSnapshotValue? (snapshotValue snapshot) = some snapshot := by
  simp [decodeSnapshotValue?, snapshotValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeCallValue_callValue (call : Call) :
    decodeCallValue? (callValue call) = some call := by
  simp [decodeCallValue?, callValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodePlansValue_plansValue (plans : List GuardPlan) :
    decodePlansValue? (plansValue plans) = some plans := by
  simp [decodePlansValue?, plansValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeModesValue_modesValue (modes : List ArgMode) :
    decodeModesValue? (modesValue modes) = some modes := by
  simp [decodeModesValue?, modesValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeResultModeValue_resultModeValue (mode : ResultMode) :
    decodeResultModeValue? (resultModeValue mode) = some mode := by
  simp [decodeResultModeValue?, resultModeValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeAcceptedValue_acceptedValue (accepted : List ArrowDeclaration) :
    decodeAcceptedValue? (acceptedValue accepted) = some accepted := by
  simp [decodeAcceptedValue?, acceptedValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeEventsValue_eventsValue (events : List ControlEvent) :
    decodeEventsValue? (eventsValue events) = some events := by
  simp [decodeEventsValue?, eventsValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]
@[simp] theorem decodeIndexValue_indexValue (index : Nat) :
    decodeIndexValue? (indexValue index) = some index := by
  simp [decodeIndexValue?, indexValue, decodeAbiWith?, abiPayload?, abiValue,
    StructuredC.Builder.node]

/-! ## Phase tags and mode tags -/

def requestPhase : String := "CETTA_PETTA_CALL_GUARD_HOT_PHASE_REQUEST_V1"
def plansPhase : String := "CETTA_PETTA_CALL_GUARD_HOT_PHASE_PLANS_V1"
def argumentsPhase : String := "CETTA_PETTA_CALL_GUARD_HOT_PHASE_ARGUMENTS_V1"
def resultPhase : String := "CETTA_PETTA_CALL_GUARD_HOT_PHASE_RESULT_V1"
def haltedPhase : String := "CETTA_PETTA_CALL_GUARD_HOT_PHASE_HALTED_V1"

def phaseValue : ExecuteControl → Pattern
  | .request .. => valueSymbol requestPhase
  | .plans .. => valueSymbol plansPhase
  | .arguments .. => valueSymbol argumentsPhase
  | .result .. => valueSymbol resultPhase
  | .halted .. => valueSymbol haltedPhase

def rawModeTag : String := "PETTA_MAINLINE_CALL_GUARD_ARG_RAW_ATOM"
def uncheckedModeTag : String := "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_UNCHECKED"
def checkedModeTag : String := "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_SOFTCUT_TYPE"
def uncheckedResultTag : String := "PETTA_MAINLINE_CALL_GUARD_RESULT_UNCHECKED"
def checkedResultTag : String := "PETTA_MAINLINE_CALL_GUARD_RESULT_SOFTCUT_TYPE"

def argumentModeTagValue : ArgMode → Pattern
  | .rawAtom => valueSymbol rawModeTag
  | .evalUnchecked => valueSymbol uncheckedModeTag
  | .evalSoftcutType _ => valueSymbol checkedModeTag

def resultModeTagValue : ResultMode → Pattern
  | .resultUnchecked => valueSymbol uncheckedResultTag
  | .resultSoftcutType _ => valueSymbol checkedResultTag

/-! ## Projections -/

/-- Every slot the generated bodies read from the current state. -/
inductive Projection where
  | owner | snapshot | function | sourceArguments | evaluatedArguments | result
  | familyOwner | familyRevision | familyHead | familyArity | plans
  | call | remaining | accepted | events
  | occurrence | planModes | resultMode
  | declarationOccurrence | declarationFunction | inputs | output
  | index | allModes | allSources | allValues
  | modes | source | sources | value | values | expected
deriving DecidableEq, Repr

def Projection.externalName : Projection → String
  | .owner => "cetta_petta_call_guard_hot_owner_v1"
  | .snapshot => "cetta_petta_call_guard_hot_snapshot_v1"
  | .function => "cetta_petta_call_guard_hot_function_v1"
  | .sourceArguments => "cetta_petta_call_guard_hot_source_arguments_v1"
  | .evaluatedArguments => "cetta_petta_call_guard_hot_evaluated_arguments_v1"
  | .result => "cetta_petta_call_guard_hot_result_v1"
  | .familyOwner => "cetta_petta_call_guard_hot_family_owner_v1"
  | .familyRevision => "cetta_petta_call_guard_hot_family_revision_v1"
  | .familyHead => "cetta_petta_call_guard_hot_family_head_v1"
  | .familyArity => "cetta_petta_call_guard_hot_family_arity_v1"
  | .plans => "cetta_petta_call_guard_hot_plans_v1"
  | .call => "cetta_petta_call_guard_hot_call_v1"
  | .remaining => "cetta_petta_call_guard_hot_remaining_v1"
  | .accepted => "cetta_petta_call_guard_hot_accepted_v1"
  | .events => "cetta_petta_call_guard_hot_events_v1"
  | .occurrence => "cetta_petta_call_guard_hot_occurrence_v1"
  | .planModes => "cetta_petta_call_guard_hot_plan_modes_v1"
  | .resultMode => "cetta_petta_call_guard_hot_result_mode_v1"
  | .declarationOccurrence => "cetta_petta_call_guard_hot_declaration_occurrence_v1"
  | .declarationFunction => "cetta_petta_call_guard_hot_declaration_function_v1"
  | .inputs => "cetta_petta_call_guard_hot_inputs_v1"
  | .output => "cetta_petta_call_guard_hot_output_v1"
  | .index => "cetta_petta_call_guard_hot_index_v1"
  | .allModes => "cetta_petta_call_guard_hot_all_modes_v1"
  | .allSources => "cetta_petta_call_guard_hot_all_sources_v1"
  | .allValues => "cetta_petta_call_guard_hot_all_values_v1"
  | .modes => "cetta_petta_call_guard_hot_modes_v1"
  | .source => "cetta_petta_call_guard_hot_source_v1"
  | .sources => "cetta_petta_call_guard_hot_sources_v1"
  | .value => "cetta_petta_call_guard_hot_value_v1"
  | .values => "cetta_petta_call_guard_hot_values_v1"
  | .expected => "cetta_petta_call_guard_hot_expected_v1"

/-- The call of a non-terminal state. -/
def call? : ExecuteControl → Option Call
  | .request _ call _ => some call
  | .plans _ call _ _ _ => some call
  | .arguments _ call _ _ _ _ _ _ _ _ => some call
  | .result _ call _ _ _ _ => some call
  | .halted _ => none

def snapshot? : ExecuteControl → Option Snapshot
  | .request current _ _ => some current.snapshot
  | .plans snapshot _ _ _ _ => some snapshot
  | .arguments snapshot _ _ _ _ _ _ _ _ _ => some snapshot
  | .result snapshot _ _ _ _ _ => some snapshot
  | .halted _ => none

def family? : ExecuteControl → Option CompiledGuardFamily
  | .request _ _ (.compiled family) => some family
  | _ => none

/-- The plan at hand: the head of the remaining plans, or the plan being
executed. -/
def plan? : ExecuteControl → Option GuardPlan
  | .plans _ _ (plan :: _) _ _ => some plan
  | .arguments _ _ plan _ _ _ _ _ _ _ => some plan
  | .result _ _ plan _ _ _ => some plan
  | _ => none

/-- The plans after the plan at hand. -/
def remaining? : ExecuteControl → Option (List GuardPlan)
  | .plans _ _ (_ :: remaining) _ _ => some remaining
  | .arguments _ _ _ remaining _ _ _ _ _ _ => some remaining
  | .result _ _ _ remaining _ _ => some remaining
  | _ => none

def accepted? : ExecuteControl → Option (List ArrowDeclaration)
  | .plans _ _ _ accepted _ => some accepted
  | .arguments _ _ _ _ _ _ _ _ accepted _ => some accepted
  | .result _ _ _ _ accepted _ => some accepted
  | _ => none

def events? : ExecuteControl → Option (List ControlEvent)
  | .plans _ _ _ _ events => some events
  | .arguments _ _ _ _ _ _ _ _ _ events => some events
  | .result _ _ _ _ _ events => some events
  | _ => none

/-- The expected type at hand: the head argument mode's type, or the result
mode's type. -/
def expected? : ExecuteControl → Option Term
  | .arguments _ _ _ _ _ (.evalSoftcutType expected :: _) _ _ _ _ => some expected
  | .result _ _ ⟨_, _, .resultSoftcutType expected, _⟩ _ _ _ => some expected
  | _ => none

def Projection.value? : Projection → ExecuteControl → Option Pattern
  | .owner => fun control => match control with
      | .request current _ _ => some (ownerValue current.owner)
      | _ => none
  | .snapshot => fun control => (snapshot? control).map snapshotValue
  | .function => fun control => (call? control).map (fun call => nameValue call.function)
  | .sourceArguments => fun control =>
      (call? control).map (fun call => termsValue call.sourceArguments)
  | .evaluatedArguments => fun control =>
      (call? control).map (fun call => termsValue call.evaluatedArguments)
  | .result => fun control => (call? control).map (fun call => termValue call.result)
  | .familyOwner => fun control => (family? control).map (fun family => ownerValue family.owner)
  | .familyRevision => fun control =>
      (family? control).map (fun family => natValue family.revision)
  | .familyHead => fun control => (family? control).map (fun family => nameValue family.head)
  | .familyArity => fun control => (family? control).map (fun family => natValue family.arity)
  | .plans => fun control => (family? control).map (fun family => plansValue family.plans)
  | .call => fun control => (call? control).map callValue
  | .remaining => fun control => (remaining? control).map plansValue
  | .accepted => fun control => (accepted? control).map acceptedValue
  | .events => fun control => (events? control).map eventsValue
  | .occurrence => fun control =>
      (plan? control).map (fun plan => natValue plan.declarationOccurrence)
  | .planModes => fun control => (plan? control).map (fun plan => modesValue plan.argumentModes)
  | .resultMode => fun control =>
      (plan? control).map (fun plan => resultModeValue plan.resultMode)
  | .declarationOccurrence => fun control =>
      (plan? control).map (fun plan => natValue plan.declaration.occurrence)
  | .declarationFunction => fun control =>
      (plan? control).map (fun plan => nameValue plan.declaration.function)
  | .inputs => fun control =>
      (plan? control).map (fun plan => termsValue plan.declaration.inputTypes)
  | .output => fun control =>
      (plan? control).map (fun plan => termValue plan.declaration.outputType)
  | .index => fun control => match control with
      | .arguments _ _ _ _ position _ _ _ _ _ => some (indexValue position)
      | _ => none
  | .allModes => fun control => match control with
      | .arguments _ _ _ _ _ wholeModes _ _ _ _ => some (modesValue wholeModes)
      | _ => none
  | .allSources => fun control => match control with
      | .arguments _ _ _ _ _ _ wholeSources _ _ _ => some (termsValue wholeSources)
      | _ => none
  | .allValues => fun control => match control with
      | .arguments _ _ _ _ _ _ _ wholeValues _ _ => some (termsValue wholeValues)
      | _ => none
  | .modes => fun control => match control with
      | .arguments _ _ _ _ _ (_ :: tail) _ _ _ _ => some (modesValue tail)
      | _ => none
  | .source => fun control => match control with
      | .arguments _ _ _ _ _ _ (head :: _) _ _ _ => some (termValue head)
      | _ => none
  | .sources => fun control => match control with
      | .arguments _ _ _ _ _ _ (_ :: tail) _ _ _ => some (termsValue tail)
      | _ => none
  | .value => fun control => match control with
      | .arguments _ _ _ _ _ _ _ (head :: _) _ _ => some (termValue head)
      | _ => none
  | .values => fun control => match control with
      | .arguments _ _ _ _ _ _ _ (_ :: tail) _ _ => some (termsValue tail)
      | _ => none
  | .expected => fun control => (expected? control).map termValue

/-! ## Frame queries -/

/-- The structural discriminations the generated dispatcher makes. -/
inductive FrameQuery where
  | phase
  | compilationIsOutside
  | plansAreEmpty
  | argumentsAreFinished
  | argumentsAreMismatched
  | argumentModeTag
  | resultModeTag
deriving DecidableEq, Repr

def FrameQuery.externalName : FrameQuery → String
  | .phase => "cetta_petta_call_guard_hot_phase_v1"
  | .compilationIsOutside => "cetta_petta_call_guard_hot_compilation_is_outside_v1"
  | .plansAreEmpty => "cetta_petta_call_guard_hot_plans_are_empty_v1"
  | .argumentsAreFinished => "cetta_petta_call_guard_hot_arguments_are_finished_v1"
  | .argumentsAreMismatched => "cetta_petta_call_guard_hot_arguments_are_mismatched_v1"
  | .argumentModeTag => "cetta_petta_call_guard_hot_argument_mode_tag_v1"
  | .resultModeTag => "cetta_petta_call_guard_hot_result_mode_tag_v1"

def boolValue (answer : Bool) : Pattern := if answer then trueValue else falseValue

def FrameQuery.value? : FrameQuery → ExecuteControl → Option Pattern
  | .phase => fun control => some (phaseValue control)
  | .compilationIsOutside => fun control => match control with
      | .request _ _ .outsideFragment => some trueValue
      | .request _ _ (.compiled _) => some falseValue
      | _ => none
  | .plansAreEmpty => fun control => match control with
      | .plans _ _ remaining _ _ => some (boolValue remaining.isEmpty)
      | _ => none
  | .argumentsAreFinished => fun control => match control with
      | .arguments _ _ _ _ _ modes sources values _ _ =>
          some (boolValue (modes.isEmpty && sources.isEmpty && values.isEmpty))
      | _ => none
  | .argumentsAreMismatched => fun control => match control with
      | .arguments _ _ _ _ _ modes sources values _ _ =>
          some (boolValue (shapeMismatch modes sources values))
      | _ => none
  | .argumentModeTag => fun control => match control with
      | .arguments _ _ _ _ _ (mode :: _) _ _ _ _ => some (argumentModeTagValue mode)
      | _ => none
  | .resultModeTag => fun control => match control with
      | .result _ _ plan _ _ _ => some (resultModeTagValue plan.resultMode)
      | _ => none

/-! ## Decisions: the thirteen relation premises on supplied operands -/

inductive Decision where
  | ownerDiffers
  | revisionStale
  | headWrong
  | arityWrong
  | familyCurrent
  | planHeadMatches
  | planHeadDiffers
  | rawEqual
  | rawDiffers
  | exactType
  | metatypeAccepts
  | metatypeRejects
  | shapeMismatched
deriving DecidableEq, Repr

def Decision.externalName : Decision → String
  | .ownerDiffers => "cetta_petta_call_guard_hot_owner_differs_v1"
  | .revisionStale => "cetta_petta_call_guard_hot_revision_stale_v1"
  | .headWrong => "cetta_petta_call_guard_hot_head_wrong_v1"
  | .arityWrong => "cetta_petta_call_guard_hot_arity_wrong_v1"
  | .familyCurrent => "cetta_petta_call_guard_hot_family_current_v1"
  | .planHeadMatches => "cetta_petta_call_guard_hot_plan_head_matches_v1"
  | .planHeadDiffers => "cetta_petta_call_guard_hot_plan_head_differs_v1"
  | .rawEqual => "cetta_petta_call_guard_hot_raw_equal_v1"
  | .rawDiffers => "cetta_petta_call_guard_hot_raw_differs_v1"
  | .exactType => "cetta_petta_call_guard_hot_exact_type_v1"
  | .metatypeAccepts => "cetta_petta_call_guard_hot_metatype_accepts_v1"
  | .metatypeRejects => "cetta_petta_call_guard_hot_metatype_rejects_v1"
  | .shapeMismatched => "cetta_petta_call_guard_hot_shape_mismatch_v1"

/-- The source relation each decision answers. -/
def Decision.relation : Decision → String
  | .ownerDiffers => foreignOwnerRelation
  | .revisionStale => staleRevisionRelation
  | .headWrong => wrongHeadRelation
  | .arityWrong => wrongArityRelation
  | .familyCurrent => currentFamilyRelation
  | .planHeadMatches => planHeadMatchesRelation
  | .planHeadDiffers => planHeadDiffersRelation
  | .rawEqual => rawEqualRelation
  | .rawDiffers => rawDiffersRelation
  | .exactType => exactTypeRelation
  | .metatypeAccepts => metatypeAcceptsRelation
  | .metatypeRejects => metatypeRejectsRelation
  | .shapeMismatched => argumentShapeMismatchRelation

/-- Decide on decoded operand values; `none` when an operand does not decode. -/
def Decision.decide? : Decision → List Pattern → Option Bool
  | .ownerDiffers, [familyOwner, currentOwner] => do
      let left ← decodeOwnerValue? familyOwner
      let right ← decodeOwnerValue? currentOwner
      pure (decide (left ≠ right))
  | .revisionStale, [familyOwner, currentOwner, familyRevision, snapshot] => do
      let left ← decodeOwnerValue? familyOwner
      let right ← decodeOwnerValue? currentOwner
      let revision ← decodeNatValue? familyRevision
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      pure (decide (left = right ∧ revision ≠ decodedSnapshot.revision))
  | .headWrong, [familyOwner, currentOwner, familyRevision, snapshot, familyHead,
      callFunction] => do
      let left ← decodeOwnerValue? familyOwner
      let right ← decodeOwnerValue? currentOwner
      let revision ← decodeNatValue? familyRevision
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let head ← decodeNameValue? familyHead
      let function ← decodeNameValue? callFunction
      pure (decide (left = right ∧ revision = decodedSnapshot.revision ∧ head ≠ function))
  | .arityWrong, [familyOwner, currentOwner, familyRevision, snapshot, familyHead,
      callFunction, familyArity, sources] => do
      let left ← decodeOwnerValue? familyOwner
      let right ← decodeOwnerValue? currentOwner
      let revision ← decodeNatValue? familyRevision
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let head ← decodeNameValue? familyHead
      let function ← decodeNameValue? callFunction
      let arity ← decodeNatValue? familyArity
      let decodedSources ← decodeTermsValue? sources
      pure (decide (requestClass left right revision decodedSnapshot.revision head function arity
        decodedSources = some .wrongArity))
  | .familyCurrent, [familyOwner, currentOwner, familyRevision, snapshot, familyHead,
      callFunction, familyArity, sources] => do
      let left ← decodeOwnerValue? familyOwner
      let right ← decodeOwnerValue? currentOwner
      let revision ← decodeNatValue? familyRevision
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let head ← decodeNameValue? familyHead
      let function ← decodeNameValue? callFunction
      let arity ← decodeNatValue? familyArity
      let decodedSources ← decodeTermsValue? sources
      pure (decide (requestClass left right revision decodedSnapshot.revision head function arity
        decodedSources = none))
  | .planHeadMatches, [declarationFunction, callFunction] => do
      let left ← decodeNameValue? declarationFunction
      let right ← decodeNameValue? callFunction
      pure (decide (left = right))
  | .planHeadDiffers, [declarationFunction, callFunction] => do
      let left ← decodeNameValue? declarationFunction
      let right ← decodeNameValue? callFunction
      pure (decide (left ≠ right))
  | .rawEqual, [source, value] => do
      let decodedSource ← decodeTermValue? source
      let decodedValue ← decodeTermValue? value
      pure (decide (decodedValue = decodedSource))
  | .rawDiffers, [source, value] => do
      let decodedSource ← decodeTermValue? source
      let decodedValue ← decodeTermValue? value
      pure (decide (decodedValue ≠ decodedSource))
  | .exactType, [snapshot, value, expected] => do
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let decodedValue ← decodeTermValue? value
      let decodedExpected ← decodeTermValue? expected
      pure (decide (GetType decodedSnapshot decodedValue decodedExpected))
  | .metatypeAccepts, [snapshot, value, expected] => do
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let decodedValue ← decodeTermValue? value
      let decodedExpected ← decodeTermValue? expected
      pure (decide (¬ GetType decodedSnapshot decodedValue decodedExpected ∧
        GetMetatype decodedSnapshot decodedValue decodedExpected))
  | .metatypeRejects, [snapshot, value, expected] => do
      let decodedSnapshot ← decodeSnapshotValue? snapshot
      let decodedValue ← decodeTermValue? value
      let decodedExpected ← decodeTermValue? expected
      pure (decide (¬ GetType decodedSnapshot decodedValue decodedExpected ∧
        ¬ GetMetatype decodedSnapshot decodedValue decodedExpected))
  | .shapeMismatched, [modes, sources, values] => do
      let decodedModes ← decodeModesValue? modes
      let decodedSources ← decodeTermsValue? sources
      let decodedValues ← decodeTermsValue? values
      pure (shapeMismatch decodedModes decodedSources decodedValues)
  | _, _ => none

/-! ## The handler, first half: projections, frame queries, decisions -/

def projections : List Projection := [
  .owner, .snapshot, .function, .sourceArguments, .evaluatedArguments, .result,
  .familyOwner, .familyRevision, .familyHead, .familyArity, .plans,
  .call, .remaining, .accepted, .events,
  .occurrence, .planModes, .resultMode,
  .declarationOccurrence, .declarationFunction, .inputs, .output,
  .index, .allModes, .allSources, .allValues, .modes, .source, .sources, .value, .values,
  .expected]

def frameQueries : List FrameQuery := [
  .phase, .compilationIsOutside, .plansAreEmpty, .argumentsAreFinished,
  .argumentsAreMismatched, .argumentModeTag, .resultModeTag]

def decisions : List Decision := [
  .ownerDiffers, .revisionStale, .headWrong, .arityWrong, .familyCurrent,
  .planHeadMatches, .planHeadDiffers, .rawEqual, .rawDiffers,
  .exactType, .metatypeAccepts, .metatypeRejects, .shapeMismatched]

def projection? (name : String) : Option Projection :=
  projections.find? fun projection => projection.externalName = name

def frameQuery? (name : String) : Option FrameQuery :=
  frameQueries.find? fun query => query.externalName = name

def decision? (name : String) : Option Decision :=
  decisions.find? fun decision => decision.externalName = name

theorem projection?_externalName (projection : Projection) :
    projection? projection.externalName = some projection := by
  cases projection <;> rfl

theorem frameQuery?_externalName (query : FrameQuery) :
    frameQuery? query.externalName = some query := by
  cases query <;> rfl

theorem decision?_externalName (decision : Decision) :
    decision? decision.externalName = some decision := by
  cases decision <;> rfl

def reply (name : String) (value environment receipt : Pattern) : Option EvaluationStep :=
  some ⟨.value value, environment, externalReceipt name receipt⟩

/-- Read one slot of the state supplied as the only operand. -/
def projectState? (name : String) (read : ExecuteControl → Option Pattern)
    (arguments : List Pattern) (environment receipt : Pattern) : Option EvaluationStep := do
  let supplied ← arguments[0]?
  let control ← currentStateArgument? environment supplied
  let value ← read control
  reply name value environment receipt

/-- Projections, frame queries, and decisions. -/
def readHandler : ExternalHandler :=
  fun name arguments environment receipt =>
    match projection? name with
    | some projection => projectState? name projection.value? arguments environment receipt
    | none =>
      match frameQuery? name with
      | some query => projectState? name query.value? arguments environment receipt
      | none =>
        match decision? name with
        | some decision => do
            let answer ← decision.decide? arguments
            reply name (boolValue answer) environment receipt
        | none => none

theorem readHandler_projection_exact (projection : Projection) (control : ExecuteControl)
    (value environment receipt : Pattern)
    (projected : projection.value? control = some value)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    readHandler projection.externalName [stateValue control] environment receipt =
      some ⟨.value value, environment, externalReceipt projection.externalName receipt⟩ := by
  simp [readHandler, projection?_externalName, projectState?, currentStateArgument?_exact control
    environment stored, projected, reply]

theorem readHandler_frameQuery_exact (query : FrameQuery) (control : ExecuteControl)
    (value environment receipt : Pattern)
    (queried : query.value? control = some value)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    readHandler query.externalName [stateValue control] environment receipt =
      some ⟨.value value, environment, externalReceipt query.externalName receipt⟩ := by
  have notProjection : projection? query.externalName = none := by
    cases query <;> rfl
  simp [readHandler, notProjection, frameQuery?_externalName, projectState?,
    currentStateArgument?_exact control environment stored, queried, reply]

theorem readHandler_decision_exact (decision : Decision) (arguments : List Pattern)
    (answer : Bool) (environment receipt : Pattern)
    (decided : decision.decide? arguments = some answer) :
    readHandler decision.externalName arguments environment receipt =
      some ⟨.value (boolValue answer), environment,
        externalReceipt decision.externalName receipt⟩ := by
  have notProjection : projection? decision.externalName = none := by
    cases decision <;> rfl
  have notQuery : frameQuery? decision.externalName = none := by
    cases decision <;> rfl
  simp [readHandler, notProjection, notQuery, decision?_externalName, decided, reply]

/-! ## Deltas: the right-hand sides of the hot rules -/

def fallbackSymbol : GuardFallbackReason → String
  | .outsideFragment => "CETTA_PETTA_CALL_GUARD_HOT_FALLBACK_OUTSIDE_FRAGMENT_V1"
  | .foreignOwner => "CETTA_PETTA_CALL_GUARD_HOT_FALLBACK_FOREIGN_OWNER_V1"
  | .staleRevision => "CETTA_PETTA_CALL_GUARD_HOT_FALLBACK_STALE_REVISION_V1"
  | .wrongHead => "CETTA_PETTA_CALL_GUARD_HOT_FALLBACK_WRONG_HEAD_V1"
  | .wrongArity => "CETTA_PETTA_CALL_GUARD_HOT_FALLBACK_WRONG_ARITY_V1"

def reasonValue (reason : GuardFallbackReason) : Pattern := valueSymbol (fallbackSymbol reason)

def decodeReasonValue? (value : Pattern) : Option GuardFallbackReason :=
  if value = reasonValue .outsideFragment then some .outsideFragment
  else if value = reasonValue .foreignOwner then some .foreignOwner
  else if value = reasonValue .staleRevision then some .staleRevision
  else if value = reasonValue .wrongHead then some .wrongHead
  else if value = reasonValue .wrongArity then some .wrongArity
  else none

@[simp] theorem decodeReasonValue_reasonValue (reason : GuardFallbackReason) :
    decodeReasonValue? (reasonValue reason) = some reason := by
  cases reason <;> decide

/-- One write primitive per right-hand-side shape of the hot rules. -/
inductive Delta where
  | recordFallback
  | beginPlans
  | finishExecuted
  | rejectPlanHead
  | beginArguments
  | evaluateCall
  | advanceRaw
  | advanceUnchecked
  | advanceExact
  | advanceMetatype
  | rejectRaw
  | rejectMetatype
  | rejectShape
  | installUnchecked
  | installExact
  | installMetatype
  | rejectResult
deriving DecidableEq, Repr

def Delta.externalName : Delta → String
  | .recordFallback => "cetta_petta_call_guard_hot_record_fallback_v1"
  | .beginPlans => "cetta_petta_call_guard_hot_begin_plans_v1"
  | .finishExecuted => "cetta_petta_call_guard_hot_finish_executed_v1"
  | .rejectPlanHead => "cetta_petta_call_guard_hot_reject_plan_head_v1"
  | .beginArguments => "cetta_petta_call_guard_hot_begin_arguments_v1"
  | .evaluateCall => "cetta_petta_call_guard_hot_evaluate_call_v1"
  | .advanceRaw => "cetta_petta_call_guard_hot_advance_raw_v1"
  | .advanceUnchecked => "cetta_petta_call_guard_hot_advance_unchecked_v1"
  | .advanceExact => "cetta_petta_call_guard_hot_advance_exact_v1"
  | .advanceMetatype => "cetta_petta_call_guard_hot_advance_metatype_v1"
  | .rejectRaw => "cetta_petta_call_guard_hot_reject_raw_v1"
  | .rejectMetatype => "cetta_petta_call_guard_hot_reject_metatype_v1"
  | .rejectShape => "cetta_petta_call_guard_hot_reject_shape_v1"
  | .installUnchecked => "cetta_petta_call_guard_hot_install_unchecked_v1"
  | .installExact => "cetta_petta_call_guard_hot_install_exact_v1"
  | .installMetatype => "cetta_petta_call_guard_hot_install_metatype_v1"
  | .rejectResult => "cetta_petta_call_guard_hot_reject_result_v1"

def deltas : List Delta := [
  .recordFallback, .beginPlans, .finishExecuted, .rejectPlanHead, .beginArguments,
  .evaluateCall, .advanceRaw, .advanceUnchecked, .advanceExact, .advanceMetatype,
  .rejectRaw, .rejectMetatype, .rejectShape, .installUnchecked, .installExact,
  .installMetatype, .rejectResult]

def delta? (name : String) : Option Delta :=
  deltas.find? fun delta => delta.externalName = name

theorem delta?_externalName (delta : Delta) : delta? delta.externalName = some delta := by
  cases delta <;> rfl

/-- The current state, after the state operand, as the source of a delta;
each delta checks the supplied operands against the fields it reads. -/
def Delta.apply? : Delta → ExecuteControl → List Pattern → Option ExecuteControl
  | .recordFallback, _, [reason] => do
      let decoded ← decodeReasonValue? reason
      pure (.halted ⟨.fallback decoded, [.fallback decoded]⟩)
  | .beginPlans, .request current call (.compiled family),
      [snapshot, function, sources, values, result, plans] => do
      let snapshot' ← decodeSnapshotValue? snapshot
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let plans' ← decodePlansValue? plans
      if snapshot' = current.snapshot ∧ (⟨function', sources', values', result'⟩ : Call) = call ∧
          plans' = family.plans then
        pure (.plans snapshot' ⟨function', sources', values', result'⟩ plans' [] [])
      else none
  | .finishExecuted, .plans _ _ [] accepted events, [acceptedValue', eventsValue'] => do
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      if accepted' = accepted ∧ events' = events then
        pure (.halted ⟨.executed accepted', events'⟩)
      else none
  | .rejectPlanHead, .plans snapshot call (plan :: remaining) accepted events,
      [snapshotValue', function, sources, values, result, remainingValue', acceptedValue',
        eventsValue', occurrence] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let occurrence' ← decodeNatValue? occurrence
      if snapshot' = snapshot ∧ (⟨function', sources', values', result'⟩ : Call) = call ∧
          remaining' = remaining ∧ accepted' = accepted ∧ events' = events ∧
          occurrence' = plan.declarationOccurrence then
        pure (.plans snapshot' ⟨function', sources', values', result'⟩ remaining' accepted'
          (events' ++ [.beginPlan occurrence', .rejectOccurrence occurrence']))
      else none
  | .beginArguments, .plans snapshot call (plan :: remaining) accepted events,
      [snapshotValue', function, sources, values, result, occurrence, planModes, resultMode,
        declarationOccurrence, declarationFunction, inputs, output, remainingValue',
        acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      let call' : Call := ⟨function', sources', values', result'⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          accepted' = accepted ∧ events' = events then
        pure (.arguments snapshot' call' plan' remaining' 0 planModes' sources' values' accepted'
          (events' ++ [.beginPlan occurrence']))
      else none
  | .evaluateCall, .arguments snapshot call plan remaining _ [] [] [] accepted events,
      [snapshotValue', callValue', occurrence, planModes, resultMode, declarationOccurrence,
        declarationFunction, inputs, output, remainingValue', acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          accepted' = accepted ∧ events' = events then
        pure (.result snapshot' call' plan' remaining' accepted'
          (events' ++ [.evaluateCall occurrence']))
      else none
  | .advanceRaw, .arguments snapshot call plan remaining index (.rawAtom :: modes)
      (source :: sources) (value :: values) accepted events,
      [snapshotValue', callValue', occurrence, planModes, resultMode, declarationOccurrence,
        declarationFunction, inputs, output, remainingValue', indexValue', modesValue',
        sourcesValue', valuesValue', acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let index' ← decodeIndexValue? indexValue'
      let modes' ← decodeModesValue? modesValue'
      let sources' ← decodeTermsValue? sourcesValue'
      let values' ← decodeTermsValue? valuesValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          index' = index ∧ modes' = modes ∧ sources' = sources ∧ values' = values ∧
          accepted' = accepted ∧ events' = events then
        let _ := source
        let _ := value
        pure (.arguments snapshot' call' plan' remaining' (index' + 1) modes' sources' values'
          accepted' (events' ++ [.useRawArgument index']))
      else none
  | .advanceUnchecked, .arguments snapshot call plan remaining index (.evalUnchecked :: modes)
      (_ :: sources) (_ :: values) accepted events,
      [snapshotValue', callValue', occurrence, planModes, resultMode, declarationOccurrence,
        declarationFunction, inputs, output, remainingValue', indexValue', modesValue',
        sourcesValue', valuesValue', acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let index' ← decodeIndexValue? indexValue'
      let modes' ← decodeModesValue? modesValue'
      let sources' ← decodeTermsValue? sourcesValue'
      let values' ← decodeTermsValue? valuesValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          index' = index ∧ modes' = modes ∧ sources' = sources ∧ values' = values ∧
          accepted' = accepted ∧ events' = events then
        pure (.arguments snapshot' call' plan' remaining' (index' + 1) modes' sources' values'
          accepted' (events' ++ [.evaluateArgument index']))
      else none
  | .advanceExact, .arguments snapshot call plan remaining index
      (.evalSoftcutType expected :: modes) (_ :: sources) (_ :: values) accepted events,
      [snapshotValue', callValue', occurrence, planModes, resultMode, declarationOccurrence,
        declarationFunction, inputs, output, remainingValue', indexValue', expectedValue',
        modesValue', sourcesValue', valuesValue', acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let index' ← decodeIndexValue? indexValue'
      let expected' ← decodeTermValue? expectedValue'
      let modes' ← decodeModesValue? modesValue'
      let sources' ← decodeTermsValue? sourcesValue'
      let values' ← decodeTermsValue? valuesValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          index' = index ∧ expected' = expected ∧ modes' = modes ∧ sources' = sources ∧
          values' = values ∧ accepted' = accepted ∧ events' = events then
        pure (.arguments snapshot' call' plan' remaining' (index' + 1) modes' sources' values'
          accepted' (events' ++ [.evaluateArgument index', .queryExactType index' expected' true]))
      else none
  | .advanceMetatype, .arguments snapshot call plan remaining index
      (.evalSoftcutType expected :: modes) (_ :: sources) (_ :: values) accepted events,
      [snapshotValue', callValue', occurrence, planModes, resultMode, declarationOccurrence,
        declarationFunction, inputs, output, remainingValue', indexValue', expectedValue',
        modesValue', sourcesValue', valuesValue', acceptedValue', eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let occurrence' ← decodeNatValue? occurrence
      let planModes' ← decodeModesValue? planModes
      let resultMode' ← decodeResultModeValue? resultMode
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let remaining' ← decodePlansValue? remainingValue'
      let index' ← decodeIndexValue? indexValue'
      let expected' ← decodeTermValue? expectedValue'
      let modes' ← decodeModesValue? modesValue'
      let sources' ← decodeTermsValue? sourcesValue'
      let values' ← decodeTermsValue? valuesValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let plan' : GuardPlan := ⟨occurrence', planModes', resultMode',
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩⟩
      if snapshot' = snapshot ∧ call' = call ∧ plan' = plan ∧ remaining' = remaining ∧
          index' = index ∧ expected' = expected ∧ modes' = modes ∧ sources' = sources ∧
          values' = values ∧ accepted' = accepted ∧ events' = events then
        pure (.arguments snapshot' call' plan' remaining' (index' + 1) modes' sources' values'
          accepted' (events' ++ [.evaluateArgument index', .queryExactType index' expected' false,
            .queryMetatype index' expected' true]))
      else none
  | .rejectRaw, .arguments snapshot call plan remaining index (.rawAtom :: _) (_ :: _) (_ :: _)
      accepted events,
      [snapshotValue', callValue', remainingValue', acceptedValue', eventsValue', occurrence,
        indexValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let occurrence' ← decodeNatValue? occurrence
      let index' ← decodeIndexValue? indexValue'
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          events' = events ∧ occurrence' = plan.declarationOccurrence ∧ index' = index then
        pure (.plans snapshot' call' remaining' accepted'
          (events' ++ [.useRawArgument index', .rejectOccurrence occurrence']))
      else none
  | .rejectMetatype, .arguments snapshot call plan remaining index
      (.evalSoftcutType expected :: _) (_ :: _) (_ :: _) accepted events,
      [snapshotValue', callValue', remainingValue', acceptedValue', eventsValue', occurrence,
        indexValue', expectedValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let occurrence' ← decodeNatValue? occurrence
      let index' ← decodeIndexValue? indexValue'
      let expected' ← decodeTermValue? expectedValue'
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          events' = events ∧ occurrence' = plan.declarationOccurrence ∧ index' = index ∧
          expected' = expected then
        pure (.plans snapshot' call' remaining' accepted'
          (events' ++ [.evaluateArgument index', .queryExactType index' expected' false,
            .queryMetatype index' expected' false, .rejectOccurrence occurrence']))
      else none
  | .rejectShape, .arguments snapshot call plan remaining index modes sources values accepted
      events,
      [snapshotValue', callValue', remainingValue', acceptedValue', eventsValue', occurrence,
        indexValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let call' ← decodeCallValue? callValue'
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let occurrence' ← decodeNatValue? occurrence
      let index' ← decodeIndexValue? indexValue'
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          events' = events ∧ occurrence' = plan.declarationOccurrence ∧ index' = index ∧
          shapeMismatch modes sources values = true then
        pure (.plans snapshot' call' remaining' accepted'
          (events' ++ [.argumentShapeMismatch index', .rejectOccurrence occurrence']))
      else none
  | .installUnchecked, .result snapshot call ⟨occurrence, planModes, .resultUnchecked, declaration⟩
      remaining accepted events,
      [snapshotValue', function, sources, values, result, remainingValue', acceptedValue',
        declarationOccurrence, declarationFunction, inputs, output, occurrenceValue',
        eventsValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let occurrence' ← decodeNatValue? occurrenceValue'
      let events' ← decodeEventsValue? eventsValue'
      let declaration' : ArrowDeclaration :=
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩
      let call' : Call := ⟨function', sources', values', result'⟩
      let _ := planModes
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          declaration' = declaration ∧ occurrence' = occurrence ∧ events' = events then
        pure (.plans snapshot' call' remaining' (accepted' ++ [declaration'])
          (events' ++ [.installOccurrence occurrence']))
      else none
  | .installExact, .result snapshot call
      ⟨occurrence, planModes, .resultSoftcutType expected, declaration⟩ remaining accepted events,
      [snapshotValue', function, sources, values, result, remainingValue', acceptedValue',
        declarationOccurrence, declarationFunction, inputs, output, occurrenceValue',
        eventsValue', expectedValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let occurrence' ← decodeNatValue? occurrenceValue'
      let events' ← decodeEventsValue? eventsValue'
      let expected' ← decodeTermValue? expectedValue'
      let declaration' : ArrowDeclaration :=
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩
      let call' : Call := ⟨function', sources', values', result'⟩
      let _ := planModes
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          declaration' = declaration ∧ occurrence' = occurrence ∧ events' = events ∧
          expected' = expected then
        pure (.plans snapshot' call' remaining' (accepted' ++ [declaration'])
          (events' ++ [.queryResultType expected' true, .installOccurrence occurrence']))
      else none
  | .installMetatype, .result snapshot call
      ⟨occurrence, planModes, .resultSoftcutType expected, declaration⟩ remaining accepted events,
      [snapshotValue', function, sources, values, result, remainingValue', acceptedValue',
        declarationOccurrence, declarationFunction, inputs, output, occurrenceValue',
        eventsValue', expectedValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let declarationOccurrence' ← decodeNatValue? declarationOccurrence
      let declarationFunction' ← decodeNameValue? declarationFunction
      let inputs' ← decodeTermsValue? inputs
      let output' ← decodeTermValue? output
      let occurrence' ← decodeNatValue? occurrenceValue'
      let events' ← decodeEventsValue? eventsValue'
      let expected' ← decodeTermValue? expectedValue'
      let declaration' : ArrowDeclaration :=
        ⟨declarationOccurrence', declarationFunction', inputs', output'⟩
      let call' : Call := ⟨function', sources', values', result'⟩
      let _ := planModes
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          declaration' = declaration ∧ occurrence' = occurrence ∧ events' = events ∧
          expected' = expected then
        pure (.plans snapshot' call' remaining' (accepted' ++ [declaration'])
          (events' ++ [.queryResultType expected' false, .queryResultMetatype expected' true,
            .installOccurrence occurrence']))
      else none
  | .rejectResult, .result snapshot call
      ⟨occurrence, planModes, .resultSoftcutType expected, declaration⟩ remaining accepted events,
      [snapshotValue', function, sources, values, result, remainingValue', acceptedValue',
        eventsValue', occurrenceValue', expectedValue'] => do
      let snapshot' ← decodeSnapshotValue? snapshotValue'
      let function' ← decodeNameValue? function
      let sources' ← decodeTermsValue? sources
      let values' ← decodeTermsValue? values
      let result' ← decodeTermValue? result
      let remaining' ← decodePlansValue? remainingValue'
      let accepted' ← decodeAcceptedValue? acceptedValue'
      let events' ← decodeEventsValue? eventsValue'
      let occurrence' ← decodeNatValue? occurrenceValue'
      let expected' ← decodeTermValue? expectedValue'
      let call' : Call := ⟨function', sources', values', result'⟩
      let _ := planModes
      let _ := declaration
      if snapshot' = snapshot ∧ call' = call ∧ remaining' = remaining ∧ accepted' = accepted ∧
          events' = events ∧ occurrence' = occurrence ∧ expected' = expected then
        pure (.plans snapshot' call' remaining' accepted'
          (events' ++ [.queryResultType expected' false, .queryResultMetatype expected' false,
            .rejectOccurrence occurrence']))
      else none
  | _, _, _ => none

/-- Write the next state into the canonical `state` slot. -/
def writeState (name : String) (control : ExecuteControl) (environment receipt : Pattern) :
    Option EvaluationStep :=
  some ⟨.value valueUnit, bindName "state" (stateValue control) environment,
    externalReceipt name receipt⟩

def deltaHandler : ExternalHandler :=
  fun name arguments environment receipt =>
    match delta? name with
    | some delta =>
        match arguments with
        | state :: operands => do
            let current ← currentStateArgument? environment state
            let next ← delta.apply? current operands
            writeState name next environment receipt
        | [] => none
    | none => none

/-- The complete hot handler. -/
def handler : ExternalHandler :=
  fun name arguments environment receipt =>
    match readHandler name arguments environment receipt with
    | some step => some step
    | none => deltaHandler name arguments environment receipt

theorem handler_of_readHandler {name : String} {arguments : List Pattern}
    {environment receipt : Pattern} {step : EvaluationStep}
    (read : readHandler name arguments environment receipt = some step) :
    handler name arguments environment receipt = some step := by
  simp [handler, read]

theorem readHandler_delta_none (delta : Delta) (arguments : List Pattern)
    (environment receipt : Pattern) :
    readHandler delta.externalName arguments environment receipt = none := by
  have notProjection : projection? delta.externalName = none := by cases delta <;> rfl
  have notQuery : frameQuery? delta.externalName = none := by cases delta <;> rfl
  have notDecision : decision? delta.externalName = none := by cases delta <;> rfl
  simp [readHandler, notProjection, notQuery, notDecision]

/-- A delta with agreeing operands writes exactly the next state. -/
theorem handler_delta_exact (delta : Delta) (control next : ExecuteControl)
    (operands : List Pattern) (environment receipt : Pattern)
    (applied : delta.apply? control operands = some next)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    handler delta.externalName (stateValue control :: operands) environment receipt =
      some ⟨.value valueUnit, bindName "state" (stateValue next) environment,
        externalReceipt delta.externalName receipt⟩ := by
  simp [handler, readHandler_delta_none, deltaHandler, delta?_externalName,
    currentStateArgument?_exact control environment stored, applied, writeState]

def relations : RelationEnv := relationEnv handler

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
