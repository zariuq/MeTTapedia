import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.IRPass

/-!
# The completed-call executor as an authored LanguageDef

The hot call-guard executor `executeStep?` is a deterministic transition
function on `ExecuteControl`.  This module presents it as an ordinary
`LanguageDef`: encoded executor states are terms, every instruction row of
the inspectable program becomes rewrite rules, and the decisions the executor
delegates to the snapshot (type and metatype queries, raw-argument equality,
name and arity comparison) are relation premises answered by the reference
functions themselves.

Identity is by slot.  Every rule left-hand side is linear: no metavariable
occurs twice, so no rule compares two values by name; every comparison the
executor makes is a relation premise on the slots it reads.

Rows with two outcomes (an argument or result check that accepts or rejects)
become two rules whose premises are complementary.  The nineteen rules and
the terminal row are listed against the seventeen program instructions in
`instructionOf`.

The exactness theorem `language_step_iff_executeStep` (next section) is the
whole content: on encoded states the authored language takes exactly the
executor's step, and through `programGSLT_step_iff_executeGSLT_step` exactly
the program's step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram

/-! ## Structural data encoding -/

def indexZero : Pattern := a "petta-call-guard-hot:index-zero"
def indexSucc (index : Pattern) : Pattern := a "petta-call-guard-hot:index-succ" [index]

/-- Argument positions are counted in unary so that advancing is one
constructor. -/
def encodeIndex : Nat → Pattern
  | 0 => indexZero
  | index + 1 => indexSucc (encodeIndex index)

def decodeIndex? : Pattern → Option Nat
  | .apply "petta-call-guard-hot:index-zero" [] => some 0
  | .apply "petta-call-guard-hot:index-succ" [index] => (decodeIndex? index).map (· + 1)
  | _ => none

@[simp] theorem decodeIndex_encodeIndex (index : Nat) :
    decodeIndex? (encodeIndex index) = some index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      simp [encodeIndex, indexSucc, a, decodeIndex?, inductionHypothesis]

def truePattern : Pattern := a "petta-call-guard-hot:true"
def falsePattern : Pattern := a "petta-call-guard-hot:false"

def encodeBool : Bool → Pattern
  | true => truePattern
  | false => falsePattern

def decodeBool? : Pattern → Option Bool
  | .apply "petta-call-guard-hot:true" [] => some true
  | .apply "petta-call-guard-hot:false" [] => some false
  | _ => none

@[simp] theorem decodeBool_encodeBool (value : Bool) :
    decodeBool? (encodeBool value) = some value := by
  cases value <;> rfl

def namesNil : Pattern := a "petta-call-guard-hot:names-nil"
def namesCons (head tail : Pattern) : Pattern :=
  a "petta-call-guard-hot:names-cons" [head, tail]

def encodeNames : List String → Pattern
  | [] => namesNil
  | head :: tail => namesCons (encodeName head) (encodeNames tail)

def decodeNames? : Pattern → Option (List String)
  | .apply "petta-call-guard-hot:names-nil" [] => some []
  | .apply "petta-call-guard-hot:names-cons" [head, tail] => do
      let decodedHead ← decodeName? head
      let decodedTail ← decodeNames? tail
      pure (decodedHead :: decodedTail)
  | _ => none

@[simp] theorem decodeNames_encodeNames (names : List String) :
    decodeNames? (encodeNames names) = some names := by
  induction names with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeNames, namesCons, a, decodeNames?, inductionHypothesis]

def annotationPattern (occurrence subject type : Pattern) : Pattern :=
  a "petta-call-guard-hot:annotation" [occurrence, subject, type]

def encodeAnnotation (annotation : TypeAnnotation) : Pattern :=
  annotationPattern (encodeNat annotation.occurrence) (encodeTerm annotation.subject)
    (encodeTerm annotation.type)

def decodeAnnotation? : Pattern → Option TypeAnnotation
  | .apply "petta-call-guard-hot:annotation" [occurrence, subject, type] => do
      let decodedOccurrence ← decodeNat? occurrence
      let decodedSubject ← decodeTerm? subject
      let decodedType ← decodeTerm? type
      pure ⟨decodedOccurrence, decodedSubject, decodedType⟩
  | _ => none

@[simp] theorem decodeAnnotation_encodeAnnotation (annotation : TypeAnnotation) :
    decodeAnnotation? (encodeAnnotation annotation) = some annotation := by
  cases annotation
  simp [encodeAnnotation, annotationPattern, a, decodeAnnotation?]

def annotationsNil : Pattern := a "petta-call-guard-hot:annotations-nil"
def annotationsCons (head tail : Pattern) : Pattern :=
  a "petta-call-guard-hot:annotations-cons" [head, tail]

def encodeAnnotations : List TypeAnnotation → Pattern
  | [] => annotationsNil
  | head :: tail => annotationsCons (encodeAnnotation head) (encodeAnnotations tail)

def decodeAnnotations? : Pattern → Option (List TypeAnnotation)
  | .apply "petta-call-guard-hot:annotations-nil" [] => some []
  | .apply "petta-call-guard-hot:annotations-cons" [head, tail] => do
      let decodedHead ← decodeAnnotation? head
      let decodedTail ← decodeAnnotations? tail
      pure (decodedHead :: decodedTail)
  | _ => none

@[simp] theorem decodeAnnotations_encodeAnnotations (annotations : List TypeAnnotation) :
    decodeAnnotations? (encodeAnnotations annotations) = some annotations := by
  induction annotations with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeAnnotations, annotationsCons, a, decodeAnnotations?, inductionHypothesis]

def snapshotPattern (revision declarations annotations registered : Pattern) : Pattern :=
  a "petta-call-guard-hot:snapshot" [revision, declarations, annotations, registered]

def encodeSnapshot (snapshot : Snapshot) : Pattern :=
  snapshotPattern (encodeNat snapshot.revision) (encodeDeclarations snapshot.declarations)
    (encodeAnnotations snapshot.annotations) (encodeNames snapshot.registeredFunctions)

def decodeSnapshot? : Pattern → Option Snapshot
  | .apply "petta-call-guard-hot:snapshot" [revision, declarations, annotations, registered] => do
      let decodedRevision ← decodeNat? revision
      let decodedDeclarations ← decodeDeclarations? declarations
      let decodedAnnotations ← decodeAnnotations? annotations
      let decodedRegistered ← decodeNames? registered
      pure ⟨decodedRevision, decodedDeclarations, decodedAnnotations, decodedRegistered⟩
  | _ => none

@[simp] theorem decodeSnapshot_encodeSnapshot (snapshot : Snapshot) :
    decodeSnapshot? (encodeSnapshot snapshot) = some snapshot := by
  cases snapshot
  simp [encodeSnapshot, snapshotPattern, a, decodeSnapshot?]

def ownedPattern (owner snapshot : Pattern) : Pattern :=
  a "petta-call-guard-hot:owned" [owner, snapshot]

def encodeOwned (owned : OwnedSnapshot) : Pattern :=
  ownedPattern (encodeOwner owned.owner) (encodeSnapshot owned.snapshot)

def decodeOwned? : Pattern → Option OwnedSnapshot
  | .apply "petta-call-guard-hot:owned" [owner, snapshot] => do
      let decodedOwner ← decodeOwner? owner
      let decodedSnapshot ← decodeSnapshot? snapshot
      pure ⟨decodedOwner, decodedSnapshot⟩
  | _ => none

@[simp] theorem decodeOwned_encodeOwned (owned : OwnedSnapshot) :
    decodeOwned? (encodeOwned owned) = some owned := by
  cases owned
  simp [encodeOwned, ownedPattern, a, decodeOwned?]

def callPattern (function sources values result : Pattern) : Pattern :=
  a "petta-call-guard-hot:call" [function, sources, values, result]

def encodeCall (call : Call) : Pattern :=
  callPattern (encodeName call.function) (encodeTerms call.sourceArguments)
    (encodeTerms call.evaluatedArguments) (encodeTerm call.result)

def decodeCall? : Pattern → Option Call
  | .apply "petta-call-guard-hot:call" [function, sources, values, result] => do
      let decodedFunction ← decodeName? function
      let decodedSources ← decodeTerms? sources
      let decodedValues ← decodeTerms? values
      let decodedResult ← decodeTerm? result
      pure ⟨decodedFunction, decodedSources, decodedValues, decodedResult⟩
  | _ => none

@[simp] theorem decodeCall_encodeCall (call : Call) :
    decodeCall? (encodeCall call) = some call := by
  cases call
  simp [encodeCall, callPattern, a, decodeCall?]

def modesNil : Pattern := a "petta-call-guard-hot:modes-nil"
def modesCons (mode modes : Pattern) : Pattern :=
  a "petta-call-guard-hot:modes-cons" [mode, modes]

/-- Argument modes in consumption order. -/
def encodeModes : List ArgMode → Pattern
  | [] => modesNil
  | mode :: modes => modesCons (encodeArgMode mode) (encodeModes modes)

def decodeModes? : Pattern → Option (List ArgMode)
  | .apply "petta-call-guard-hot:modes-nil" [] => some []
  | .apply "petta-call-guard-hot:modes-cons" [mode, modes] => do
      let decodedMode ← decodeArgMode? mode
      let decodedModes ← decodeModes? modes
      pure (decodedMode :: decodedModes)
  | _ => none

@[simp] theorem decodeModes_encodeModes (modes : List ArgMode) :
    decodeModes? (encodeModes modes) = some modes := by
  induction modes with
  | nil => rfl
  | cons mode modes inductionHypothesis =>
      simp [encodeModes, modesCons, a, decodeModes?, inductionHypothesis]

def planPattern (occurrence modes result declaration : Pattern) : Pattern :=
  a "petta-call-guard-hot:plan" [occurrence, modes, result, declaration]

def encodeHotPlan (plan : GuardPlan) : Pattern :=
  planPattern (encodeNat plan.declarationOccurrence) (encodeModes plan.argumentModes)
    (encodeResultMode plan.resultMode) (encodeDeclaration plan.declaration)

def decodeHotPlan? : Pattern → Option GuardPlan
  | .apply "petta-call-guard-hot:plan" [occurrence, modes, result, declaration] => do
      let decodedOccurrence ← decodeNat? occurrence
      let decodedModes ← decodeModes? modes
      let decodedResult ← decodeResultMode? result
      let decodedDeclaration ← decodeDeclaration? declaration
      pure ⟨decodedOccurrence, decodedModes, decodedResult, decodedDeclaration⟩
  | _ => none

@[simp] theorem decodeHotPlan_encodeHotPlan (plan : GuardPlan) :
    decodeHotPlan? (encodeHotPlan plan) = some plan := by
  cases plan
  simp [encodeHotPlan, planPattern, a, decodeHotPlan?]

def plansNil : Pattern := a "petta-call-guard-hot:plans-nil"
def plansCons (plan plans : Pattern) : Pattern :=
  a "petta-call-guard-hot:plans-cons" [plan, plans]

/-- Plans in consumption order. -/
def encodeHotPlans : List GuardPlan → Pattern
  | [] => plansNil
  | plan :: plans => plansCons (encodeHotPlan plan) (encodeHotPlans plans)

def decodeHotPlans? : Pattern → Option (List GuardPlan)
  | .apply "petta-call-guard-hot:plans-nil" [] => some []
  | .apply "petta-call-guard-hot:plans-cons" [plan, plans] => do
      let decodedPlan ← decodeHotPlan? plan
      let decodedPlans ← decodeHotPlans? plans
      pure (decodedPlan :: decodedPlans)
  | _ => none

@[simp] theorem decodeHotPlans_encodeHotPlans (plans : List GuardPlan) :
    decodeHotPlans? (encodeHotPlans plans) = some plans := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      simp [encodeHotPlans, plansCons, a, decodeHotPlans?, inductionHypothesis]

def familyPattern (owner revision head arity plans : Pattern) : Pattern :=
  a "petta-call-guard-hot:family" [owner, revision, head, arity, plans]

def encodeHotFamily (family : CompiledGuardFamily) : Pattern :=
  familyPattern (encodeOwner family.owner) (encodeNat family.revision) (encodeName family.head)
    (encodeNat family.arity) (encodeHotPlans family.plans)

def decodeHotFamily? : Pattern → Option CompiledGuardFamily
  | .apply "petta-call-guard-hot:family" [owner, revision, head, arity, plans] => do
      let decodedOwner ← decodeOwner? owner
      let decodedRevision ← decodeNat? revision
      let decodedHead ← decodeName? head
      let decodedArity ← decodeNat? arity
      let decodedPlans ← decodeHotPlans? plans
      pure ⟨decodedOwner, decodedRevision, decodedHead, decodedArity, decodedPlans⟩
  | _ => none

@[simp] theorem decodeHotFamily_encodeHotFamily (family : CompiledGuardFamily) :
    decodeHotFamily? (encodeHotFamily family) = some family := by
  cases family
  simp [encodeHotFamily, familyPattern, a, decodeHotFamily?]

def compiledPattern (family : Pattern) : Pattern :=
  a "petta-call-guard-hot:compiled" [family]
def outsideFragmentPattern : Pattern := a "petta-call-guard-hot:outside-fragment"

def encodeHotCompilation : CompilationResult → Pattern
  | .compiled family => compiledPattern (encodeHotFamily family)
  | .outsideFragment => outsideFragmentPattern

def decodeHotCompilation? : Pattern → Option CompilationResult
  | .apply "petta-call-guard-hot:compiled" [family] =>
      (decodeHotFamily? family).map CompilationResult.compiled
  | .apply "petta-call-guard-hot:outside-fragment" [] => some .outsideFragment
  | _ => none

@[simp] theorem decodeHotCompilation_encodeHotCompilation (result : CompilationResult) :
    decodeHotCompilation? (encodeHotCompilation result) = some result := by
  cases result <;> simp [encodeHotCompilation, compiledPattern, outsideFragmentPattern, a,
    decodeHotCompilation?]

def acceptedNil : Pattern := a "petta-call-guard-hot:accepted-nil"
def acceptedSnoc (accepted declaration : Pattern) : Pattern :=
  a "petta-call-guard-hot:accepted-snoc" [accepted, declaration]

/-- Accepted declarations in installation order, newest last. -/
def encodeAccepted (declarations : List ArrowDeclaration) : Pattern :=
  declarations.foldl
    (fun encoded declaration => acceptedSnoc encoded (encodeDeclaration declaration))
    acceptedNil

@[simp] theorem encodeAccepted_append_singleton
    (declarations : List ArrowDeclaration) (declaration : ArrowDeclaration) :
    encodeAccepted (declarations ++ [declaration]) =
      acceptedSnoc (encodeAccepted declarations) (encodeDeclaration declaration) := by
  simp [encodeAccepted, List.foldl_append]

def decodeAccepted? : Pattern → Option (List ArrowDeclaration)
  | .apply "petta-call-guard-hot:accepted-nil" [] => some []
  | .apply "petta-call-guard-hot:accepted-snoc" [accepted, declaration] => do
      let decodedAccepted ← decodeAccepted? accepted
      let decodedDeclaration ← decodeDeclaration? declaration
      pure (decodedAccepted ++ [decodedDeclaration])
  | _ => none

@[simp] theorem decodeAccepted_encodeAccepted (declarations : List ArrowDeclaration) :
    decodeAccepted? (encodeAccepted declarations) = some declarations := by
  induction declarations using List.reverseRecOn with
  | nil => rfl
  | append_singleton declarations declaration inductionHypothesis =>
      simp [encodeAccepted_append_singleton, acceptedSnoc, a, decodeAccepted?,
        inductionHypothesis]

def reasonOutsideFragment : Pattern := a "petta-call-guard-hot:reason-outside-fragment"
def reasonForeignOwner : Pattern := a "petta-call-guard-hot:reason-foreign-owner"
def reasonStaleRevision : Pattern := a "petta-call-guard-hot:reason-stale-revision"
def reasonWrongHead : Pattern := a "petta-call-guard-hot:reason-wrong-head"
def reasonWrongArity : Pattern := a "petta-call-guard-hot:reason-wrong-arity"

def encodeReason : GuardFallbackReason → Pattern
  | .outsideFragment => reasonOutsideFragment
  | .foreignOwner => reasonForeignOwner
  | .staleRevision => reasonStaleRevision
  | .wrongHead => reasonWrongHead
  | .wrongArity => reasonWrongArity

def decodeReason? : Pattern → Option GuardFallbackReason
  | .apply "petta-call-guard-hot:reason-outside-fragment" [] => some .outsideFragment
  | .apply "petta-call-guard-hot:reason-foreign-owner" [] => some .foreignOwner
  | .apply "petta-call-guard-hot:reason-stale-revision" [] => some .staleRevision
  | .apply "petta-call-guard-hot:reason-wrong-head" [] => some .wrongHead
  | .apply "petta-call-guard-hot:reason-wrong-arity" [] => some .wrongArity
  | _ => none

@[simp] theorem decodeReason_encodeReason (reason : GuardFallbackReason) :
    decodeReason? (encodeReason reason) = some reason := by
  cases reason <;> rfl

def eventBeginPlan (occurrence : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-begin-plan" [occurrence]
def eventUseRawArgument (index : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-use-raw-argument" [index]
def eventEvaluateArgument (index : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-evaluate-argument" [index]
def eventQueryExactType (index expected succeeded : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-query-exact-type" [index, expected, succeeded]
def eventQueryMetatype (index expected succeeded : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-query-metatype" [index, expected, succeeded]
def eventArgumentShapeMismatch (index : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-argument-shape-mismatch" [index]
def eventEvaluateCall (occurrence : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-evaluate-call" [occurrence]
def eventQueryResultType (expected succeeded : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-query-result-type" [expected, succeeded]
def eventQueryResultMetatype (expected succeeded : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-query-result-metatype" [expected, succeeded]
def eventInstallOccurrence (occurrence : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-install-occurrence" [occurrence]
def eventRejectOccurrence (occurrence : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-reject-occurrence" [occurrence]
def eventFallback (reason : Pattern) : Pattern :=
  a "petta-call-guard-hot:event-fallback" [reason]

def encodeEvent : ControlEvent → Pattern
  | .beginPlan occurrence => eventBeginPlan (encodeNat occurrence)
  | .useRawArgument index => eventUseRawArgument (encodeIndex index)
  | .evaluateArgument index => eventEvaluateArgument (encodeIndex index)
  | .queryExactType index expected succeeded =>
      eventQueryExactType (encodeIndex index) (encodeTerm expected) (encodeBool succeeded)
  | .queryMetatype index expected succeeded =>
      eventQueryMetatype (encodeIndex index) (encodeTerm expected) (encodeBool succeeded)
  | .argumentShapeMismatch index => eventArgumentShapeMismatch (encodeIndex index)
  | .evaluateCall occurrence => eventEvaluateCall (encodeNat occurrence)
  | .queryResultType expected succeeded =>
      eventQueryResultType (encodeTerm expected) (encodeBool succeeded)
  | .queryResultMetatype expected succeeded =>
      eventQueryResultMetatype (encodeTerm expected) (encodeBool succeeded)
  | .installOccurrence occurrence => eventInstallOccurrence (encodeNat occurrence)
  | .rejectOccurrence occurrence => eventRejectOccurrence (encodeNat occurrence)
  | .fallback reason => eventFallback (encodeReason reason)

def decodeEvent? : Pattern → Option ControlEvent
  | .apply "petta-call-guard-hot:event-begin-plan" [occurrence] =>
      (decodeNat? occurrence).map ControlEvent.beginPlan
  | .apply "petta-call-guard-hot:event-use-raw-argument" [index] =>
      (decodeIndex? index).map ControlEvent.useRawArgument
  | .apply "petta-call-guard-hot:event-evaluate-argument" [index] =>
      (decodeIndex? index).map ControlEvent.evaluateArgument
  | .apply "petta-call-guard-hot:event-query-exact-type" [index, expected, succeeded] => do
      let decodedIndex ← decodeIndex? index
      let decodedExpected ← decodeTerm? expected
      let decodedSucceeded ← decodeBool? succeeded
      pure (.queryExactType decodedIndex decodedExpected decodedSucceeded)
  | .apply "petta-call-guard-hot:event-query-metatype" [index, expected, succeeded] => do
      let decodedIndex ← decodeIndex? index
      let decodedExpected ← decodeTerm? expected
      let decodedSucceeded ← decodeBool? succeeded
      pure (.queryMetatype decodedIndex decodedExpected decodedSucceeded)
  | .apply "petta-call-guard-hot:event-argument-shape-mismatch" [index] =>
      (decodeIndex? index).map ControlEvent.argumentShapeMismatch
  | .apply "petta-call-guard-hot:event-evaluate-call" [occurrence] =>
      (decodeNat? occurrence).map ControlEvent.evaluateCall
  | .apply "petta-call-guard-hot:event-query-result-type" [expected, succeeded] => do
      let decodedExpected ← decodeTerm? expected
      let decodedSucceeded ← decodeBool? succeeded
      pure (.queryResultType decodedExpected decodedSucceeded)
  | .apply "petta-call-guard-hot:event-query-result-metatype" [expected, succeeded] => do
      let decodedExpected ← decodeTerm? expected
      let decodedSucceeded ← decodeBool? succeeded
      pure (.queryResultMetatype decodedExpected decodedSucceeded)
  | .apply "petta-call-guard-hot:event-install-occurrence" [occurrence] =>
      (decodeNat? occurrence).map ControlEvent.installOccurrence
  | .apply "petta-call-guard-hot:event-reject-occurrence" [occurrence] =>
      (decodeNat? occurrence).map ControlEvent.rejectOccurrence
  | .apply "petta-call-guard-hot:event-fallback" [reason] =>
      (decodeReason? reason).map ControlEvent.fallback
  | _ => none

@[simp] theorem decodeEvent_encodeEvent (event : ControlEvent) :
    decodeEvent? (encodeEvent event) = some event := by
  cases event <;> simp [encodeEvent, decodeEvent?, a, eventBeginPlan, eventUseRawArgument,
    eventEvaluateArgument, eventQueryExactType, eventQueryMetatype, eventArgumentShapeMismatch,
    eventEvaluateCall, eventQueryResultType, eventQueryResultMetatype, eventInstallOccurrence,
    eventRejectOccurrence, eventFallback]

def eventsNil : Pattern := a "petta-call-guard-hot:events-nil"
def eventsSnoc (events event : Pattern) : Pattern :=
  a "petta-call-guard-hot:events-snoc" [events, event]

/-- Events in emission order, newest last. -/
def encodeEvents (events : List ControlEvent) : Pattern :=
  events.foldl (fun encoded event => eventsSnoc encoded (encodeEvent event)) eventsNil

@[simp] theorem encodeEvents_append_singleton (events : List ControlEvent) (event : ControlEvent) :
    encodeEvents (events ++ [event]) = eventsSnoc (encodeEvents events) (encodeEvent event) := by
  simp [encodeEvents, List.foldl_append]

@[simp] theorem encodeEvents_append_pair (events : List ControlEvent) (first second : ControlEvent) :
    encodeEvents (events ++ [first, second]) =
      eventsSnoc (eventsSnoc (encodeEvents events) (encodeEvent first)) (encodeEvent second) := by
  simp [encodeEvents, List.foldl_append]

@[simp] theorem encodeEvents_append_append_singleton
    (events trace : List ControlEvent) (event : ControlEvent) :
    encodeEvents (events ++ (trace ++ [event])) =
      eventsSnoc (encodeEvents (events ++ trace)) (encodeEvent event) := by
  rw [← List.append_assoc, encodeEvents_append_singleton]

def decodeEvents? : Pattern → Option (List ControlEvent)
  | .apply "petta-call-guard-hot:events-nil" [] => some []
  | .apply "petta-call-guard-hot:events-snoc" [events, event] => do
      let decodedEvents ← decodeEvents? events
      let decodedEvent ← decodeEvent? event
      pure (decodedEvents ++ [decodedEvent])
  | _ => none

@[simp] theorem decodeEvents_encodeEvents (events : List ControlEvent) :
    decodeEvents? (encodeEvents events) = some events := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton events event inductionHypothesis =>
      simp [encodeEvents_append_singleton, eventsSnoc, a, decodeEvents?, inductionHypothesis]

def executedPattern (accepted : Pattern) : Pattern :=
  a "petta-call-guard-hot:executed" [accepted]
def fallbackPattern (reason : Pattern) : Pattern :=
  a "petta-call-guard-hot:fallback" [reason]

def encodeOutcome : GuardExecution → Pattern
  | .executed declarations => executedPattern (encodeAccepted declarations)
  | .fallback reason => fallbackPattern (encodeReason reason)

def decodeOutcome? : Pattern → Option GuardExecution
  | .apply "petta-call-guard-hot:executed" [accepted] =>
      (decodeAccepted? accepted).map GuardExecution.executed
  | .apply "petta-call-guard-hot:fallback" [reason] =>
      (decodeReason? reason).map GuardExecution.fallback
  | _ => none

@[simp] theorem decodeOutcome_encodeOutcome (outcome : GuardExecution) :
    decodeOutcome? (encodeOutcome outcome) = some outcome := by
  cases outcome <;> simp [encodeOutcome, executedPattern, fallbackPattern, a, decodeOutcome?]

def observationPattern (outcome events : Pattern) : Pattern :=
  a "petta-call-guard-hot:observation" [outcome, events]

def encodeObservation (observation : ControlObservation) : Pattern :=
  observationPattern (encodeOutcome observation.outcome) (encodeEvents observation.events)

def decodeObservation? : Pattern → Option ControlObservation
  | .apply "petta-call-guard-hot:observation" [outcome, events] => do
      let decodedOutcome ← decodeOutcome? outcome
      let decodedEvents ← decodeEvents? events
      pure ⟨decodedOutcome, decodedEvents⟩
  | _ => none

@[simp] theorem decodeObservation_encodeObservation (observation : ControlObservation) :
    decodeObservation? (encodeObservation observation) = some observation := by
  cases observation
  simp [encodeObservation, observationPattern, a, decodeObservation?]

/-! ## Executor states -/

def requestPattern (owned call compilation : Pattern) : Pattern :=
  a "petta-call-guard-hot:request" [owned, call, compilation]

def plansPattern (snapshot call remaining accepted events : Pattern) : Pattern :=
  a "petta-call-guard-hot:plans" [snapshot, call, remaining, accepted, events]

def argumentsPattern (snapshot call plan remaining index modes sources values accepted
    events : Pattern) : Pattern :=
  a "petta-call-guard-hot:arguments"
    [snapshot, call, plan, remaining, index, modes, sources, values, accepted, events]

def resultPattern (snapshot call plan remaining accepted events : Pattern) : Pattern :=
  a "petta-call-guard-hot:result" [snapshot, call, plan, remaining, accepted, events]

def haltedPattern (observation : Pattern) : Pattern :=
  a "petta-call-guard-hot:halted" [observation]

def encodeExecuteControl : ExecuteControl → Pattern
  | .request current call compilation =>
      requestPattern (encodeOwned current) (encodeCall call) (encodeHotCompilation compilation)
  | .plans snapshot call remaining accepted events =>
      plansPattern (encodeSnapshot snapshot) (encodeCall call) (encodeHotPlans remaining)
        (encodeAccepted accepted) (encodeEvents events)
  | .arguments snapshot call plan remaining index modes sources values accepted events =>
      argumentsPattern (encodeSnapshot snapshot) (encodeCall call) (encodeHotPlan plan)
        (encodeHotPlans remaining) (encodeIndex index) (encodeModes modes)
        (encodeTerms sources) (encodeTerms values) (encodeAccepted accepted)
        (encodeEvents events)
  | .result snapshot call plan remaining accepted events =>
      resultPattern (encodeSnapshot snapshot) (encodeCall call) (encodeHotPlan plan)
        (encodeHotPlans remaining) (encodeAccepted accepted) (encodeEvents events)
  | .halted observation => haltedPattern (encodeObservation observation)

def decodeExecuteControl? : Pattern → Option ExecuteControl
  | .apply "petta-call-guard-hot:request" [owned, call, compilation] => do
      let decodedOwned ← decodeOwned? owned
      let decodedCall ← decodeCall? call
      let decodedCompilation ← decodeHotCompilation? compilation
      pure (.request decodedOwned decodedCall decodedCompilation)
  | .apply "petta-call-guard-hot:plans" [snapshot, call, remaining, accepted, events] => do
      let decodedSnapshot ← decodeSnapshot? snapshot
      let decodedCall ← decodeCall? call
      let decodedRemaining ← decodeHotPlans? remaining
      let decodedAccepted ← decodeAccepted? accepted
      let decodedEvents ← decodeEvents? events
      pure (.plans decodedSnapshot decodedCall decodedRemaining decodedAccepted decodedEvents)
  | .apply "petta-call-guard-hot:arguments"
      [snapshot, call, plan, remaining, index, modes, sources, values, accepted, events] => do
      let decodedSnapshot ← decodeSnapshot? snapshot
      let decodedCall ← decodeCall? call
      let decodedPlan ← decodeHotPlan? plan
      let decodedRemaining ← decodeHotPlans? remaining
      let decodedIndex ← decodeIndex? index
      let decodedModes ← decodeModes? modes
      let decodedSources ← decodeTerms? sources
      let decodedValues ← decodeTerms? values
      let decodedAccepted ← decodeAccepted? accepted
      let decodedEvents ← decodeEvents? events
      pure (.arguments decodedSnapshot decodedCall decodedPlan decodedRemaining decodedIndex
        decodedModes decodedSources decodedValues decodedAccepted decodedEvents)
  | .apply "petta-call-guard-hot:result" [snapshot, call, plan, remaining, accepted, events] => do
      let decodedSnapshot ← decodeSnapshot? snapshot
      let decodedCall ← decodeCall? call
      let decodedPlan ← decodeHotPlan? plan
      let decodedRemaining ← decodeHotPlans? remaining
      let decodedAccepted ← decodeAccepted? accepted
      let decodedEvents ← decodeEvents? events
      pure (.result decodedSnapshot decodedCall decodedPlan decodedRemaining decodedAccepted
        decodedEvents)
  | .apply "petta-call-guard-hot:halted" [observation] =>
      (decodeObservation? observation).map ExecuteControl.halted
  | _ => none

@[simp] theorem decodeExecuteControl_encodeExecuteControl (control : ExecuteControl) :
    decodeExecuteControl? (encodeExecuteControl control) = some control := by
  cases control <;> simp [encodeExecuteControl, decodeExecuteControl?, a, requestPattern,
    plansPattern, argumentsPattern, resultPattern, haltedPattern]

theorem encodeExecuteControl_injective : Function.Injective encodeExecuteControl := by
  intro left right equal
  have decoded := congrArg decodeExecuteControl? equal
  simpa using decoded

/-! ## The decision relations

Every relation is a filter on decoded slots: it answers whether the executor's
decision holds, and nothing else.  Events are built by the rules. -/

def foreignOwnerRelation : String := "PeTTaCallGuardHotForeignOwner"
def staleRevisionRelation : String := "PeTTaCallGuardHotStaleRevision"
def wrongHeadRelation : String := "PeTTaCallGuardHotWrongHead"
def wrongArityRelation : String := "PeTTaCallGuardHotWrongArity"
def currentFamilyRelation : String := "PeTTaCallGuardHotCurrentFamily"
def planHeadMatchesRelation : String := "PeTTaCallGuardHotPlanHeadMatches"
def planHeadDiffersRelation : String := "PeTTaCallGuardHotPlanHeadDiffers"
def rawEqualRelation : String := "PeTTaCallGuardHotRawEqual"
def rawDiffersRelation : String := "PeTTaCallGuardHotRawDiffers"
def exactTypeRelation : String := "PeTTaCallGuardHotExactType"
def metatypeAcceptsRelation : String := "PeTTaCallGuardHotMetatypeAccepts"
def metatypeRejectsRelation : String := "PeTTaCallGuardHotMetatypeRejects"
def argumentShapeMismatchRelation : String := "PeTTaCallGuardHotArgumentShapeMismatch"

/-- The request checks in the executor's order: owner, revision, head, arity. -/
def requestClass (familyOwner currentOwner : SpaceOwner) (familyRevision currentRevision : Nat)
    (familyHead callFunction : String) (familyArity : Nat) (sources : List Term) :
    Option GuardFallbackReason :=
  if familyOwner = currentOwner then
    if familyRevision = currentRevision then
      if familyHead = callFunction then
        if familyArity = sources.length then none
        else some .wrongArity
      else some .wrongHead
    else some .staleRevision
  else some .foreignOwner

def shapeMismatch (modes : List ArgMode) (sources values : List Term) : Bool :=
  match modes, sources, values with
  | [], [], [] => false
  | _ :: _, _ :: _, _ :: _ => false
  | _, _, _ => true

/-- The type decisions of one softcut check, in the executor's order: exact
type first, metatype only after an exact failure. -/
def typeDecision (relation : String) (snapshot : Snapshot) (value expected : Term) : Bool :=
  if relation = exactTypeRelation then decide (GetType snapshot value expected)
  else if relation = metatypeAcceptsRelation then
    decide (¬ GetType snapshot value expected ∧ GetMetatype snapshot value expected)
  else if relation = metatypeRejectsRelation then
    decide (¬ GetType snapshot value expected ∧ ¬ GetMetatype snapshot value expected)
  else false

/-- The reference decisions as a relation environment. -/
def relationEnv : RelationEnv where
  tuples relation arguments :=
    match arguments with
    | [left, right] =>
        if relation = foreignOwnerRelation then
          match decodeOwner? left, decodeOwner? right with
          | some familyOwner, some currentOwner =>
              rowWhen (decide (familyOwner ≠ currentOwner)) arguments
          | _, _ => []
        else if relation = planHeadMatchesRelation then
          match decodeName? left, decodeName? right with
          | some declarationFunction, some callFunction =>
              rowWhen (decide (declarationFunction = callFunction)) arguments
          | _, _ => []
        else if relation = planHeadDiffersRelation then
          match decodeName? left, decodeName? right with
          | some declarationFunction, some callFunction =>
              rowWhen (decide (declarationFunction ≠ callFunction)) arguments
          | _, _ => []
        else if relation = rawEqualRelation then
          match decodeTerm? left, decodeTerm? right with
          | some source, some value => rowWhen (decide (value = source)) arguments
          | _, _ => []
        else if relation = rawDiffersRelation then
          match decodeTerm? left, decodeTerm? right with
          | some source, some value => rowWhen (decide (value ≠ source)) arguments
          | _, _ => []
        else []
    | [first, second, third] =>
        if relation = argumentShapeMismatchRelation then
          match decodeModes? first, decodeTerms? second, decodeTerms? third with
          | some modes, some sources, some values =>
              rowWhen (shapeMismatch modes sources values) arguments
          | _, _, _ => []
        else
          match decodeSnapshot? first, decodeTerm? second, decodeTerm? third with
          | some snapshot, some value, some expected =>
              rowWhen (typeDecision relation snapshot value expected) arguments
          | _, _, _ => []
    | [familyOwner, currentOwner, familyRevision, snapshot] =>
        if relation = staleRevisionRelation then
          match decodeOwner? familyOwner, decodeOwner? currentOwner, decodeNat? familyRevision,
              decodeSnapshot? snapshot with
          | some decodedFamilyOwner, some decodedCurrentOwner, some decodedFamilyRevision,
              some decodedSnapshot =>
              rowWhen (decide (decodedFamilyOwner = decodedCurrentOwner ∧
                decodedFamilyRevision ≠ decodedSnapshot.revision)) arguments
          | _, _, _, _ => []
        else []
    | [familyOwner, currentOwner, familyRevision, snapshot, familyHead, callFunction] =>
        if relation = wrongHeadRelation then
          match decodeOwner? familyOwner, decodeOwner? currentOwner, decodeNat? familyRevision,
              decodeSnapshot? snapshot, decodeName? familyHead, decodeName? callFunction with
          | some decodedFamilyOwner, some decodedCurrentOwner, some decodedFamilyRevision,
              some decodedSnapshot, some decodedFamilyHead, some decodedCallFunction =>
              rowWhen (decide (decodedFamilyOwner = decodedCurrentOwner ∧
                decodedFamilyRevision = decodedSnapshot.revision ∧
                decodedFamilyHead ≠ decodedCallFunction)) arguments
          | _, _, _, _, _, _ => []
        else []
    | [familyOwner, currentOwner, familyRevision, snapshot, familyHead, callFunction,
        familyArity, sources] =>
        match decodeOwner? familyOwner, decodeOwner? currentOwner, decodeNat? familyRevision,
            decodeSnapshot? snapshot, decodeName? familyHead, decodeName? callFunction,
            decodeNat? familyArity, decodeTerms? sources with
        | some decodedFamilyOwner, some decodedCurrentOwner, some decodedFamilyRevision,
            some decodedSnapshot, some decodedFamilyHead, some decodedCallFunction,
            some decodedFamilyArity, some decodedSources =>
            let classification := requestClass decodedFamilyOwner decodedCurrentOwner
              decodedFamilyRevision decodedSnapshot.revision decodedFamilyHead
              decodedCallFunction decodedFamilyArity decodedSources
            if relation = wrongArityRelation then
              rowWhen (decide (classification = some .wrongArity)) arguments
            else if relation = currentFamilyRelation then
              rowWhen (decide (classification = none)) arguments
            else []
        | _, _, _, _, _, _, _, _ => []
    | _ => []

/-! ## Authored rules -/

@[reducible] private def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def callShape : Pattern :=
  callPattern (v "function") (v "sourceArguments") (v "evaluatedArguments") (v "result")

def familyShape : Pattern :=
  familyPattern (v "familyOwner") (v "familyRevision") (v "familyHead") (v "familyArity")
    (v "plans")

def requestShape : Pattern :=
  requestPattern (ownedPattern (v "owner") (v "snapshot")) callShape
    (compiledPattern familyShape)

def declarationShape : Pattern :=
  declarationPattern (v "declarationOccurrence") (v "declarationFunction") (v "inputs")
    (v "output")

def planShape : Pattern :=
  planPattern (v "occurrence") (v "planModes") (v "resultMode") declarationShape

def fallbackHalted (reason : Pattern) : Pattern :=
  haltedPattern (observationPattern (fallbackPattern reason)
    (eventsSnoc eventsNil (eventFallback reason)))

private def requestContext : List (String × TypeExpr) := typed [
  ("owner", "CGOwner"), ("snapshot", "HGSnapshot"),
  ("function", "CGName"), ("sourceArguments", "CGTerms"),
  ("evaluatedArguments", "CGTerms"), ("result", "CGTerm"),
  ("familyOwner", "CGOwner"), ("familyRevision", "CGNat"), ("familyHead", "CGName"),
  ("familyArity", "CGNat"), ("plans", "HGPlans")]

private def plansContext : List (String × TypeExpr) := typed [
  ("snapshot", "HGSnapshot"), ("function", "CGName"), ("sourceArguments", "CGTerms"),
  ("evaluatedArguments", "CGTerms"), ("result", "CGTerm"),
  ("occurrence", "CGNat"), ("planModes", "HGModes"), ("resultMode", "CGResultMode"),
  ("declarationOccurrence", "CGNat"), ("declarationFunction", "CGName"),
  ("inputs", "CGTerms"), ("output", "CGTerm"),
  ("remaining", "HGPlans"), ("accepted", "HGAccepted"), ("events", "HGEvents")]

private def argumentContext : List (String × TypeExpr) := typed [
  ("snapshot", "HGSnapshot"), ("call", "HGCall"),
  ("occurrence", "CGNat"), ("planModes", "HGModes"), ("resultMode", "CGResultMode"),
  ("declarationOccurrence", "CGNat"), ("declarationFunction", "CGName"),
  ("inputs", "CGTerms"), ("output", "CGTerm"),
  ("remaining", "HGPlans"), ("index", "HGIndex"), ("expected", "CGTerm"),
  ("modes", "HGModes"), ("source", "CGTerm"), ("sources", "CGTerms"),
  ("value", "CGTerm"), ("values", "CGTerms"), ("accepted", "HGAccepted"),
  ("events", "HGEvents")]

private def resultContext : List (String × TypeExpr) := typed [
  ("snapshot", "HGSnapshot"), ("function", "CGName"), ("sourceArguments", "CGTerms"),
  ("evaluatedArguments", "CGTerms"), ("result", "CGTerm"),
  ("occurrence", "CGNat"), ("planModes", "HGModes"), ("expected", "CGTerm"),
  ("declarationOccurrence", "CGNat"), ("declarationFunction", "CGName"),
  ("inputs", "CGTerms"), ("output", "CGTerm"),
  ("remaining", "HGPlans"), ("accepted", "HGAccepted"), ("events", "HGEvents")]

def requestOutsideFragmentRule : RewriteRule := {
  name := "petta-call-guard-hot-request-outside-fragment"
  typeContext := typed [("owned", "HGOwned"), ("call", "HGCall")]
  premises := []
  left := requestPattern (v "owned") (v "call") outsideFragmentPattern
  right := fallbackHalted reasonOutsideFragment
}

def requestForeignOwnerRule : RewriteRule := {
  name := "petta-call-guard-hot-request-foreign-owner"
  typeContext := requestContext
  premises := [query foreignOwnerRelation [v "familyOwner", v "owner"]]
  left := requestShape
  right := fallbackHalted reasonForeignOwner
}

def requestStaleRevisionRule : RewriteRule := {
  name := "petta-call-guard-hot-request-stale-revision"
  typeContext := requestContext
  premises := [query staleRevisionRelation
    [v "familyOwner", v "owner", v "familyRevision", v "snapshot"]]
  left := requestShape
  right := fallbackHalted reasonStaleRevision
}

def requestWrongHeadRule : RewriteRule := {
  name := "petta-call-guard-hot-request-wrong-head"
  typeContext := requestContext
  premises := [query wrongHeadRelation
    [v "familyOwner", v "owner", v "familyRevision", v "snapshot", v "familyHead",
      v "function"]]
  left := requestShape
  right := fallbackHalted reasonWrongHead
}

def requestWrongArityRule : RewriteRule := {
  name := "petta-call-guard-hot-request-wrong-arity"
  typeContext := requestContext
  premises := [query wrongArityRelation
    [v "familyOwner", v "owner", v "familyRevision", v "snapshot", v "familyHead",
      v "function", v "familyArity", v "sourceArguments"]]
  left := requestShape
  right := fallbackHalted reasonWrongArity
}

def requestCurrentRule : RewriteRule := {
  name := "petta-call-guard-hot-request-current"
  typeContext := requestContext
  premises := [query currentFamilyRelation
    [v "familyOwner", v "owner", v "familyRevision", v "snapshot", v "familyHead",
      v "function", v "familyArity", v "sourceArguments"]]
  left := requestShape
  right := plansPattern (v "snapshot") callShape (v "plans") acceptedNil eventsNil
}

def plansFinishedRule : RewriteRule := {
  name := "petta-call-guard-hot-plans-finished"
  typeContext := typed [("snapshot", "HGSnapshot"), ("call", "HGCall"),
    ("accepted", "HGAccepted"), ("events", "HGEvents")]
  premises := []
  left := plansPattern (v "snapshot") (v "call") plansNil (v "accepted") (v "events")
  right := haltedPattern (observationPattern (executedPattern (v "accepted")) (v "events"))
}

def planHeadMismatchRule : RewriteRule := {
  name := "petta-call-guard-hot-plan-head-mismatch"
  typeContext := plansContext
  premises := [query planHeadDiffersRelation [v "declarationFunction", v "function"]]
  left := plansPattern (v "snapshot") callShape (plansCons planShape (v "remaining"))
    (v "accepted") (v "events")
  right := plansPattern (v "snapshot") callShape (v "remaining") (v "accepted")
    (eventsSnoc (eventsSnoc (v "events") (eventBeginPlan (v "occurrence")))
      (eventRejectOccurrence (v "occurrence")))
}

def planHeadMatchesRule : RewriteRule := {
  name := "petta-call-guard-hot-plan-head-matches"
  typeContext := plansContext
  premises := [query planHeadMatchesRelation [v "declarationFunction", v "function"]]
  left := plansPattern (v "snapshot") callShape (plansCons planShape (v "remaining"))
    (v "accepted") (v "events")
  right := argumentsPattern (v "snapshot") callShape planShape (v "remaining") indexZero
    (v "planModes") (v "sourceArguments") (v "evaluatedArguments") (v "accepted")
    (eventsSnoc (v "events") (eventBeginPlan (v "occurrence")))
}

def argumentsFinishedRule : RewriteRule := {
  name := "petta-call-guard-hot-arguments-finished"
  typeContext := argumentContext
  premises := []
  left := argumentsPattern (v "snapshot") (v "call") planShape (v "remaining") (v "index")
    modesNil termsNil termsNil (v "accepted") (v "events")
  right := resultPattern (v "snapshot") (v "call") planShape (v "remaining") (v "accepted")
    (eventsSnoc (v "events") (eventEvaluateCall (v "occurrence")))
}

/-- The source of every argument row: the head mode is fixed by `mode`. -/
def argumentSource (mode : Pattern) : Pattern :=
  argumentsPattern (v "snapshot") (v "call") planShape (v "remaining") (v "index")
    (modesCons mode (v "modes")) (termsCons (v "source") (v "sources"))
    (termsCons (v "value") (v "values")) (v "accepted") (v "events")

/-- Advance to the next argument with the given events. -/
def argumentAdvance (events : Pattern) : Pattern :=
  argumentsPattern (v "snapshot") (v "call") planShape (v "remaining")
    (indexSucc (v "index")) (v "modes") (v "sources") (v "values") (v "accepted") events

/-- Reject the plan with the given events. -/
def argumentReject (events : Pattern) : Pattern :=
  plansPattern (v "snapshot") (v "call") (v "remaining") (v "accepted")
    (eventsSnoc events (eventRejectOccurrence (v "occurrence")))

def rawArgumentAcceptedRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-raw-accepted"
  typeContext := argumentContext
  premises := [query rawEqualRelation [v "source", v "value"]]
  left := argumentSource rawArgMode
  right := argumentAdvance (eventsSnoc (v "events") (eventUseRawArgument (v "index")))
}

def rawArgumentRejectedRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-raw-rejected"
  typeContext := argumentContext
  premises := [query rawDiffersRelation [v "source", v "value"]]
  left := argumentSource rawArgMode
  right := argumentReject (eventsSnoc (v "events") (eventUseRawArgument (v "index")))
}

def uncheckedArgumentRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-unchecked"
  typeContext := argumentContext
  premises := []
  left := argumentSource uncheckedArgMode
  right := argumentAdvance (eventsSnoc (v "events") (eventEvaluateArgument (v "index")))
}

def checkedArgumentExactRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-checked-exact"
  typeContext := argumentContext
  premises := [query exactTypeRelation [v "snapshot", v "value", v "expected"]]
  left := argumentSource (checkedArgMode (v "expected"))
  right := argumentAdvance
    (eventsSnoc (eventsSnoc (v "events") (eventEvaluateArgument (v "index")))
      (eventQueryExactType (v "index") (v "expected") truePattern))
}

def checkedArgumentMetatypeAcceptedRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-checked-metatype-accepted"
  typeContext := argumentContext
  premises := [query metatypeAcceptsRelation [v "snapshot", v "value", v "expected"]]
  left := argumentSource (checkedArgMode (v "expected"))
  right := argumentAdvance
    (eventsSnoc (eventsSnoc (eventsSnoc (v "events") (eventEvaluateArgument (v "index")))
      (eventQueryExactType (v "index") (v "expected") falsePattern))
      (eventQueryMetatype (v "index") (v "expected") truePattern))
}

def checkedArgumentMetatypeRejectedRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-checked-metatype-rejected"
  typeContext := argumentContext
  premises := [query metatypeRejectsRelation [v "snapshot", v "value", v "expected"]]
  left := argumentSource (checkedArgMode (v "expected"))
  right := argumentReject
    (eventsSnoc (eventsSnoc (eventsSnoc (v "events") (eventEvaluateArgument (v "index")))
      (eventQueryExactType (v "index") (v "expected") falsePattern))
      (eventQueryMetatype (v "index") (v "expected") falsePattern))
}

def argumentShapeMismatchRule : RewriteRule := {
  name := "petta-call-guard-hot-argument-shape-mismatch"
  typeContext := argumentContext
  premises := [query argumentShapeMismatchRelation [v "modes", v "sources", v "values"]]
  left := argumentsPattern (v "snapshot") (v "call") planShape (v "remaining") (v "index")
    (v "modes") (v "sources") (v "values") (v "accepted") (v "events")
  right := plansPattern (v "snapshot") (v "call") (v "remaining") (v "accepted")
    (eventsSnoc (eventsSnoc (v "events") (eventArgumentShapeMismatch (v "index")))
      (eventRejectOccurrence (v "occurrence")))
}

/-- The source of every result row: the plan's result mode is fixed by
`mode`. -/
def resultSource (mode : Pattern) : Pattern :=
  resultPattern (v "snapshot") callShape
    (planPattern (v "occurrence") (v "planModes") mode declarationShape)
    (v "remaining") (v "accepted") (v "events")

/-- Install the plan's declaration with the given events. -/
def resultInstall (events : Pattern) : Pattern :=
  plansPattern (v "snapshot") callShape (v "remaining")
    (acceptedSnoc (v "accepted") declarationShape)
    (eventsSnoc events (eventInstallOccurrence (v "occurrence")))

/-- Reject the plan with the given events. -/
def resultReject (events : Pattern) : Pattern :=
  plansPattern (v "snapshot") callShape (v "remaining") (v "accepted")
    (eventsSnoc events (eventRejectOccurrence (v "occurrence")))

def uncheckedResultRule : RewriteRule := {
  name := "petta-call-guard-hot-result-unchecked"
  typeContext := resultContext
  premises := []
  left := resultSource uncheckedResultMode
  right := resultInstall (v "events")
}

def checkedResultExactRule : RewriteRule := {
  name := "petta-call-guard-hot-result-checked-exact"
  typeContext := resultContext
  premises := [query exactTypeRelation [v "snapshot", v "result", v "expected"]]
  left := resultSource (checkedResultMode (v "expected"))
  right := resultInstall
    (eventsSnoc (v "events") (eventQueryResultType (v "expected") truePattern))
}

def checkedResultMetatypeAcceptedRule : RewriteRule := {
  name := "petta-call-guard-hot-result-checked-metatype-accepted"
  typeContext := resultContext
  premises := [query metatypeAcceptsRelation [v "snapshot", v "result", v "expected"]]
  left := resultSource (checkedResultMode (v "expected"))
  right := resultInstall
    (eventsSnoc (eventsSnoc (v "events") (eventQueryResultType (v "expected") falsePattern))
      (eventQueryResultMetatype (v "expected") truePattern))
}

def checkedResultMetatypeRejectedRule : RewriteRule := {
  name := "petta-call-guard-hot-result-checked-metatype-rejected"
  typeContext := resultContext
  premises := [query metatypeRejectsRelation [v "snapshot", v "result", v "expected"]]
  left := resultSource (checkedResultMode (v "expected"))
  right := resultReject
    (eventsSnoc (eventsSnoc (v "events") (eventQueryResultType (v "expected") falsePattern))
      (eventQueryResultMetatype (v "expected") falsePattern))
}

def transitions : List RewriteRule := [
  requestOutsideFragmentRule,
  requestForeignOwnerRule,
  requestStaleRevisionRule,
  requestWrongHeadRule,
  requestWrongArityRule,
  requestCurrentRule,
  plansFinishedRule,
  planHeadMismatchRule,
  planHeadMatchesRule,
  argumentsFinishedRule,
  rawArgumentAcceptedRule,
  rawArgumentRejectedRule,
  uncheckedArgumentRule,
  checkedArgumentExactRule,
  checkedArgumentMetatypeAcceptedRule,
  checkedArgumentMetatypeRejectedRule,
  argumentShapeMismatchRule,
  uncheckedResultRule,
  checkedResultExactRule,
  checkedResultMetatypeAcceptedRule,
  checkedResultMetatypeRejectedRule]

/-- The program instruction each rule realizes; the terminal instruction
`halted` has no rule because a halted state has no step. -/
def instructionOf (rule : RewriteRule) : Instruction :=
  if rule.name = requestOutsideFragmentRule.name then .requestOutsideFragment
  else if rule.name = requestForeignOwnerRule.name then .requestForeignOwner
  else if rule.name = requestStaleRevisionRule.name then .requestStaleRevision
  else if rule.name = requestWrongHeadRule.name then .requestWrongHead
  else if rule.name = requestWrongArityRule.name then .requestWrongArity
  else if rule.name = requestCurrentRule.name then .requestCurrent
  else if rule.name = plansFinishedRule.name then .plansFinished
  else if rule.name = planHeadMismatchRule.name then .planHeadMismatch
  else if rule.name = planHeadMatchesRule.name then .planHeadMatches
  else if rule.name = argumentsFinishedRule.name then .argumentsFinished
  else if rule.name = rawArgumentAcceptedRule.name then .argumentRaw
  else if rule.name = rawArgumentRejectedRule.name then .argumentRaw
  else if rule.name = uncheckedArgumentRule.name then .argumentUnchecked
  else if rule.name = checkedArgumentExactRule.name then .argumentChecked
  else if rule.name = checkedArgumentMetatypeAcceptedRule.name then .argumentChecked
  else if rule.name = checkedArgumentMetatypeRejectedRule.name then .argumentChecked
  else if rule.name = argumentShapeMismatchRule.name then .argumentShapeMismatch
  else if rule.name = uncheckedResultRule.name then .resultUnchecked
  else .resultChecked

/-- Every non-terminal program instruction is realized by some rule, and the
rules realize nothing else, in program order. -/
theorem instructionOf_transitions :
    transitions.map instructionOf = [
      .requestOutsideFragment, .requestForeignOwner, .requestStaleRevision, .requestWrongHead,
      .requestWrongArity, .requestCurrent, .plansFinished, .planHeadMismatch, .planHeadMatches,
      .argumentsFinished, .argumentRaw, .argumentRaw, .argumentUnchecked, .argumentChecked,
      .argumentChecked, .argumentChecked, .argumentShapeMismatch, .resultUnchecked,
      .resultChecked, .resultChecked, .resultChecked] := by
  decide

theorem program_eq_halted_cons_instructions :
    program = .halted :: (transitions.map instructionOf).eraseDups := by
  decide

/-! ## The language -/

@[reducible] private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := policy
}

def terms : List GrammarRule := [
  ctor "petta-call-guard:nat-zero" "CGNat" [],
  ctor "petta-call-guard:nat-bit-zero" "CGNat" [("value", "CGNat")],
  ctor "petta-call-guard:nat-bit-one" "CGNat" [("value", "CGNat")],
  ctor "petta-call-guard:char" "CGChar" [("value", "CGNat")],
  ctor "petta-call-guard:chars-nil" "CGChars" [],
  ctor "petta-call-guard:chars-cons" "CGChars" [("head", "CGChar"), ("tail", "CGChars")],
  ctor "petta-call-guard:name" "CGName" [("characters", "CGChars")],
  ctor "petta-call-guard:term-variable" "CGTerm" [("name", "CGName")],
  ctor "petta-call-guard:term-number" "CGTerm" [("lexeme", "CGName")],
  ctor "petta-call-guard:term-string" "CGTerm" [("value", "CGName")],
  ctor "petta-call-guard:term-atom" "CGTerm" [("name", "CGName")],
  ctor "petta-call-guard:term-list" "CGTerm" [("elements", "CGTerms")],
  ctor "petta-call-guard:terms-nil" "CGTerms" [],
  ctor "petta-call-guard:terms-cons" "CGTerms" [("head", "CGTerm"), ("tail", "CGTerms")],
  ctor "petta-call-guard:declaration" "CGDeclaration"
    [("occurrence", "CGNat"), ("function", "CGName"), ("inputs", "CGTerms"),
      ("output", "CGTerm")],
  ctor "petta-call-guard:declarations-nil" "CGDeclarations" [],
  ctor "petta-call-guard:declarations-cons" "CGDeclarations"
    [("head", "CGDeclaration"), ("tail", "CGDeclarations")],
  ctor "petta-call-guard:owner" "CGOwner" [("token", "CGNat")],
  ctor "petta-call-guard:arg-raw" "CGArgMode" [],
  ctor "petta-call-guard:arg-unchecked" "CGArgMode" [],
  ctor "petta-call-guard:arg-checked" "CGArgMode" [("expected", "CGTerm")],
  ctor "petta-call-guard:result-unchecked" "CGResultMode" [],
  ctor "petta-call-guard:result-checked" "CGResultMode" [("expected", "CGTerm")],
  ctor "petta-call-guard-hot:index-zero" "HGIndex" [],
  ctor "petta-call-guard-hot:index-succ" "HGIndex" [("index", "HGIndex")],
  ctor "petta-call-guard-hot:true" "HGBool" [],
  ctor "petta-call-guard-hot:false" "HGBool" [],
  ctor "petta-call-guard-hot:names-nil" "HGNames" [],
  ctor "petta-call-guard-hot:names-cons" "HGNames" [("head", "CGName"), ("tail", "HGNames")],
  ctor "petta-call-guard-hot:annotation" "HGAnnotation"
    [("occurrence", "CGNat"), ("subject", "CGTerm"), ("type", "CGTerm")],
  ctor "petta-call-guard-hot:annotations-nil" "HGAnnotations" [],
  ctor "petta-call-guard-hot:annotations-cons" "HGAnnotations"
    [("head", "HGAnnotation"), ("tail", "HGAnnotations")],
  ctor "petta-call-guard-hot:snapshot" "HGSnapshot"
    [("revision", "CGNat"), ("declarations", "CGDeclarations"),
      ("annotations", "HGAnnotations"), ("registered", "HGNames")],
  ctor "petta-call-guard-hot:owned" "HGOwned" [("owner", "CGOwner"), ("snapshot", "HGSnapshot")],
  ctor "petta-call-guard-hot:call" "HGCall"
    [("function", "CGName"), ("sources", "CGTerms"), ("values", "CGTerms"),
      ("result", "CGTerm")],
  ctor "petta-call-guard-hot:modes-nil" "HGModes" [],
  ctor "petta-call-guard-hot:modes-cons" "HGModes" [("mode", "CGArgMode"), ("modes", "HGModes")],
  ctor "petta-call-guard-hot:plan" "HGPlan"
    [("occurrence", "CGNat"), ("modes", "HGModes"), ("result", "CGResultMode"),
      ("declaration", "CGDeclaration")],
  ctor "petta-call-guard-hot:plans-nil" "HGPlans" [],
  ctor "petta-call-guard-hot:plans-cons" "HGPlans" [("plan", "HGPlan"), ("plans", "HGPlans")],
  ctor "petta-call-guard-hot:family" "HGFamily"
    [("owner", "CGOwner"), ("revision", "CGNat"), ("head", "CGName"), ("arity", "CGNat"),
      ("plans", "HGPlans")],
  ctor "petta-call-guard-hot:compiled" "HGCompilation" [("family", "HGFamily")],
  ctor "petta-call-guard-hot:outside-fragment" "HGCompilation" [],
  ctor "petta-call-guard-hot:accepted-nil" "HGAccepted" [],
  ctor "petta-call-guard-hot:accepted-snoc" "HGAccepted"
    [("accepted", "HGAccepted"), ("declaration", "CGDeclaration")],
  ctor "petta-call-guard-hot:reason-outside-fragment" "HGReason" [],
  ctor "petta-call-guard-hot:reason-foreign-owner" "HGReason" [],
  ctor "petta-call-guard-hot:reason-stale-revision" "HGReason" [],
  ctor "petta-call-guard-hot:reason-wrong-head" "HGReason" [],
  ctor "petta-call-guard-hot:reason-wrong-arity" "HGReason" [],
  ctor "petta-call-guard-hot:event-begin-plan" "HGEvent" [("occurrence", "CGNat")],
  ctor "petta-call-guard-hot:event-use-raw-argument" "HGEvent" [("index", "HGIndex")],
  ctor "petta-call-guard-hot:event-evaluate-argument" "HGEvent" [("index", "HGIndex")],
  ctor "petta-call-guard-hot:event-query-exact-type" "HGEvent"
    [("index", "HGIndex"), ("expected", "CGTerm"), ("succeeded", "HGBool")],
  ctor "petta-call-guard-hot:event-query-metatype" "HGEvent"
    [("index", "HGIndex"), ("expected", "CGTerm"), ("succeeded", "HGBool")],
  ctor "petta-call-guard-hot:event-argument-shape-mismatch" "HGEvent" [("index", "HGIndex")],
  ctor "petta-call-guard-hot:event-evaluate-call" "HGEvent" [("occurrence", "CGNat")],
  ctor "petta-call-guard-hot:event-query-result-type" "HGEvent"
    [("expected", "CGTerm"), ("succeeded", "HGBool")],
  ctor "petta-call-guard-hot:event-query-result-metatype" "HGEvent"
    [("expected", "CGTerm"), ("succeeded", "HGBool")],
  ctor "petta-call-guard-hot:event-install-occurrence" "HGEvent" [("occurrence", "CGNat")],
  ctor "petta-call-guard-hot:event-reject-occurrence" "HGEvent" [("occurrence", "CGNat")],
  ctor "petta-call-guard-hot:event-fallback" "HGEvent" [("reason", "HGReason")],
  ctor "petta-call-guard-hot:events-nil" "HGEvents" [],
  ctor "petta-call-guard-hot:events-snoc" "HGEvents"
    [("events", "HGEvents"), ("event", "HGEvent")],
  ctor "petta-call-guard-hot:executed" "HGOutcome" [("accepted", "HGAccepted")],
  ctor "petta-call-guard-hot:fallback" "HGOutcome" [("reason", "HGReason")],
  ctor "petta-call-guard-hot:observation" "HGObservation"
    [("outcome", "HGOutcome"), ("events", "HGEvents")],
  ctor "petta-call-guard-hot:request" "HGExecuteControl"
    [("owned", "HGOwned"), ("call", "HGCall"), ("compilation", "HGCompilation")] (some .rewrite),
  ctor "petta-call-guard-hot:plans" "HGExecuteControl"
    [("snapshot", "HGSnapshot"), ("call", "HGCall"), ("remaining", "HGPlans"),
      ("accepted", "HGAccepted"), ("events", "HGEvents")] (some .rewrite),
  ctor "petta-call-guard-hot:arguments" "HGExecuteControl"
    [("snapshot", "HGSnapshot"), ("call", "HGCall"), ("plan", "HGPlan"),
      ("remaining", "HGPlans"), ("index", "HGIndex"), ("modes", "HGModes"),
      ("sources", "CGTerms"), ("values", "CGTerms"), ("accepted", "HGAccepted"),
      ("events", "HGEvents")] (some .rewrite),
  ctor "petta-call-guard-hot:result" "HGExecuteControl"
    [("snapshot", "HGSnapshot"), ("call", "HGCall"), ("plan", "HGPlan"),
      ("remaining", "HGPlans"), ("accepted", "HGAccepted"), ("events", "HGEvents")]
    (some .rewrite),
  ctor "petta-call-guard-hot:halted" "HGExecuteControl" [("observation", "HGObservation")]
]

/-- The completed-call executor as an ordinary source presentation. -/
def language : LanguageDef := {
  name := "PeTTaMainlineCallGuardExecuteOperational"
  types := [
    "CGNat", "CGChar", "CGChars", "CGName", "CGTerm", "CGTerms", "CGDeclaration",
    "CGDeclarations", "CGOwner", "CGArgMode", "CGResultMode",
    "HGIndex", "HGBool", "HGNames", "HGAnnotation", "HGAnnotations", "HGSnapshot", "HGOwned",
    "HGCall", "HGModes", "HGPlan", "HGPlans", "HGFamily", "HGCompilation", "HGAccepted",
    "HGReason", "HGEvent", "HGEvents", "HGOutcome", "HGObservation", "HGExecuteControl"]
  terms := terms
  equations := []
  rewrites := transitions
}

theorem language_inventory :
    language.types.length = 31 ∧ language.terms.length = 72 ∧
      language.rewrites.length = 21 := by
  decide

/-! ## Validation -/

private theorem labels_nodup : (language.terms.map (·.label)).Nodup := by
  decide +kernel

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
private theorem rewrites_check :
    ∀ rewrite ∈ transitions, RewriteValidationCertificate.check language rewrite = true := by
  intro rewrite member
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp +decide [
      RewriteValidationCertificate.check, RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      RewriteValidationCertificate.constructorSignatures,
      RewriteValidationCertificate.constructorLabels, language, terms, ctor, typed,
      requestOutsideFragmentRule, requestForeignOwnerRule, requestStaleRevisionRule,
      requestWrongHeadRule, requestWrongArityRule, requestCurrentRule, plansFinishedRule,
      planHeadMismatchRule, planHeadMatchesRule, argumentsFinishedRule,
      rawArgumentAcceptedRule, rawArgumentRejectedRule, uncheckedArgumentRule,
      checkedArgumentExactRule, checkedArgumentMetatypeAcceptedRule,
      checkedArgumentMetatypeRejectedRule, argumentShapeMismatchRule,
      uncheckedResultRule, checkedResultExactRule, checkedResultMetatypeAcceptedRule,
      checkedResultMetatypeRejectedRule, argumentSource, argumentAdvance, argumentReject,
      resultSource, resultInstall, resultReject, requestShape, callShape, familyShape,
      planShape, declarationShape, fallbackHalted, requestContext, plansContext,
      argumentContext, resultContext,
      indexZero, indexSucc, truePattern, falsePattern, namesNil, namesCons,
      annotationPattern, annotationsNil, annotationsCons, snapshotPattern, ownedPattern,
      callPattern, modesNil, modesCons, planPattern, plansNil, plansCons, familyPattern,
      compiledPattern, outsideFragmentPattern, acceptedNil, acceptedSnoc,
      reasonOutsideFragment, reasonForeignOwner, reasonStaleRevision, reasonWrongHead,
      reasonWrongArity, eventBeginPlan, eventUseRawArgument, eventEvaluateArgument,
      eventQueryExactType, eventQueryMetatype, eventArgumentShapeMismatch,
      eventEvaluateCall, eventQueryResultType, eventQueryResultMetatype,
      eventInstallOccurrence, eventRejectOccurrence, eventFallback, eventsNil, eventsSnoc,
      executedPattern, fallbackPattern, observationPattern, requestPattern, plansPattern,
      argumentsPattern, resultPattern, haltedPattern, declarationPattern, termsNil,
      termsCons, rawArgMode, uncheckedArgMode, checkedArgMode, uncheckedResultMode,
      checkedResultMode, a, v, query, foreignOwnerRelation, staleRevisionRelation,
      wrongHeadRelation, wrongArityRelation, currentFamilyRelation,
      planHeadMatchesRelation, planHeadDiffersRelation, rawEqualRelation,
      rawDiffersRelation, exactTypeRelation, metatypeAcceptsRelation,
      metatypeRejectsRelation, argumentShapeMismatchRelation,
      LanguageDef.typeNames, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      Pattern.freeFvarNames, TypeExpr.baseNames, TypeDecl.plain,
      LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams]

private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites, LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite member
  exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check labels_nodup
    (rewrites_check rewrite member)

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide
  exact rewrites_validate

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

/-- The hot executor as a representation. -/
def executeIR : IRLanguage := ⟨validated, relationEnv⟩

/-! ## The step is the root executor -/

open Mettapedia.OSLF.MeTTaIL.ContextualStep in
theorem rules_noncontextual :
    ∀ rule, rule ∈ language.rewrites → NoncontextualPremises rule.premises := by
  intro rule member
  change rule ∈ transitions at member
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact .nil | exact .relationQuery .nil

theorem language_isEquationFree : language.isEquationFree = true := by
  decide

private theorem rootStep_iff_mem_executor (source target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.RootStep relationEnv language source target ↔
      target ∈ rewriteStepWithPremisesUsing relationEnv language source := by
  simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.RootStep, rewriteStepWithPremisesUsing,
    applyRuleWithPremisesUsing]

theorem language_step_iff_mem_executor (source target : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language source
        target ↔
      target ∈ rewriteStepWithPremisesUsing relationEnv language source := by
  unfold Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing
  rw [Mettapedia.OSLF.MeTTaIL.ContextualStep.step_iff_rootStep_of_noncontextualRules
    rules_noncontextual]
  exact rootStep_iff_mem_executor source target

/-! ## Exactness against the executor -/

/-- The executor's step, as the list of encoded successors. -/
def executorImage (source : ExecuteControl) : List Pattern :=
  match executeStep? source with
  | none => []
  | some target => [encodeExecuteControl target]

@[simp] theorem encodeEvents_append (events trace : List ControlEvent) :
    encodeEvents (events ++ trace) =
      trace.foldl (fun encoded event => eventsSnoc encoded (encodeEvent event)) (encodeEvents events) := by
  simp [encodeEvents, List.foldl_append]

@[simp] theorem encodeEvents_nil : encodeEvents [] = eventsNil := rfl

@[simp] theorem encodeEvents_singleton (event : ControlEvent) :
    encodeEvents [event] = eventsSnoc eventsNil (encodeEvent event) := rfl

@[simp] theorem encodeAccepted_nil : encodeAccepted [] = acceptedNil := rfl

@[simp] theorem encodeIndex_succ (index : Nat) :
    encodeIndex (index + 1) = indexSucc (encodeIndex index) := rfl

@[simp] theorem encodeIndex_zero : encodeIndex 0 = indexZero := rfl


/-! ## Guarded evaluation of the matcher

Each lemma fires only when the bindings it consumes are already a concrete
list, so that simplification never expands merges under a binder whose
bindings are still unknown. -/

@[simp] theorem lookup_nil (name : String) : Bindings.lookup [] name = none := rfl

@[simp] theorem lookup_cons (bound : String) (value : Pattern) (rest : Bindings) (name : String) :
    Bindings.lookup ((bound, value) :: rest) name =
      if bound = name then some value else Bindings.lookup rest name := by
  simp only [Bindings.lookup, List.find?_cons]
  by_cases equal : bound = name
  · simp [equal]
  · rw [show (bound == name) = false from beq_eq_false_iff_ne.mpr equal]
    simp [equal]

theorem mergeBindings_cons (bindings : Bindings) (name : String) (value : Pattern)
    (rest : Bindings) :
    mergeBindings bindings ((name, value) :: rest) =
      match Bindings.lookup bindings name with
      | none => mergeBindings ((name, value) :: bindings) rest
      | some existing => if existing = value then mergeBindings bindings rest else none := by
  unfold mergeBindings
  simp only [List.foldlM_cons]
  cases found : bindings.find? (fun entry => entry.1 == name) with
  | none => simp [Bindings.lookup, found]
  | some entry =>
      obtain ⟨bound, existing⟩ := entry
      by_cases same : existing = value
      · simp [Bindings.lookup, found, same]
      · simp [Bindings.lookup, found, same]

@[simp] theorem mergeBindings_nil_right (bindings : Bindings) : mergeBindings bindings [] = some bindings :=
  rfl

@[simp] theorem mergeBindings_nil_cons (name : String) (value : Pattern) (rest : Bindings) :
    mergeBindings [] ((name, value) :: rest) = mergeBindings [(name, value)] rest := by
  rw [mergeBindings_cons]
  rfl

@[simp] theorem mergeBindings_cons_cons (bound : String) (boundValue : Pattern) (bindings : Bindings)
    (name : String) (value : Pattern) (rest : Bindings) :
    mergeBindings ((bound, boundValue) :: bindings) ((name, value) :: rest) =
      match Bindings.lookup ((bound, boundValue) :: bindings) name with
      | none => mergeBindings ((name, value) :: (bound, boundValue) :: bindings) rest
      | some existing =>
          if existing = value then mergeBindings ((bound, boundValue) :: bindings) rest else none :=
  mergeBindings_cons _ _ _ _

/-- Merge one head binding into each tail binding. -/
def mergeInto (head : Bindings) (tails : List Bindings) : List Bindings :=
  tails.filterMap (mergeBindings head)

@[simp] theorem mergeInto_nil (head : Bindings) : mergeInto head [] = [] := rfl

@[simp] theorem mergeInto_nil_cons (tail : Bindings) (tails : List Bindings) :
    mergeInto [] (tail :: tails) =
      match mergeBindings [] tail with
      | none => mergeInto [] tails
      | some merged => merged :: mergeInto [] tails := by
  simp only [mergeInto, List.filterMap_cons]
  cases mergeBindings [] tail <;> rfl

@[simp] theorem mergeInto_cons_cons (bound : String) (value : Pattern) (head : Bindings)
    (tail : Bindings) (tails : List Bindings) :
    mergeInto ((bound, value) :: head) (tail :: tails) =
      match mergeBindings ((bound, value) :: head) tail with
      | none => mergeInto ((bound, value) :: head) tails
      | some merged => merged :: mergeInto ((bound, value) :: head) tails := by
  simp only [mergeInto, List.filterMap_cons]
  cases mergeBindings ((bound, value) :: head) tail <;> rfl

@[simp] theorem matchArgs_nil : matchArgs [] [] = [[]] := by
  simp [matchArgs]

@[simp] theorem matchArgs_cons (pattern term : Pattern) (patterns terms : List Pattern) :
    matchArgs (pattern :: patterns) (term :: terms) =
      (matchPattern pattern term).flatMap fun head => mergeInto head (matchArgs patterns terms) := by
  rw [matchArgs]
  rfl

@[simp] theorem matchPattern_fvar (name : String) (term : Pattern) :
    matchPattern (.fvar name) term = [[(name, term)]] := by
  simp [matchPattern]

@[simp] theorem matchPattern_apply (label label' : String) (params args : List Pattern) :
    matchPattern (.apply label params) (.apply label' args) =
      if label = label' ∧ params.length = args.length then matchArgs params args else [] := by
  simp [matchPattern]

@[simp] theorem applyBindings_fvar_nil (name : String) : applyBindings [] (.fvar name) = .fvar name := by
  simp [applyBindings]

@[simp] theorem applyBindings_fvar_cons (bound : String) (value : Pattern) (bindings : Bindings)
    (name : String) :
    applyBindings ((bound, value) :: bindings) (.fvar name) =
      if bound = name then value else applyBindings bindings (.fvar name) := by
  unfold applyBindings
  simp only [List.find?_cons]
  by_cases equal : bound = name
  · simp [equal]
  · rw [show (bound == name) = false from beq_eq_false_iff_ne.mpr equal]
    simp [equal]

@[simp] theorem applyBindings_apply (bindings : Bindings) (label : String) (args : List Pattern) :
    applyBindings bindings (.apply label args) = .apply label (args.map (applyBindings bindings)) := by
  simp [applyBindings]

@[simp] theorem applyPremises_nil (relEnv : RelationEnv) (lang : LanguageDef) (seed : Bindings) :
    applyPremisesWithEnv relEnv lang [] seed = [seed] := by
  simp [applyPremisesWithEnv]

@[simp] theorem applyPremises_singleton (relEnv : RelationEnv) (lang : LanguageDef)
    (premise : Premise) (seed : Bindings) :
    applyPremisesWithEnv relEnv lang [premise] seed = premiseStepWithEnv relEnv lang seed premise := by
  simp [applyPremisesWithEnv]

@[simp] theorem premiseStep_relationQuery_cons (relEnv : RelationEnv) (lang : LanguageDef)
    (bound : String) (value : Pattern) (bindings : Bindings) (relation : String)
    (args : List Pattern) :
    premiseStepWithEnv relEnv lang ((bound, value) :: bindings) (.relationQuery relation args) =
      relationQueryStep relEnv lang ((bound, value) :: bindings) relation args :=
  rfl

@[simp] theorem relationQueryStep_cons (relEnv : RelationEnv) (lang : LanguageDef)
    (bound : String) (value : Pattern) (bindings : Bindings) (relation : String)
    (args : List Pattern) :
    relationQueryStep relEnv lang ((bound, value) :: bindings) relation args =
      (builtinRelationTuples lang relation (args.map (applyBindings ((bound, value) :: bindings))) ++
        relEnv.tuples relation (args.map (applyBindings ((bound, value) :: bindings)))).flatMap
          fun tuple =>
            (matchRelationArgs ((bound, value) :: bindings) args tuple).filterMap fun premiseBindings =>
              mergeBindings ((bound, value) :: bindings) premiseBindings :=
  rfl

@[simp] theorem matchRelationArgs_nil (seed : Bindings) : matchRelationArgs seed [] [] = [[]] := by
  simp [matchRelationArgs]

@[simp] theorem matchRelationArgs_cons_seed (bound : String) (value : Pattern) (seed : Bindings)
    (argument : Pattern) (arguments : List Pattern) (row : Pattern) (rows : List Pattern) :
    matchRelationArgs ((bound, value) :: seed) (argument :: arguments) (row :: rows) =
      (matchRelationArgument ((bound, value) :: seed) argument row).flatMap fun headBindings =>
        match mergeBindings ((bound, value) :: seed) headBindings with
        | none => []
        | some extended =>
            (matchRelationArgs extended arguments rows).filterMap fun tailBindings =>
              mergeBindings headBindings tailBindings := by
  rw [matchRelationArgs]
  rfl

@[simp] theorem matchRelationArgument_fvar_cons (bound : String) (value : Pattern) (seed : Bindings)
    (name : String) (row : Pattern) :
    matchRelationArgument ((bound, value) :: seed) (.fvar name) row =
      match Bindings.lookup ((bound, value) :: seed) name with
      | some existing => if existing = row then [[]] else []
      | none => [[(name, row)]] :=
  rfl

@[simp] theorem matchRelationArgument_apply (seed : Bindings) (label : String) (args : List Pattern)
    (row : Pattern) :
    matchRelationArgument seed (.apply label args) row =
      matchPattern (applyBindings seed (.apply label args)) row :=
  rfl

@[simp] theorem applyRule_eq (relEnv : RelationEnv) (lang : LanguageDef) (rule : RewriteRule)
    (term : Pattern) :
    applyRuleWithPremisesUsing relEnv lang rule term =
      (matchPattern rule.left term).flatMap fun bindings =>
        (applyPremisesWithEnv relEnv lang rule.premises bindings).map fun final =>
          applyBindings final rule.right := by
  simp [applyRuleWithPremisesUsing,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing]

@[simp] theorem applyBindingsForRule_eq (lang : LanguageDef) (rule : RewriteRule) (bindings : Bindings) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule lang rule bindings =
      applyBindings bindings rule.right := by
  simp [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRuleUsing]

@[simp] theorem rewriteStep_eq (relEnv : RelationEnv) (lang : LanguageDef) (term : Pattern) :
    rewriteStepWithPremisesUsing relEnv lang term =
      lang.rewrites.flatMap fun rule => applyRuleWithPremisesUsing relEnv lang rule term :=
  rfl

local macro "executor_simp" : tactic =>
  `(tactic| simp (config := {maxSteps := 4000000}) [*, executorImage, executeStep?, language,
      transitions, runArgMode, runResultMode, getTypeDecision, getMetatypeDecision,
      requestOutsideFragmentRule, requestForeignOwnerRule, requestStaleRevisionRule,
      requestWrongHeadRule, requestWrongArityRule, requestCurrentRule, plansFinishedRule,
      planHeadMismatchRule, planHeadMatchesRule, argumentsFinishedRule,
      rawArgumentAcceptedRule, rawArgumentRejectedRule, uncheckedArgumentRule,
      checkedArgumentExactRule, checkedArgumentMetatypeAcceptedRule,
      checkedArgumentMetatypeRejectedRule, argumentShapeMismatchRule,
      uncheckedResultRule, checkedResultExactRule, checkedResultMetatypeAcceptedRule,
      checkedResultMetatypeRejectedRule, argumentSource, argumentAdvance, argumentReject,
      resultSource, resultInstall, resultReject, requestShape, planShape, declarationShape,
      callShape, familyShape, fallbackHalted, encodeExecuteControl, encodeOwned, encodeCall,
      encodeHotPlan, encodeHotCompilation, encodeHotFamily, encodeHotPlans, encodeModes,
      encodeTerms, encodeOutcome, encodeObservation, encodeReason, encodeEvent,
      encodeDeclaration, encodeArgMode, encodeResultMode, encodeBool, encodeEvents_append,
      indexZero, indexSucc, truePattern, falsePattern, ownedPattern, callPattern, modesNil,
      modesCons, planPattern, plansNil, plansCons, familyPattern, compiledPattern,
      outsideFragmentPattern, acceptedNil, acceptedSnoc, reasonOutsideFragment,
      reasonForeignOwner, reasonStaleRevision, reasonWrongHead, reasonWrongArity,
      eventBeginPlan, eventUseRawArgument, eventEvaluateArgument, eventQueryExactType,
      eventQueryMetatype, eventArgumentShapeMismatch, eventEvaluateCall,
      eventQueryResultType, eventQueryResultMetatype, eventInstallOccurrence,
      eventRejectOccurrence, eventFallback, eventsNil, eventsSnoc, executedPattern,
      fallbackPattern, observationPattern, requestPattern, plansPattern, argumentsPattern,
      resultPattern, haltedPattern, declarationPattern, termsNil, termsCons, rawArgMode,
      uncheckedArgMode, checkedArgMode, uncheckedResultMode, checkedResultMode,
      decodeModes?, decodeTerms?, decodeArgMode?,
      a, v, query, builtinRelationTuples,
      relationEnv, typeDecision, shapeMismatch, requestClass, rowWhen,
      foreignOwnerRelation, staleRevisionRelation, wrongHeadRelation, wrongArityRelation,
      currentFamilyRelation, planHeadMatchesRelation, planHeadDiffersRelation,
      rawEqualRelation, rawDiffersRelation, exactTypeRelation, metatypeAcceptsRelation,
      metatypeRejectsRelation, argumentShapeMismatchRelation])

set_option maxHeartbeats 4000000 in
theorem executor_exact (source : ExecuteControl) :
    rewriteStepWithPremisesUsing relationEnv language (encodeExecuteControl source) =
      executorImage source := by
  cases source with
  | halted observation => executor_simp
  | request current call compilation =>
      cases compilation with
      | outsideFragment => executor_simp
      | compiled family =>
          by_cases ownerCurrent : family.owner = current.owner
          · by_cases revisionCurrent : family.revision = current.snapshot.revision
            · by_cases headMatches : family.head = call.function
              · by_cases arityMatches : family.arity = call.sourceArguments.length
                · executor_simp
                · executor_simp
              · executor_simp
            · executor_simp
          · executor_simp
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil => executor_simp
      | cons plan remaining =>
          by_cases headMatches : plan.declaration.function = call.function
          · executor_simp
          · executor_simp
  | arguments snapshot call plan remaining index modes sources values accepted events =>
      cases modes with
      | nil => cases sources <;> cases values <;> executor_simp
      | cons mode modes =>
          cases sources with
          | nil => cases mode <;> cases values <;> executor_simp
          | cons source sources =>
              cases values with
              | nil => cases mode <;> executor_simp
              | cons value values =>
                  cases mode with
                  | rawAtom =>
                      by_cases equal : value = source
                      · executor_simp
                      · executor_simp
                  | evalUnchecked => executor_simp
                  | evalSoftcutType expected =>
                      by_cases exact : GetType snapshot value expected
                      · executor_simp
                      · by_cases metatype : GetMetatype snapshot value expected
                        · executor_simp
                        · executor_simp
  | result snapshot call plan remaining accepted events =>
      rcases plan with ⟨occurrence, argumentModes, resultMode, declaration⟩
      cases resultMode with
      | resultUnchecked => executor_simp
      | resultSoftcutType expected =>
          by_cases exact : GetType snapshot call.result expected
          · executor_simp
          · by_cases metatype : GetMetatype snapshot call.result expected
            · executor_simp
            · executor_simp

open Mettapedia.GSLT.LanguageDef.EquationSemantics in
theorem language_step_iff_executeStep (source : ExecuteControl) (wire : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeExecuteControl source) wire ↔
      ∃ target, executeStep? source = some target ∧ wire = encodeExecuteControl target := by
  rw [language_step_iff_mem_executor, executor_exact]
  constructor
  · intro member
    unfold executorImage at member
    split at member
    · simp at member
    · rename_i target step
      simp only [List.mem_singleton] at member
      exact ⟨target, step, member⟩
  · rintro ⟨target, step, rfl⟩
    unfold executorImage
    rw [step]
    simp

theorem language_step_iff_programStep (source : ExecuteControl) (wire : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relationEnv language
        (encodeExecuteControl source) wire ↔
      ∃ target, programGSLT.Step source target ∧ wire = encodeExecuteControl target := by
  rw [language_step_iff_executeStep]
  simp only [programGSLT_step_iff_executeGSLT_step, executeGSLT_step_iff]
  exact Iff.rfl

open Mettapedia.GSLT.LanguageDef.EquationSemantics in
theorem executeIR_step_iff (source : ExecuteControl) (wire : Pattern) :
    executeIR.semantics.Step (encodeExecuteControl source) wire ↔
      ∃ target, executeStep? source = some target ∧ wire = encodeExecuteControl target := by
  change StepModuloEquations (engineBasePremises relationEnv) language _ _ ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators language_isEquationFree]
  exact language_step_iff_executeStep source wire

open Mettapedia.GSLT.LanguageDef.EquationSemantics in
theorem executeIR_equiv_iff (left right : Pattern) :
    executeIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators language_isEquationFree left right

theorem halted_no_step (observation : ControlObservation) (wire : Pattern) :
    ¬ executeIR.semantics.Step (encodeExecuteControl (.halted observation)) wire := by
  intro step
  obtain ⟨target, stepped, _⟩ := (executeIR_step_iff _ _).1 step
  simp [executeStep?] at stepped

#print axioms executor_exact
#print axioms language_step_iff_executeStep
#print axioms executeIR_step_iff


end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
