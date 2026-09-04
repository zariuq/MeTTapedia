import Mettapedia.GSLT.LanguageDef.NormalizationPath
import Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher

/-!
# Actual StructuredC execution of the cold compiler finish transition

This module executes the source-derived cold dispatcher through the authored
StructuredC rewrite system.  Its primitive semantics is structural: it
decodes the current compiler state, projects named fields, tests the concrete
declaration list, and constructs the finished family from explicit operands.
It never calls `compileLanguageStep?` and does not receive a transition name or
an expected target.

The first qualified route is the premise-free finish family.  Later modules
extend the same structural handler with the remaining explicit deltas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.GSLT.LanguageDef.NormalizationPath
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher

/-! ## Explicit ABI values -/

/-- A relation-supplied StructuredC value carrying one canonical call-guard
payload.  The wrapper is an ABI carrier; its payload is decoded before use. -/
def abiValue (payload : Pattern) : Pattern :=
  node "cetta-petta-call-guard:structured-c-abi-value" [payload]

def abiPayload? : Pattern → Option Pattern
  | .apply "cetta-petta-call-guard:structured-c-abi-value" [payload] =>
      some payload
  | _ => none

def decodeAbiWith? {Value : Type}
    (decode : Pattern → Option Value) (value : Pattern) : Option Value := do
  let payload ← abiPayload? value
  decode payload

def stateValue (control : CompileLanguageControl) : Pattern :=
  abiValue (encodeCompileLanguageControl control)

def decodeStateValue? (value : Pattern) : Option CompileLanguageControl :=
  decodeAbiWith? decodeCompileLanguageControl? value

def valueUnit : Pattern := node "structured-c:value-unit"
def readyReceipt : Pattern := node "structured-c:receipt-ready"

def externalReceipt (name : String) (prior : Pattern) : Pattern :=
  node "structured-c:receipt-external"
    [valueSymbol name, valueUnit, valueUnit, prior]

def initialEnvironment (control : CompileLanguageControl) : Pattern :=
  bindName "state" (stateValue control) environmentEmpty

def currentStateArgument?
    (environment supplied : Pattern) : Option CompileLanguageControl := do
  let stored ← lookup? environment (identifier "state")
  if stored = supplied then decodeStateValue? supplied else none

private def externalValue
    (name : String) (value environment receipt : Pattern) :
    Option EvaluationStep :=
  some ⟨.value value, environment, externalReceipt name receipt⟩

private def updatedState
    (name : String) (control : CompileLanguageControl)
    (environment receipt : Pattern) : Option EvaluationStep :=
  some ⟨.value valueUnit,
    bindName "state" (stateValue control) environment,
    externalReceipt name receipt⟩

private def owner? : CompileLanguageControl → Option SpaceOwner
  | .running owner _ _ _ _ _
  | .arguments owner _ _ _ _ _ _ _ _
  | .result owner _ _ _ _ _ _ _ => some owner
  | .halted _ => none

private def revision? : CompileLanguageControl → Option Nat
  | .running _ revision _ _ _ _
  | .arguments _ revision _ _ _ _ _ _ _
  | .result _ revision _ _ _ _ _ _ => some revision
  | .halted _ => none

private def head? : CompileLanguageControl → Option String
  | .running _ _ head _ _ _
  | .arguments _ _ head _ _ _ _ _ _
  | .result _ _ head _ _ _ _ _ => some head
  | .halted _ => none

private def arity? : CompileLanguageControl → Option Nat
  | .running _ _ _ arity _ _
  | .arguments _ _ _ arity _ _ _ _ _
  | .result _ _ _ arity _ _ _ _ => some arity
  | .halted _ => none

private def accepted? : CompileLanguageControl → Option (List GuardPlan)
  | .running _ _ _ _ _ accepted
  | .arguments _ _ _ _ _ _ _ _ accepted
  | .result _ _ _ _ _ _ _ accepted => some accepted
  | .halted _ => none

def phaseValue : CompileLanguageControl → Pattern
  | .running .. => valueSymbol runningPhase
  | .arguments .. => valueSymbol argumentsPhase
  | .result .. => valueSymbol resultPhase
  | .halted .. => valueSymbol haltedPhase

private def declarationsEmptyValue : CompileLanguageControl → Option Pattern
  | .running _ _ _ _ remaining _ =>
      some (if remaining.isEmpty then trueValue else falseValue)
  | _ => none

/-- The five projections shared by every nonterminal cold-compiler phase. -/
inductive CommonProjection where
  | owner
  | revision
  | head
  | arity
  | accepted
deriving DecidableEq, Repr

def CommonProjection.externalName : CommonProjection → String
  | .owner => ownerProjection
  | .revision => revisionProjection
  | .head => headProjection
  | .arity => arityProjection
  | .accepted => acceptedProjection

def CommonProjection.value? (field : CommonProjection) :
    CompileLanguageControl → Option Pattern :=
  match field with
  | .owner => fun control => (owner? control).map
      (fun owner => abiValue (encodeOwner owner))
  | .revision => fun control => (revision? control).map
      (fun revision => abiValue (encodeNat revision))
  | .head => fun control => (head? control).map
      (fun head => abiValue (encodeName head))
  | .arity => fun control => (arity? control).map
      (fun arity => abiValue (encodeNat arity))
  | .accepted => fun control => (accepted? control).map
      (fun accepted => abiValue (encodePlans accepted))

private def projectState?
    (name : String) (projection : CompileLanguageControl → Option Pattern)
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep := do
  let supplied ← arguments[0]?
  let control ← currentStateArgument? environment supplied
  let value ← projection control
  externalValue name value environment receipt

private def finishDelta?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue, acceptedValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeAbiWith? decodeOwner? ownerValue
      let revision ← decodeAbiWith? decodeNat? revisionValue
      let head ← decodeAbiWith? decodeName? headValue
      let arity ← decodeAbiWith? decodeNat? arityValue
      let accepted ← decodeAbiWith? decodePlans? acceptedValue
      match source with
      | .running sourceOwner sourceRevision sourceHead sourceArity []
          sourceAccepted =>
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              head = sourceHead ∧ arity = sourceArity ∧
              accepted = sourceAccepted then
            updatedState setCompiledFamilyDelta
              (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))
              environment receipt
          else
            none
      | _ => none
  | _ => none

/-! ## Finish-qualified structural primitive handler -/

/-- Structural semantics for every projection used before the finish row and
for the finish delta itself.  Every other primitive fails closed. -/
def finishHandler : ExternalHandler :=
  fun name arguments environment receipt =>
    if name = compilePhaseQuery then
      projectState? name (fun control => some (phaseValue control))
        arguments environment receipt
    else if name = ownerProjection then
      projectState? name (fun control => (owner? control).map
        (fun owner => abiValue (encodeOwner owner)))
        arguments environment receipt
    else if name = revisionProjection then
      projectState? name (fun control => (revision? control).map
        (fun revision => abiValue (encodeNat revision)))
        arguments environment receipt
    else if name = headProjection then
      projectState? name (fun control => (head? control).map
        (fun head => abiValue (encodeName head)))
        arguments environment receipt
    else if name = arityProjection then
      projectState? name (fun control => (arity? control).map
        (fun arity => abiValue (encodeNat arity)))
        arguments environment receipt
    else if name = acceptedProjection then
      projectState? name (fun control => (accepted? control).map
        (fun accepted => abiValue (encodePlans accepted)))
        arguments environment receipt
    else if name = declarationsAreEmptyQuery then
      projectState? name declarationsEmptyValue arguments environment receipt
    else if name = setCompiledFamilyDelta then
      finishDelta? arguments environment receipt
    else
      none

/-- Exact phase response for any canonical state present in the surrounding
environment.  Additional bindings do not matter because lookup is by the
authored `state` identifier. -/
theorem finishHandler_phase_exact
    (control : CompileLanguageControl) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    finishHandler compilePhaseQuery [stateValue control] environment receipt =
      some ⟨.value (phaseValue control), environment,
        externalReceipt compilePhaseQuery receipt⟩ := by
  cases control <;>
    simp [finishHandler, compilePhaseQuery, projectState?,
      currentStateArgument?, stored, phaseValue, externalValue,
      decodeStateValue?, stateValue, decodeAbiWith?, abiPayload?, abiValue,
      node]

/-- Every shared field query is exactly the corresponding structural
projection from the canonical current state. -/
theorem finishHandler_commonProjection_exact
    (field : CommonProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    finishHandler field.externalName [stateValue control]
        environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  cases field <;> cases control <;>
    simp [CommonProjection.externalName, CommonProjection.value?, owner?,
      revision?, head?, arity?, accepted?, finishHandler, compilePhaseQuery,
      ownerProjection, revisionProjection, headProjection, arityProjection,
      acceptedProjection, projectState?, currentStateArgument?, stored,
      externalValue, decodeStateValue?, stateValue, decodeAbiWith?,
      abiPayload?, abiValue, node] at projected ⊢
  all_goals exact projected

/-- An exhausted authored declaration row is observed as Boolean true. -/
theorem finishHandler_declarations_empty_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity [] accepted))) :
    finishHandler declarationsAreEmptyQuery
        [stateValue (.running owner revision head arity [] accepted)]
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt declarationsAreEmptyQuery receipt⟩ := by
  simp [finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, projectState?, currentStateArgument?, stored,
    declarationsEmptyValue, externalValue, decodeStateValue?, stateValue,
    decodeAbiWith?, abiPayload?, abiValue, node]

/-- A nonempty authored declaration row is observed as Boolean false.  The
head declaration itself is retained in the state; this query inspects only
the list constructor. -/
theorem finishHandler_declarations_nonempty_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue
          (.running owner revision head arity
            (declaration :: remaining) accepted))) :
    finishHandler declarationsAreEmptyQuery
        [stateValue (.running owner revision head arity
          (declaration :: remaining) accepted)] environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt declarationsAreEmptyQuery receipt⟩ := by
  simp [finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, projectState?, currentStateArgument?, stored,
    declarationsEmptyValue, externalValue, decodeStateValue?, stateValue,
    decodeAbiWith?, abiPayload?, abiValue, node]

/-- The finish delta consumes exactly the six generated operands and updates
only the canonical `state` binding to the corresponding compiled family. -/
theorem finishHandler_finishDelta_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity [] accepted))) :
    finishHandler setCompiledFamilyDelta
        [ stateValue (.running owner revision head arity [] accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodePlans accepted) ]
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue
            (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩)))
          environment,
        externalReceipt setCompiledFamilyDelta receipt⟩ := by
  simp [finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta, finishDelta?,
    currentStateArgument?, stored, updatedState, decodeStateValue?, stateValue,
    decodeAbiWith?, abiPayload?, abiValue, node]

def relations : RelationEnv := relationEnv finishHandler

def reductionLaws : ReductionRespectsEquationsUsing relations
    StructuredC.language :=
  ReductionRespectsEquationsUsing.of_equation_free relations rfl

def targetGSLT : GSLT :=
  languageGSLTUsing relations StructuredC.language reductionLaws

def start (control : CompileLanguageControl) : Pattern :=
  run generatedColdBody (initialEnvironment control) readyReceipt

/-- Observe only a genuinely halted StructuredC configuration whose final
environment contains a canonical call-guard state. -/
def terminalControl? : Pattern → Option CompileLanguageControl
  | .apply "structured-c:halted" [_outcome, environment, _receipt] => do
      let value ← lookup? environment (identifier "state")
      decodeStateValue? value
  | _ => none

/-! ## Discriminating actual-path canary -/

def sourceControl : CompileLanguageControl :=
  .running ⟨0⟩ 0 "f" 0 [] []

def targetControl : CompileLanguageControl :=
  .halted (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩)

theorem source_has_finish_step :
    compileLanguageGSLT.Step sourceControl targetControl := by
  rfl

abbrev targetRun :
    NormalizationPath.Run relations StructuredC.language reductionLaws
      1 64 (start sourceControl) :=
  normalizeFirstRunUsing relations StructuredC.language reductionLaws
    1 64 (start sourceControl)

theorem target_run_observes_exact_source_target :
    terminalControl? targetRun.endpoint = some targetControl := by
  decide +kernel

theorem target_path_is_bounded : targetRun.path.length ≤ 64 :=
  targetRun.length_le

theorem target_path_length_exact : targetRun.path.length = 17 := by
  decide +kernel

theorem target_path_is_nonempty : 0 < targetRun.path.length := by
  decide +kernel

/-- Removing the finish primitive prevents the generated program from reaching
the source target within the same bound. -/
def missingFinishHandler : ExternalHandler :=
  fun name arguments environment receipt =>
    if name = setCompiledFamilyDelta then none
    else finishHandler name arguments environment receipt

def missingFinishRelations : RelationEnv := relationEnv missingFinishHandler

def missingFinishLaws : ReductionRespectsEquationsUsing missingFinishRelations
    StructuredC.language :=
  ReductionRespectsEquationsUsing.of_equation_free missingFinishRelations rfl

theorem missing_finish_does_not_reach_source_target :
    terminalControl?
        (normalizeFirstUsing missingFinishRelations StructuredC.language
          1 64 (start sourceControl)) ≠ some targetControl := by
  decide +kernel

#print axioms source_has_finish_step
#print axioms target_run_observes_exact_source_target
#print axioms target_path_is_bounded
#print axioms target_path_length_exact
#print axioms target_path_is_nonempty
#print axioms missing_finish_does_not_reach_source_target

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
