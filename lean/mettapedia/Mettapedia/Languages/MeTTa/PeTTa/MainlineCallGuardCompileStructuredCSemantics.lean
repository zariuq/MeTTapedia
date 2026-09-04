import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
import Mettapedia.GSLT.LanguageDef.StructuredCStructuralAdmission

/-!
# Structural StructuredC semantics for all cold call-guard families

This module extends the proved finish handler to every cold compiler family.
Projection primitives decode the canonical current state.  Predicate
primitives decide only their named local question.  Mutation primitives check
the current phase and every explicit operand before constructing one exact
successor.  No primitive invokes `compileLanguageStep?`, chooses a rewrite
family, or returns a precomputed expected target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics

private def callValue
    (name : String) (value environment receipt : Pattern) :
    Option EvaluationStep :=
  some ⟨.value value, environment, externalReceipt name receipt⟩

private def callBool
    (name : String) (answer : Bool) (environment receipt : Pattern) :
    Option EvaluationStep :=
  callValue name (if answer then trueValue else falseValue)
    environment receipt

private def writeState
    (name : String) (control : CompileLanguageControl)
    (environment receipt : Pattern) : Option EvaluationStep :=
  some ⟨.value valueUnit,
    bindName "state" (stateValue control) environment,
    externalReceipt name receipt⟩

private def projectState?
    (name : String) (projection : CompileLanguageControl → Option Pattern)
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep := do
  let supplied ← arguments[0]?
  let control ← currentStateArgument? environment supplied
  let value ← projection control
  callValue name value environment receipt

private def declarationAndRemaining? :
    CompileLanguageControl → Option (ArrowDeclaration × List ArrowDeclaration)
  | .running _ _ _ _ (declaration :: remaining) _ =>
      some (declaration, remaining)
  | .arguments _ _ _ _ declaration remaining _ _ _ =>
      some (declaration, remaining)
  | .result _ _ _ _ declaration remaining _ _ =>
      some (declaration, remaining)
  | _ => none

private def remaining? (control : CompileLanguageControl) :
    Option (List ArrowDeclaration) :=
  (declarationAndRemaining? control).map Prod.snd

private def declaration? (control : CompileLanguageControl) :
    Option ArrowDeclaration :=
  (declarationAndRemaining? control).map Prod.fst

/-- The five fields exposed by the generated declaration-binding block.
The projection is taken from the canonical compiler state; its public value
function lets statement-level simulations state exactly which source field a
generated declaration reads. -/
inductive DeclarationProjection where
  | remaining
  | occurrence
  | head
  | inputs
  | output
deriving DecidableEq, Repr

def DeclarationProjection.externalName : DeclarationProjection → String
  | .remaining => remainingProjection
  | .occurrence => occurrenceProjection
  | .head => declarationHeadProjection
  | .inputs => inputsProjection
  | .output => outputProjection

def DeclarationProjection.value? (field : DeclarationProjection) :
    CompileLanguageControl → Option Pattern :=
  match field with
  | .remaining => fun control => (remaining? control).map
      (fun remaining => abiValue (encodeDeclarations remaining))
  | .occurrence => fun control => (declaration? control).map
      (fun declaration => abiValue (encodeNat declaration.occurrence))
  | .head => fun control => (declaration? control).map
      (fun declaration => abiValue (encodeName declaration.function))
  | .inputs => fun control => (declaration? control).map
      (fun declaration => abiValue (encodeTerms declaration.inputTypes))
  | .output => fun control => (declaration? control).map
      (fun declaration => abiValue (encodeTerm declaration.outputType))

private def modes? : CompileLanguageControl → Option (List ArgMode)
  | .arguments _ _ _ _ _ _ _ modes _
  | .result _ _ _ _ _ _ modes _ => some modes
  | _ => none

private def inputCursor? : CompileLanguageControl → Option (List Term)
  | .arguments _ _ _ _ _ _ inputCursor _ _ => some inputCursor
  | _ => none

private def encodeAbiProjection {Value : Type}
    (projection : CompileLanguageControl → Option Value)
    (encode : Value → Pattern) (control : CompileLanguageControl) :
    Option Pattern :=
  (projection control).map (fun value => abiValue (encode value))

private def inputCursorEmptyValue :
    CompileLanguageControl → Option Pattern
  | .arguments _ _ _ _ _ _ inputCursor _ _ =>
      some (if inputCursor.isEmpty then trueValue else falseValue)
  | _ => none

private def inputHeadProjectionValue :
    CompileLanguageControl → Option Pattern
  | .arguments _ _ _ _ _ _ (expected :: _) _ _ =>
      some (abiValue (encodeTerm expected))
  | _ => none

private def inputTailProjectionValue :
    CompileLanguageControl → Option Pattern
  | .arguments _ _ _ _ _ _ (_ :: tail) _ _ =>
      some (abiValue (encodeTerms tail))
  | _ => none

/-- The argument-phase fields exposed after the authored declaration row.
`modes` is also meaningful in the result phase; head and tail require a
nonempty argument cursor. -/
inductive ArgumentProjection where
  | modes
  | inputHead
  | inputTail
deriving DecidableEq, Repr

def ArgumentProjection.externalName : ArgumentProjection → String
  | .modes => modesProjection
  | .inputHead => inputHeadProjection
  | .inputTail => inputTailProjection

def ArgumentProjection.value? (field : ArgumentProjection) :
    CompileLanguageControl → Option Pattern :=
  match field with
  | .modes => encodeAbiProjection modes? encodeArgModes
  | .inputHead => inputHeadProjectionValue
  | .inputTail => inputTailProjectionValue

/-- The three literal classifiers used by the ordered argument and result
dispatchers.  Each classifier retains both its external query and the exact
PeTTa term it recognizes. -/
inductive LiteralPredicate where
  | atom
  | undefined
  | hole
deriving DecidableEq, Repr

def LiteralPredicate.externalName : LiteralPredicate → String
  | .atom => termIsAtomQuery
  | .undefined => termIsUndefinedQuery
  | .hole => termIsHoleQuery

def LiteralPredicate.term : LiteralPredicate → Term
  | .atom => atomType
  | .undefined => undefinedType
  | .hole => holeType

/-- Canonical target-ABI operands for one argument mode. -/
def argumentModeTag : ArgMode → Pattern
  | .rawAtom => valueSymbol rawArgumentMode
  | .evalUnchecked => valueSymbol uncheckedArgumentMode
  | .evalSoftcutType _ => valueSymbol checkedArgumentMode

def argumentModePayload : ArgMode → Pattern
  | .rawAtom
  | .evalUnchecked => valueSymbol noModePayload
  | .evalSoftcutType expected => abiValue (encodeTerm expected)

/-- Canonical target-ABI operands for one result mode. -/
def resultModeTag : ResultMode → Pattern
  | .resultUnchecked => valueSymbol uncheckedResultMode
  | .resultSoftcutType _ => valueSymbol checkedResultMode

def resultModePayload : ResultMode → Pattern
  | .resultUnchecked => valueSymbol noModePayload
  | .resultSoftcutType expected => abiValue (encodeTerm expected)

/-- Canonical target operand for a result term.  The three authored literal
rows retain their dedicated ABI symbols; all other terms use the exact term
codec. -/
def resultOutputValue (output : Term) : Pattern :=
  if output = undefinedType then valueSymbol undefinedTerm
  else if output = holeType then valueSymbol holeTerm
  else if output = atomType then valueSymbol atomTerm
  else abiValue (encodeTerm output)

private def decodeTermValue? (value : Pattern) : Option Term :=
  decodeAbiWith? decodeTerm? value

private def decodeTermsValue? (value : Pattern) : Option (List Term) :=
  decodeAbiWith? decodeTerms? value

private def decodeNameValue? (value : Pattern) : Option String :=
  decodeAbiWith? decodeName? value

private def decodeNatValue? (value : Pattern) : Option Nat :=
  decodeAbiWith? decodeNat? value

private def decodeOwnerValue? (value : Pattern) : Option SpaceOwner :=
  decodeAbiWith? decodeOwner? value

private def decodeDeclarationValue? (value : Pattern) :
    Option ArrowDeclaration :=
  decodeAbiWith? decodeDeclaration? value

private def decodeDeclarationsValue? (value : Pattern) :
    Option (List ArrowDeclaration) :=
  decodeAbiWith? decodeDeclarations? value

private def decodeArgModesValue? (value : Pattern) : Option (List ArgMode) :=
  decodeAbiWith? decodeArgModes? value

private def decodePlansValue? (value : Pattern) : Option (List GuardPlan) :=
  decodeAbiWith? decodePlans? value

private def decodeArgumentModeOperands?
    (mode payload : Pattern) : Option ArgMode :=
  if mode = valueSymbol rawArgumentMode ∧
      payload = valueSymbol noModePayload then
    some .rawAtom
  else if mode = valueSymbol uncheckedArgumentMode ∧
      payload = valueSymbol noModePayload then
    some .evalUnchecked
  else if mode = valueSymbol checkedArgumentMode then
    (decodeTermValue? payload).map ArgMode.evalSoftcutType
  else
    none

private def decodeResultOutput? (value : Pattern) : Option Term :=
  if value = valueSymbol undefinedTerm then some undefinedType
  else if value = valueSymbol holeTerm then some holeType
  else if value = valueSymbol atomTerm then some atomType
  else decodeTermValue? value

private theorem decodeResultOutputValue_exact (output : Term) :
    decodeResultOutput? (resultOutputValue output) = some output := by
  by_cases isUndefined : output = undefinedType
  · subst output
    simp [resultOutputValue, decodeResultOutput?, undefinedTerm, valueSymbol,
      identifier, node, token]
  · by_cases isHole : output = holeType
    · subst output
      simp [resultOutputValue, decodeResultOutput?, isUndefined,
        undefinedTerm, holeTerm, valueSymbol, identifier, node, token]
    · by_cases isAtom : output = atomType
      · subst output
        simp [resultOutputValue, decodeResultOutput?, isUndefined, isHole,
          undefinedTerm, holeTerm, atomTerm, valueSymbol, identifier, node,
          token]
      · simp [resultOutputValue, decodeResultOutput?, isUndefined, isHole,
          isAtom, decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue,
          undefinedTerm, holeTerm, atomTerm, valueSymbol, identifier, node,
          token]

private def decodeResultModeOperands?
    (mode payload : Pattern) : Option ResultMode :=
  if mode = valueSymbol uncheckedResultMode ∧
      payload = valueSymbol noModePayload then
    some .resultUnchecked
  else if mode = valueSymbol checkedResultMode then
    (decodeTermValue? payload).map ResultMode.resultSoftcutType
  else
    none

private theorem decodeResultModeOperands_exact (mode : ResultMode) :
    decodeResultModeOperands? (resultModeTag mode) (resultModePayload mode) =
      some mode := by
  cases mode <;>
    simp [decodeResultModeOperands?, resultModeTag, resultModePayload,
      decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue, valueSymbol,
      identifier, node, token]

private def setCompileRunning?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue,
      remainingValue, acceptedValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeOwnerValue? ownerValue
      let revision ← decodeNatValue? revisionValue
      let targetHead ← decodeNameValue? headValue
      let arity ← decodeNatValue? arityValue
      let remaining ← decodeDeclarationsValue? remainingValue
      let accepted ← decodePlansValue? acceptedValue
      match source with
      | .running sourceOwner sourceRevision sourceHead sourceArity
          (declaration :: sourceRemaining) sourceAccepted =>
          let exactSkipHead :=
            targetHead = sourceHead ∧ declaration.function ≠ sourceHead
          let exactSkipArity :=
            targetHead = declaration.function ∧
              sourceHead = declaration.function ∧
              declaration.inputTypes.length ≠ sourceArity
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              arity = sourceArity ∧ remaining = sourceRemaining ∧
              accepted = sourceAccepted ∧
              (exactSkipHead ∨ exactSkipArity) then
            writeState setCompileRunningDelta
              (.running owner revision targetHead arity remaining accepted)
              environment receipt
          else none
      | _ => none
  | _ => none

private def startCompileArguments?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue,
      occurrenceValue, declarationHeadValue, inputsValue, outputValue,
      remainingValue, cursorValue, acceptedValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeOwnerValue? ownerValue
      let revision ← decodeNatValue? revisionValue
      let head ← decodeNameValue? headValue
      let arity ← decodeNatValue? arityValue
      let occurrence ← decodeNatValue? occurrenceValue
      let declarationHead ← decodeNameValue? declarationHeadValue
      let inputs ← decodeTermsValue? inputsValue
      let output ← decodeTermValue? outputValue
      let remaining ← decodeDeclarationsValue? remainingValue
      let cursor ← decodeTermsValue? cursorValue
      let accepted ← decodePlansValue? acceptedValue
      let declaration : ArrowDeclaration :=
        ⟨occurrence, declarationHead, inputs, output⟩
      match source with
      | .running sourceOwner sourceRevision sourceHead sourceArity
          (sourceDeclaration :: sourceRemaining) sourceAccepted =>
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              head = sourceHead ∧ arity = sourceArity ∧
              declaration = sourceDeclaration ∧
              remaining = sourceRemaining ∧ cursor = inputs ∧
              accepted = sourceAccepted ∧
              declaration.function = sourceHead ∧
              declaration.inputTypes.length = sourceArity then
            writeState startCompileArgumentsDelta
              (.arguments owner revision head arity declaration remaining
                cursor [] accepted) environment receipt
          else none
      | _ => none
  | _ => none

private def appendArgumentMode?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue,
      occurrenceValue, declarationHeadValue, inputsValue, outputValue,
      remainingValue, inputCursorValue, modesValue, acceptedValue,
      modeValue, payloadValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeOwnerValue? ownerValue
      let revision ← decodeNatValue? revisionValue
      let head ← decodeNameValue? headValue
      let arity ← decodeNatValue? arityValue
      let occurrence ← decodeNatValue? occurrenceValue
      let declarationHead ← decodeNameValue? declarationHeadValue
      let inputs ← decodeTermsValue? inputsValue
      let output ← decodeTermValue? outputValue
      let remaining ← decodeDeclarationsValue? remainingValue
      let inputCursor ← decodeTermsValue? inputCursorValue
      let modes ← decodeArgModesValue? modesValue
      let accepted ← decodePlansValue? acceptedValue
      let mode ← decodeArgumentModeOperands? modeValue payloadValue
      let declaration : ArrowDeclaration :=
        ⟨occurrence, declarationHead, inputs, output⟩
      match source with
      | .arguments sourceOwner sourceRevision sourceHead sourceArity
          sourceDeclaration sourceRemaining (expected :: sourceCursor)
          sourceModes sourceAccepted =>
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              head = sourceHead ∧ arity = sourceArity ∧
              declaration = sourceDeclaration ∧
              remaining = sourceRemaining ∧
              inputCursor = sourceCursor ∧ modes = sourceModes ∧
              accepted = sourceAccepted ∧
              compileArgMode expected = some mode then
            writeState appendArgumentModeDelta
              (.arguments owner revision head arity declaration remaining
                inputCursor (modes ++ [mode]) accepted)
              environment receipt
          else none
      | _ => none
  | _ => none

private def setCompileResult?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue,
      occurrenceValue, declarationHeadValue, inputsValue, outputValue,
      remainingValue, modesValue, acceptedValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeOwnerValue? ownerValue
      let revision ← decodeNatValue? revisionValue
      let head ← decodeNameValue? headValue
      let arity ← decodeNatValue? arityValue
      let occurrence ← decodeNatValue? occurrenceValue
      let declarationHead ← decodeNameValue? declarationHeadValue
      let inputs ← decodeTermsValue? inputsValue
      let output ← decodeTermValue? outputValue
      let remaining ← decodeDeclarationsValue? remainingValue
      let modes ← decodeArgModesValue? modesValue
      let accepted ← decodePlansValue? acceptedValue
      let declaration : ArrowDeclaration :=
        ⟨occurrence, declarationHead, inputs, output⟩
      match source with
      | .arguments sourceOwner sourceRevision sourceHead sourceArity
          sourceDeclaration sourceRemaining [] sourceModes sourceAccepted =>
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              head = sourceHead ∧ arity = sourceArity ∧
              declaration = sourceDeclaration ∧
              remaining = sourceRemaining ∧ modes = sourceModes ∧
              accepted = sourceAccepted then
            writeState setCompileResultDelta
              (.result owner revision head arity declaration remaining modes
                accepted) environment receipt
          else none
      | _ => none
  | _ => none

private def appendCompiledPlan?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep :=
  match arguments with
  | [state, ownerValue, revisionValue, headValue, arityValue,
      remainingValue, acceptedValue, occurrenceValue, modesValue,
      declarationHeadValue, inputsValue, outputValue, resultModeValue,
      payloadValue] => do
      let source ← currentStateArgument? environment state
      let owner ← decodeOwnerValue? ownerValue
      let revision ← decodeNatValue? revisionValue
      let head ← decodeNameValue? headValue
      let arity ← decodeNatValue? arityValue
      let remaining ← decodeDeclarationsValue? remainingValue
      let accepted ← decodePlansValue? acceptedValue
      let occurrence ← decodeNatValue? occurrenceValue
      let modes ← decodeArgModesValue? modesValue
      let declarationHead ← decodeNameValue? declarationHeadValue
      let inputs ← decodeTermsValue? inputsValue
      let output ← decodeResultOutput? outputValue
      let resultMode ←
        decodeResultModeOperands? resultModeValue payloadValue
      let declaration : ArrowDeclaration :=
        ⟨occurrence, declarationHead, inputs, output⟩
      let plan : GuardPlan := ⟨occurrence, modes, resultMode, declaration⟩
      match source with
      | .result sourceOwner sourceRevision sourceHead sourceArity
          sourceDeclaration sourceRemaining sourceModes sourceAccepted =>
          if owner = sourceOwner ∧ revision = sourceRevision ∧
              head = sourceHead ∧ arity = sourceArity ∧
              declaration = sourceDeclaration ∧
              remaining = sourceRemaining ∧ modes = sourceModes ∧
              accepted = sourceAccepted ∧
              compileResultMode sourceDeclaration.outputType =
                some resultMode then
            writeState appendCompiledPlanDelta
              (.running owner revision head arity remaining
                (accepted ++ [plan])) environment receipt
          else none
      | _ => none
  | _ => none

private def setOutsideFragment?
    (arguments : List Pattern) (environment receipt : Pattern) :
    Option EvaluationStep := do
  let state ← arguments[0]?
  let source ← currentStateArgument? environment state
  let unsupported : Bool := match source with
    | .arguments _ _ _ _ _ _ (expected :: _) _ _ =>
        (compileArgMode expected).isNone
    | .result _ _ _ _ declaration _ _ _ =>
        (compileResultMode declaration.outputType).isNone
    | _ => false
  if unsupported then
    writeState setOutsideFragmentDelta (.halted .outsideFragment)
      environment receipt
  else
    none

private def localPredicate?
    (name : String) (arguments : List Pattern)
    (environment receipt : Pattern) : Option EvaluationStep :=
  if name = termIsAtomQuery then do
    let value ← arguments[0]?
    let term ← decodeTermValue? value
    callBool name (term = atomType) environment receipt
  else if name = termIsUndefinedQuery then do
    let value ← arguments[0]?
    let term ← decodeTermValue? value
    callBool name (term = undefinedType) environment receipt
  else if name = termIsHoleQuery then do
    let value ← arguments[0]?
    let term ← decodeTermValue? value
    callBool name (term = holeType) environment receipt
  else if name = nameNotEqualQuery then
    match arguments with
    | [leftValue, rightValue] => do
        let left ← decodeNameValue? leftValue
        let right ← decodeNameValue? rightValue
        callBool name (left ≠ right) environment receipt
    | _ => none
  else if name = arityDiffersQuery ∨ name = arityMatchesQuery then
    match arguments with
    | [inputsValue, arityValue] => do
        let inputs ← decodeTermsValue? inputsValue
        let arity ← decodeNatValue? arityValue
        let doesMatch := inputs.length = arity
        callBool name
          (if name = arityMatchesQuery then doesMatch else !doesMatch)
          environment receipt
    | _ => none
  else if name = inputIsCheckedQuery ∨ name = inputIsOpenQuery then do
    let value ← arguments[0]?
    let term ← decodeTermValue? value
    let mode := compileArgMode term
    let answer := if name = inputIsCheckedQuery then
      match mode with
      | some (.evalSoftcutType _) => true
      | _ => false
    else mode.isNone
    callBool name answer environment receipt
  else if name = resultIsCheckedQuery ∨ name = resultIsOpenQuery then do
    let value ← arguments[0]?
    let term ← decodeTermValue? value
    let mode := compileResultMode term
    let answer := if name = resultIsCheckedQuery then
      match mode with
      | some (.resultSoftcutType _) => true
      | _ => false
    else mode.isNone
    callBool name answer environment receipt
  else
    none

/-- Complete structural primitive semantics for the generated cold body. -/
def handler : ExternalHandler :=
  fun name arguments environment receipt =>
    match finishHandler name arguments environment receipt with
    | some result => some result
    | none =>
      if name = inputCursorIsEmptyQuery then
        projectState? name inputCursorEmptyValue arguments environment receipt
      else if name = remainingProjection then
        projectState? name
          (encodeAbiProjection remaining? encodeDeclarations)
          arguments environment receipt
      else if name = occurrenceProjection then
        projectState? name
          (fun control => (declaration? control).map
            (fun declaration => abiValue (encodeNat declaration.occurrence)))
          arguments environment receipt
      else if name = declarationHeadProjection then
        projectState? name
          (fun control => (declaration? control).map
            (fun declaration => abiValue (encodeName declaration.function)))
          arguments environment receipt
      else if name = inputsProjection then
        projectState? name
          (fun control => (declaration? control).map
            (fun declaration => abiValue
              (encodeTerms declaration.inputTypes)))
          arguments environment receipt
      else if name = outputProjection then
        projectState? name
          (fun control => (declaration? control).map
            (fun declaration => abiValue (encodeTerm declaration.outputType)))
          arguments environment receipt
      else if name = modesProjection then
        projectState? name ArgumentProjection.modes.value?
          arguments environment receipt
      else if name = inputHeadProjection then
        projectState? name ArgumentProjection.inputHead.value?
          arguments environment receipt
      else if name = inputTailProjection then
        projectState? name ArgumentProjection.inputTail.value?
          arguments environment receipt
      else if name = setCompileRunningDelta then
        setCompileRunning? arguments environment receipt
      else if name = startCompileArgumentsDelta then
        startCompileArguments? arguments environment receipt
      else if name = appendArgumentModeDelta then
        appendArgumentMode? arguments environment receipt
      else if name = setCompileResultDelta then
        setCompileResult? arguments environment receipt
      else if name = appendCompiledPlanDelta then
        appendCompiledPlan? arguments environment receipt
      else if name = setOutsideFragmentDelta then
        setOutsideFragment? arguments environment receipt
      else
        localPredicate? name arguments environment receipt

def relations : RelationEnv := relationEnv handler

def reductionLaws : ReductionRespectsEquationsUsing relations
    StructuredC.language :=
  ReductionRespectsEquationsUsing.of_equation_free relations rfl

def targetGSLT : GSLT :=
  languageGSLTUsing relations StructuredC.language reductionLaws

def runControl (control : CompileLanguageControl) : Pattern :=
  run generatedColdBody (initialEnvironment control) readyReceipt

/-! ## Structural call admission -/

/-- Every result supplied by the structurally smaller finish handler remains
exact in the complete cold-compiler handler. -/
theorem handler_of_finishHandler_exact
    (name : String) (arguments : List Pattern)
    (environment receipt : Pattern) (step : EvaluationStep)
    (handled :
      finishHandler name arguments environment receipt = some step) :
    handler name arguments environment receipt = some step := by
  simp [handler, handled]

/-- Phase inspection is computed from the canonical state stored in the
runtime environment.  The theorem is parametric in surrounding bindings and
the incoming receipt, so later statement-level proofs can reuse it after
earlier declarations have extended both. -/
theorem phase_evaluation_exact
    (control : CompileLanguageControl) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    evaluate? handler (call compilePhaseQuery [variableExpression "state"])
        environment receipt =
      some ⟨.value (phaseValue control), environment,
        externalReceipt compilePhaseQuery receipt⟩ := by
  have handled :
      handler compilePhaseQuery [stateValue control] environment receipt =
        some ⟨.value (phaseValue control), environment,
          externalReceipt compilePhaseQuery receipt⟩ := by
    simp [handler,
      finishHandler_phase_exact control environment receipt stored]
  exact evaluate_single_variable_call_exact handler compilePhaseQuery "state"
    (stateValue control) environment receipt _ stored handled

/-- Every shared nonterminal field query is admitted through the same
one-variable structural call boundary as phase inspection. -/
theorem common_projection_evaluation_exact
    (field : CommonProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    evaluate? handler
        (call field.externalName [variableExpression "state"])
        environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  have handled :
      handler field.externalName [stateValue control] environment receipt =
        some ⟨.value value, environment,
          externalReceipt field.externalName receipt⟩ := by
    simp [handler,
      finishHandler_commonProjection_exact field control value environment
        receipt projected stored]
  exact evaluate_single_variable_call_exact handler field.externalName "state"
    (stateValue control) environment receipt _ stored handled

/-- One generated common-field declaration is an exact authored StructuredC
step.  The result environment is persistent shadowing, and the external-call
receipt is retained. -/
theorem common_projection_declare_rewrite_exact
    (field : CommonProjection) (slotName typeName : String)
    (control : CompileLanguageControl) (value rest environment receipt : Pattern)
    (projected : field.value? control = some value)
    (storedState :
      lookup? environment (identifier "state") = some (stateValue control)) :
    rewriteAt (engineBasePremises relations) StructuredC.language 1
        (run (consStatement
          (declare slotName (namedType typeName)
            (call field.externalName [variableExpression "state"])) rest)
          environment receipt) =
      [run rest (bindName slotName value environment)
        (externalReceipt field.externalName receipt)] := by
  have evaluated := common_projection_evaluation_exact field control value
    environment receipt projected storedState
  have storedValue :
      store? environment (identifier slotName) value =
        some (bindName slotName value environment) := by
    simp [store?, identifierName?, bindName, identifier, node, token]
  simpa [relations, declare, node, StructuredC.a] using
    declare_rewriteAt_exact_of_evaluate handler (identifier slotName)
      (namedType typeName)
      (call field.externalName [variableExpression "state"])
      rest environment receipt value environment
      (externalReceipt field.externalName receipt)
      (bindName slotName value environment) evaluated storedValue

/-- Every generated declaration-field query returns exactly the corresponding
field of the canonical source state.  The complete handler, rather than a
parallel projection evaluator, supplies the result. -/
theorem handler_declarationProjection_exact
    (field : DeclarationProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    handler field.externalName [stateValue control] environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  have current :
      currentStateArgument? environment (stateValue control) = some control := by
    simp [currentStateArgument?, stored, decodeStateValue?, stateValue,
      decodeAbiWith?, abiPayload?, abiValue, node]
  cases field <;>
    simp only [DeclarationProjection.value?] at projected <;>
    simp [DeclarationProjection.externalName,
      handler, finishHandler, compilePhaseQuery, ownerProjection,
      revisionProjection, headProjection, arityProjection,
      acceptedProjection, declarationsAreEmptyQuery, setCompiledFamilyDelta,
      inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
      declarationHeadProjection, inputsProjection, outputProjection,
      projectState?, encodeAbiProjection, current, projected, callValue]

/-- A declaration field call is evaluated from the generated one-variable
expression and retains the external-call receipt. -/
theorem declaration_projection_evaluation_exact
    (field : DeclarationProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    evaluate? handler
        (call field.externalName [variableExpression "state"])
        environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  have handled := handler_declarationProjection_exact field control value
    environment receipt projected stored
  exact evaluate_single_variable_call_exact handler field.externalName "state"
    (stateValue control) environment receipt _ stored handled

/-- One generated declaration-field binding is an exact authored StructuredC
declaration step. -/
theorem declaration_projection_declare_rewrite_exact
    (field : DeclarationProjection) (slotName typeName : String)
    (control : CompileLanguageControl) (value rest environment receipt : Pattern)
    (projected : field.value? control = some value)
    (storedState :
      lookup? environment (identifier "state") = some (stateValue control)) :
    rewriteAt (engineBasePremises relations) StructuredC.language 1
        (run (consStatement
          (declare slotName (namedType typeName)
            (call field.externalName [variableExpression "state"])) rest)
          environment receipt) =
      [run rest (bindName slotName value environment)
        (externalReceipt field.externalName receipt)] := by
  have evaluated := declaration_projection_evaluation_exact field control value
    environment receipt projected storedState
  have storedValue :
      store? environment (identifier slotName) value =
        some (bindName slotName value environment) := by
    simp [store?, identifierName?, bindName, identifier, node, token]
  simpa [relations, declare, node, StructuredC.a] using
    declare_rewriteAt_exact_of_evaluate handler (identifier slotName)
      (namedType typeName)
      (call field.externalName [variableExpression "state"])
      rest environment receipt value environment
      (externalReceipt field.externalName receipt)
      (bindName slotName value environment) evaluated storedValue

/-- Every generated argument-field query returns exactly the field selected
from the canonical source state. -/
theorem handler_argumentProjection_exact
    (field : ArgumentProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    handler field.externalName [stateValue control] environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  have current :
      currentStateArgument? environment (stateValue control) = some control := by
    simp [currentStateArgument?, stored, decodeStateValue?, stateValue,
      decodeAbiWith?, abiPayload?, abiValue, node]
  cases field <;>
    simp only [ArgumentProjection.value?] at projected <;>
    simp [ArgumentProjection.externalName, ArgumentProjection.value?,
      handler, finishHandler, compilePhaseQuery, ownerProjection,
      revisionProjection, headProjection, arityProjection,
      acceptedProjection, declarationsAreEmptyQuery, setCompiledFamilyDelta,
      inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
      declarationHeadProjection, inputsProjection, outputProjection,
      modesProjection, inputHeadProjection, inputTailProjection,
      projectState?, current, projected, callValue]

theorem argument_projection_evaluation_exact
    (field : ArgumentProjection) (control : CompileLanguageControl)
    (value environment receipt : Pattern)
    (projected : field.value? control = some value)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control)) :
    evaluate? handler
        (call field.externalName [variableExpression "state"])
        environment receipt =
      some ⟨.value value, environment,
        externalReceipt field.externalName receipt⟩ := by
  have handled := handler_argumentProjection_exact field control value
    environment receipt projected stored
  exact evaluate_single_variable_call_exact handler field.externalName "state"
    (stateValue control) environment receipt _ stored handled

theorem argument_projection_declare_rewrite_exact
    (field : ArgumentProjection) (slotName typeName : String)
    (control : CompileLanguageControl) (value rest environment receipt : Pattern)
    (projected : field.value? control = some value)
    (storedState :
      lookup? environment (identifier "state") = some (stateValue control)) :
    rewriteAt (engineBasePremises relations) StructuredC.language 1
        (run (consStatement
          (declare slotName (namedType typeName)
            (call field.externalName [variableExpression "state"])) rest)
          environment receipt) =
      [run rest (bindName slotName value environment)
        (externalReceipt field.externalName receipt)] := by
  have evaluated := argument_projection_evaluation_exact field control value
    environment receipt projected storedState
  have storedValue :
      store? environment (identifier slotName) value =
        some (bindName slotName value environment) := by
    simp [store?, identifierName?, bindName, identifier, node, token]
  simpa [relations, declare, node, StructuredC.a] using
    declare_rewriteAt_exact_of_evaluate handler (identifier slotName)
      (namedType typeName)
      (call field.externalName [variableExpression "state"])
      rest environment receipt value environment
      (externalReceipt field.externalName receipt)
      (bindName slotName value environment) evaluated storedValue

/-- The generated argument-cursor shape query is true exactly on the empty
cursor required by the premise-free arguments-finished row. -/
theorem arguments_cursor_empty_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining [] modes accepted))) :
    evaluate? handler
        (call inputCursorIsEmptyQuery [variableExpression "state"])
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt inputCursorIsEmptyQuery receipt⟩ := by
  have current :
      currentStateArgument? environment
          (stateValue (.arguments owner revision head arity declaration
            remaining [] modes accepted)) =
        some (.arguments owner revision head arity declaration remaining []
          modes accepted) := by
    simp [currentStateArgument?, stored, decodeStateValue?, stateValue,
      decodeAbiWith?, abiPayload?, abiValue, node]
  have handled :
      handler inputCursorIsEmptyQuery
          [stateValue (.arguments owner revision head arity declaration
            remaining [] modes accepted)] environment receipt =
        some ⟨.value trueValue, environment,
          externalReceipt inputCursorIsEmptyQuery receipt⟩ := by
    simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
      revisionProjection, headProjection, arityProjection,
      acceptedProjection, declarationsAreEmptyQuery, setCompiledFamilyDelta,
      inputCursorIsEmptyQuery, projectState?, inputCursorEmptyValue, current,
      callValue]
  exact evaluate_single_variable_call_exact handler inputCursorIsEmptyQuery
    "state"
    (stateValue (.arguments owner revision head arity declaration remaining []
      modes accepted)) environment receipt _ stored handled

/-- A visible input head makes the same structural cursor query return false;
the head itself is not inspected by this shape test. -/
theorem arguments_cursor_nonempty_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining (expected :: inputCursor) modes accepted))) :
    evaluate? handler
        (call inputCursorIsEmptyQuery [variableExpression "state"])
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt inputCursorIsEmptyQuery receipt⟩ := by
  have current :
      currentStateArgument? environment
          (stateValue (.arguments owner revision head arity declaration
            remaining (expected :: inputCursor) modes accepted)) =
        some (.arguments owner revision head arity declaration remaining
          (expected :: inputCursor) modes accepted) := by
    simp [currentStateArgument?, stored, decodeStateValue?, stateValue,
      decodeAbiWith?, abiPayload?, abiValue, node]
  have handled :
      handler inputCursorIsEmptyQuery
          [stateValue (.arguments owner revision head arity declaration
            remaining (expected :: inputCursor) modes accepted)]
          environment receipt =
        some ⟨.value falseValue, environment,
          externalReceipt inputCursorIsEmptyQuery receipt⟩ := by
    simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
      revisionProjection, headProjection, arityProjection,
      acceptedProjection, declarationsAreEmptyQuery, setCompiledFamilyDelta,
      inputCursorIsEmptyQuery, projectState?, inputCursorEmptyValue, current,
      callValue, falseValue, trueValue, valueSymbol, identifier, node, token]
  exact evaluate_single_variable_call_exact handler inputCursorIsEmptyQuery
    "state"
    (stateValue (.arguments owner revision head arity declaration remaining
      (expected :: inputCursor) modes accepted)) environment receipt _ stored
    handled

/-- Literal dispatch evaluates the selected PeTTa classifier itself.  The
answer is not read from a generated transition or expected target. -/
theorem handler_literalPredicate_exact
    (predicate : LiteralPredicate) (term : Term)
    (environment receipt : Pattern) :
    handler predicate.externalName [abiValue (encodeTerm term)]
        environment receipt =
      some ⟨.value
          (if term == predicate.term then trueValue else falseValue),
        environment, externalReceipt predicate.externalName receipt⟩ := by
  cases predicate <;>
    simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
      revisionProjection, headProjection, arityProjection, acceptedProjection,
      declarationsAreEmptyQuery, setCompiledFamilyDelta,
      inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
      declarationHeadProjection, inputsProjection, outputProjection,
      modesProjection, inputHeadProjection, inputTailProjection,
      setCompileRunningDelta, startCompileArgumentsDelta,
      appendArgumentModeDelta, setCompileResultDelta,
      appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
      LiteralPredicate.externalName, LiteralPredicate.term,
      termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
      decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue, callBool,
      callValue, node]

theorem literalPredicate_evaluation_exact
    (predicate : LiteralPredicate) (term : Term)
    (environment receipt : Pattern)
    (stored : lookup? environment (identifier "expected") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call predicate.externalName [variableExpression "expected"])
        environment receipt =
      some ⟨.value
          (if term == predicate.term then trueValue else falseValue),
        environment, externalReceipt predicate.externalName receipt⟩ := by
  exact evaluate_single_variable_call_exact handler predicate.externalName
    "expected" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_literalPredicate_exact predicate term environment receipt)

/-- The checked-input guard is derived from the independent PeTTa argument
classifier, not from the generated branch that consumes its answer. -/
def checkedInputAnswer (term : Term) : Bool :=
  match compileArgMode term with
  | some (.evalSoftcutType _) => true
  | _ => false

/-- The open-input guard holds exactly when the independent PeTTa argument
classifier has no supported mode. -/
def openInputAnswer (term : Term) : Bool :=
  (compileArgMode term).isNone

theorem handler_inputIsChecked_exact
    (term : Term) (environment receipt : Pattern) :
    handler inputIsCheckedQuery [abiValue (encodeTerm term)]
        environment receipt =
      some ⟨.value (if checkedInputAnswer term then trueValue else falseValue),
        environment, externalReceipt inputIsCheckedQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, localPredicate?, termIsAtomQuery,
    termIsUndefinedQuery, termIsHoleQuery, inputIsCheckedQuery,
    inputIsOpenQuery, nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    checkedInputAnswer, decodeTermValue?, decodeAbiWith?,
    abiPayload?, abiValue, callBool, callValue, node]

theorem handler_inputIsOpen_exact
    (term : Term) (environment receipt : Pattern) :
    handler inputIsOpenQuery [abiValue (encodeTerm term)] environment receipt =
      some ⟨.value (if openInputAnswer term then trueValue else falseValue),
        environment, externalReceipt inputIsOpenQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, localPredicate?, termIsAtomQuery,
    termIsUndefinedQuery, termIsHoleQuery, inputIsCheckedQuery,
    inputIsOpenQuery, nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    openInputAnswer, decodeTermValue?, decodeAbiWith?,
    abiPayload?, abiValue, callBool, callValue, node]

theorem inputIsChecked_evaluation_exact
    (term : Term) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "expected") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call inputIsCheckedQuery [variableExpression "expected"])
        environment receipt =
      some ⟨.value (if checkedInputAnswer term then trueValue else falseValue),
        environment, externalReceipt inputIsCheckedQuery receipt⟩ := by
  exact evaluate_single_variable_call_exact handler inputIsCheckedQuery
    "expected" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_inputIsChecked_exact term environment receipt)

theorem inputIsOpen_evaluation_exact
    (term : Term) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "expected") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call inputIsOpenQuery [variableExpression "expected"])
        environment receipt =
      some ⟨.value (if openInputAnswer term then trueValue else falseValue),
        environment, externalReceipt inputIsOpenQuery receipt⟩ := by
  exact evaluate_single_variable_call_exact handler inputIsOpenQuery
    "expected" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_inputIsOpen_exact term environment receipt)

/-- The checked-result guard is derived from the independent PeTTa result
classifier, not from the generated branch that consumes its answer. -/
def checkedResultAnswer (term : Term) : Bool :=
  match compileResultMode term with
  | some (.resultSoftcutType _) => true
  | _ => false

/-- The open-result guard holds exactly when the independent PeTTa result
classifier has no supported mode. -/
def openResultAnswer (term : Term) : Bool :=
  (compileResultMode term).isNone

theorem handler_resultIsChecked_exact
    (term : Term) (environment receipt : Pattern) :
    handler resultIsCheckedQuery [abiValue (encodeTerm term)]
        environment receipt =
      some ⟨.value (if checkedResultAnswer term then trueValue else falseValue),
        environment, externalReceipt resultIsCheckedQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, localPredicate?, termIsAtomQuery,
    termIsUndefinedQuery, termIsHoleQuery, inputIsCheckedQuery,
    inputIsOpenQuery, resultIsCheckedQuery, resultIsOpenQuery,
    nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    checkedResultAnswer, decodeTermValue?, decodeAbiWith?, abiPayload?,
    abiValue, callBool, callValue, node]

theorem handler_resultIsOpen_exact
    (term : Term) (environment receipt : Pattern) :
    handler resultIsOpenQuery [abiValue (encodeTerm term)] environment receipt =
      some ⟨.value (if openResultAnswer term then trueValue else falseValue),
        environment, externalReceipt resultIsOpenQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, localPredicate?, termIsAtomQuery,
    termIsUndefinedQuery, termIsHoleQuery, inputIsCheckedQuery,
    inputIsOpenQuery, resultIsCheckedQuery, resultIsOpenQuery,
    nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    openResultAnswer, decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue,
    callBool, callValue, node]

theorem resultIsChecked_evaluation_exact
    (term : Term) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "output") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call resultIsCheckedQuery [variableExpression "output"])
        environment receipt =
      some ⟨.value (if checkedResultAnswer term then trueValue else falseValue),
        environment, externalReceipt resultIsCheckedQuery receipt⟩ := by
  exact evaluate_single_variable_call_exact handler resultIsCheckedQuery
    "output" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_resultIsChecked_exact term environment receipt)

theorem resultIsOpen_evaluation_exact
    (term : Term) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "output") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call resultIsOpenQuery [variableExpression "output"])
        environment receipt =
      some ⟨.value (if openResultAnswer term then trueValue else falseValue),
        environment, externalReceipt resultIsOpenQuery receipt⟩ := by
  exact evaluate_single_variable_call_exact handler resultIsOpenQuery
    "output" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_resultIsOpen_exact term environment receipt)

theorem literalResultPredicate_evaluation_exact
    (predicate : LiteralPredicate) (term : Term)
    (environment receipt : Pattern)
    (stored : lookup? environment (identifier "output") =
      some (abiValue (encodeTerm term))) :
    evaluate? handler
        (call predicate.externalName [variableExpression "output"])
        environment receipt =
      some ⟨.value
          (if term == predicate.term then trueValue else falseValue),
        environment, externalReceipt predicate.externalName receipt⟩ := by
  exact evaluate_single_variable_call_exact handler predicate.externalName
    "output" (abiValue (encodeTerm term)) environment receipt _ stored
    (handler_literalPredicate_exact predicate term environment receipt)

/-- The generated exhausted-declaration query evaluates to true for every
running state whose remaining declaration row is empty. -/
theorem finish_declarations_empty_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity [] accepted))) :
    evaluate? handler
        (call declarationsAreEmptyQuery [variableExpression "state"])
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt declarationsAreEmptyQuery receipt⟩ := by
  have finishHandled := finishHandler_declarations_empty_exact owner revision
    head arity accepted environment receipt stored
  have handled := handler_of_finishHandler_exact declarationsAreEmptyQuery
    [stateValue (.running owner revision head arity [] accepted)]
    environment receipt _ finishHandled
  exact evaluate_single_variable_call_exact handler
    declarationsAreEmptyQuery "state"
    (stateValue (.running owner revision head arity [] accepted))
    environment receipt _ stored handled

/-- The generated exhausted-declaration query evaluates to false for every
running state with a visible head declaration. -/
theorem declarations_nonempty_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity
          (declaration :: remaining) accepted))) :
    evaluate? handler
        (call declarationsAreEmptyQuery [variableExpression "state"])
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt declarationsAreEmptyQuery receipt⟩ := by
  have finishHandled := finishHandler_declarations_nonempty_exact owner
    revision head arity declaration remaining accepted environment receipt
    stored
  have handled := handler_of_finishHandler_exact declarationsAreEmptyQuery
    [stateValue (.running owner revision head arity
      (declaration :: remaining) accepted)] environment receipt _
    finishHandled
  exact evaluate_single_variable_call_exact handler
    declarationsAreEmptyQuery "state"
    (stateValue (.running owner revision head arity
      (declaration :: remaining) accepted))
    environment receipt _ stored handled

/-- The generated skip-head guard computes the authored name disequality from
its two explicit ABI operands. -/
theorem handler_nameNotEqual_true_exact
    (left right : String) (environment receipt : Pattern)
    (different : left ≠ right) :
    handler nameNotEqualQuery
        [abiValue (encodeName left), abiValue (encodeName right)]
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt nameNotEqualQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta,
    appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
    termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
    nameNotEqualQuery, decodeNameValue?, decodeAbiWith?, abiPayload?,
    abiValue, callBool, callValue, different, node]

/-- The skip-head guard is evaluated from the two generated variable
expressions without re-reading or reclassifying the source transition. -/
theorem nameNotEqual_evaluation_exact
    (left right : String) (environment receipt : Pattern)
    (different : left ≠ right)
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["declaration_head", "head"]
      [abiValue (encodeName left), abiValue (encodeName right)]) :
    evaluate? handler
        (call nameNotEqualQuery
          (["declaration_head", "head"].map variableExpression))
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt nameNotEqualQuery receipt⟩ := by
  have handled := handler_nameNotEqual_true_exact left right environment
    receipt different
  exact evaluate_variable_call_exact handler nameNotEqualQuery
    ["declaration_head", "head"]
    [abiValue (encodeName left), abiValue (encodeName right)]
    environment receipt _ storedOperands handled

/-- Equal authored names make the skip-head guard false, leaving later source
rows available in their original order. -/
theorem handler_nameNotEqual_false_exact
    (name : String) (environment receipt : Pattern) :
    handler nameNotEqualQuery
        [abiValue (encodeName name), abiValue (encodeName name)]
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt nameNotEqualQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta,
    appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
    termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
    nameNotEqualQuery, decodeNameValue?, decodeAbiWith?, abiPayload?,
    abiValue, callBool, callValue, node]

theorem nameNotEqual_false_evaluation_exact
    (name : String) (environment receipt : Pattern)
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["declaration_head", "head"]
      [abiValue (encodeName name), abiValue (encodeName name)]) :
    evaluate? handler
        (call nameNotEqualQuery
          (["declaration_head", "head"].map variableExpression))
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt nameNotEqualQuery receipt⟩ := by
  have handled := handler_nameNotEqual_false_exact name environment receipt
  exact evaluate_variable_call_exact handler nameNotEqualQuery
    ["declaration_head", "head"]
    [abiValue (encodeName name), abiValue (encodeName name)]
    environment receipt _ storedOperands handled

/-- The generated skip-arity guard computes the authored length mismatch from
the explicit input row and requested arity. -/
theorem handler_arityDiffers_true_exact
    (inputs : List Term) (arity : Nat) (environment receipt : Pattern)
    (different : inputs.length ≠ arity) :
    handler arityDiffersQuery
        [abiValue (encodeTerms inputs), abiValue (encodeNat arity)]
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt arityDiffersQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta,
    appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
    termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
    nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    decodeTermsValue?, decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue,
    callBool, callValue, different, node]

theorem arityDiffers_evaluation_exact
    (inputs : List Term) (arity : Nat) (environment receipt : Pattern)
    (different : inputs.length ≠ arity)
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["inputs", "arity"]
      [abiValue (encodeTerms inputs), abiValue (encodeNat arity)]) :
    evaluate? handler
        (call arityDiffersQuery
          (["inputs", "arity"].map variableExpression))
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt arityDiffersQuery receipt⟩ := by
  have handled := handler_arityDiffers_true_exact inputs arity environment
    receipt different
  exact evaluate_variable_call_exact handler arityDiffersQuery
    ["inputs", "arity"]
    [abiValue (encodeTerms inputs), abiValue (encodeNat arity)]
    environment receipt _ storedOperands handled

/-- Equal input length makes the skip-arity guard false. -/
theorem handler_arityDiffers_false_exact
    (inputs : List Term) (environment receipt : Pattern) :
    handler arityDiffersQuery
        [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt arityDiffersQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta,
    appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
    termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
    nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    decodeTermsValue?, decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue,
    callBool, callValue, node]

theorem arityDiffers_false_evaluation_exact
    (inputs : List Term) (environment receipt : Pattern)
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["inputs", "arity"]
      [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]) :
    evaluate? handler
        (call arityDiffersQuery
          (["inputs", "arity"].map variableExpression))
        environment receipt =
      some ⟨.value falseValue, environment,
        externalReceipt arityDiffersQuery receipt⟩ := by
  have handled := handler_arityDiffers_false_exact inputs environment receipt
  exact evaluate_variable_call_exact handler arityDiffersQuery
    ["inputs", "arity"]
    [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]
    environment receipt _ storedOperands handled

/-- Equal input length makes the authored begin-declaration guard true. -/
theorem handler_arityMatches_true_exact
    (inputs : List Term) (environment receipt : Pattern) :
    handler arityMatchesQuery
        [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt arityMatchesQuery receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta,
    appendCompiledPlanDelta, setOutsideFragmentDelta, localPredicate?,
    termIsAtomQuery, termIsUndefinedQuery, termIsHoleQuery,
    nameNotEqualQuery, arityDiffersQuery, arityMatchesQuery,
    decodeTermsValue?, decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue,
    callBool, callValue, node]

theorem arityMatches_evaluation_exact
    (inputs : List Term) (environment receipt : Pattern)
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["inputs", "arity"]
      [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]) :
    evaluate? handler
        (call arityMatchesQuery
          (["inputs", "arity"].map variableExpression))
        environment receipt =
      some ⟨.value trueValue, environment,
        externalReceipt arityMatchesQuery receipt⟩ := by
  have handled := handler_arityMatches_true_exact inputs environment receipt
  exact evaluate_variable_call_exact handler arityMatchesQuery
    ["inputs", "arity"]
    [abiValue (encodeTerms inputs), abiValue (encodeNat inputs.length)]
    environment receipt _ storedOperands handled

/-- The generated skip-head delta consumes the seven explicit target fields
and updates only the persistent `state` binding. -/
theorem handler_skipHead_delta_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (different : declaration.function ≠ head)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity
          (declaration :: remaining) accepted))) :
    handler setCompileRunningDelta
        [ stateValue (.running owner revision head arity
            (declaration :: remaining) accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodePlans accepted) ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision head arity remaining accepted))
          environment,
        externalReceipt setCompileRunningDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, setCompileRunning?, currentStateArgument?, stored,
    decodeStateValue?, decodeOwnerValue?, decodeNatValue?, decodeNameValue?,
    decodeDeclarationsValue?, decodePlansValue?, decodeAbiWith?, abiPayload?,
    stateValue, abiValue, writeState, valueUnit, different, node]

/-- The skip-head delta call evaluates from the generated seven-variable
operand row to the exact source-machine successor. -/
theorem skipHead_delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (different : declaration.function ≠ head)
    (storedState :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity
          (declaration :: remaining) accepted)))
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "remaining",
        "accepted"]
      [ stateValue (.running owner revision head arity
          (declaration :: remaining) accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName head)
      , abiValue (encodeNat arity)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodePlans accepted) ]) :
    evaluate? handler
        (call setCompileRunningDelta
          (["state", "owner", "revision", "head", "arity", "remaining",
            "accepted"].map variableExpression))
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision head arity remaining accepted))
          environment,
        externalReceipt setCompileRunningDelta receipt⟩ := by
  have handled := handler_skipHead_delta_exact owner revision head arity
    declaration remaining accepted environment receipt different storedState
  exact evaluate_variable_call_exact handler setCompileRunningDelta
    ["state", "owner", "revision", "head", "arity", "remaining", "accepted"]
    [ stateValue (.running owner revision head arity
        (declaration :: remaining) accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodePlans accepted) ]
    environment receipt _ storedOperands handled

/-- The generated skip-arity delta is admitted exactly when the current
declaration owns the requested head and has a different input arity. -/
theorem handler_skipArity_delta_exact
    (owner : SpaceOwner) (revision : Nat) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (different : declaration.inputTypes.length ≠ arity)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision declaration.function arity
          (declaration :: remaining) accepted))) :
    handler setCompileRunningDelta
        [ stateValue (.running owner revision declaration.function arity
            (declaration :: remaining) accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeNat arity)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodePlans accepted) ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision declaration.function arity
            remaining accepted)) environment,
        externalReceipt setCompileRunningDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, setCompileRunning?, currentStateArgument?, stored,
    decodeStateValue?, decodeOwnerValue?, decodeNatValue?, decodeNameValue?,
    decodeDeclarationsValue?, decodePlansValue?, decodeAbiWith?, abiPayload?,
    stateValue, abiValue, writeState, valueUnit, different, node]

theorem skipArity_delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (different : declaration.inputTypes.length ≠ arity)
    (storedState :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision declaration.function arity
          (declaration :: remaining) accepted)))
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["state", "owner", "revision", "declaration_head", "arity",
        "remaining", "accepted"]
      [ stateValue (.running owner revision declaration.function arity
          (declaration :: remaining) accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName declaration.function)
      , abiValue (encodeNat arity)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodePlans accepted) ]) :
    evaluate? handler
        (call setCompileRunningDelta
          (["state", "owner", "revision", "declaration_head", "arity",
            "remaining", "accepted"].map variableExpression))
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision declaration.function arity
            remaining accepted)) environment,
        externalReceipt setCompileRunningDelta receipt⟩ := by
  have handled := handler_skipArity_delta_exact owner revision arity
    declaration remaining accepted environment receipt different storedState
  exact evaluate_variable_call_exact handler setCompileRunningDelta
    ["state", "owner", "revision", "declaration_head", "arity", "remaining",
      "accepted"]
    [ stateValue (.running owner revision declaration.function arity
        (declaration :: remaining) accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName declaration.function)
    , abiValue (encodeNat arity)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodePlans accepted) ] environment receipt _ storedOperands
    handled

/-- The generated begin-declaration delta reconstructs the exact declaration,
copies its input row into the argument cursor, and initializes the accumulated
mode row to empty. -/
theorem handler_beginDeclaration_delta_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision declaration.function
          declaration.inputTypes.length (declaration :: remaining)
          accepted))) :
    handler startCompileArgumentsDelta
        [ stateValue (.running owner revision declaration.function
            declaration.inputTypes.length (declaration :: remaining) accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeNat declaration.inputTypes.length)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , abiValue (encodeTerm declaration.outputType)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodeTerms declaration.inputTypes)
        , abiValue (encodePlans accepted) ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.arguments owner revision declaration.function
            declaration.inputTypes.length declaration remaining
            declaration.inputTypes [] accepted)) environment,
        externalReceipt startCompileArgumentsDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    startCompileArguments?, currentStateArgument?, stored, decodeStateValue?,
    decodeOwnerValue?, decodeNatValue?, decodeNameValue?, decodeTermsValue?,
    decodeTermValue?, decodeDeclarationsValue?, decodePlansValue?,
    decodeAbiWith?, abiPayload?, stateValue, abiValue,
    writeState, valueUnit, node]

theorem beginDeclaration_delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (declaration : ArrowDeclaration)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (storedState :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision declaration.function
          declaration.inputTypes.length (declaration :: remaining) accepted)))
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["state", "owner", "revision", "declaration_head", "arity",
        "occurrence", "declaration_head", "inputs", "output", "remaining",
        "inputs", "accepted"]
      [ stateValue (.running owner revision declaration.function
          declaration.inputTypes.length (declaration :: remaining) accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName declaration.function)
      , abiValue (encodeNat declaration.inputTypes.length)
      , abiValue (encodeNat declaration.occurrence)
      , abiValue (encodeName declaration.function)
      , abiValue (encodeTerms declaration.inputTypes)
      , abiValue (encodeTerm declaration.outputType)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodeTerms declaration.inputTypes)
      , abiValue (encodePlans accepted) ]) :
    evaluate? handler
        (call startCompileArgumentsDelta
          (["state", "owner", "revision", "declaration_head", "arity",
            "occurrence", "declaration_head", "inputs", "output",
            "remaining", "inputs", "accepted"].map variableExpression))
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.arguments owner revision declaration.function
            declaration.inputTypes.length declaration remaining
            declaration.inputTypes [] accepted)) environment,
        externalReceipt startCompileArgumentsDelta receipt⟩ := by
  have handled := handler_beginDeclaration_delta_exact owner revision
    declaration remaining accepted environment receipt storedState
  exact evaluate_variable_call_exact handler startCompileArgumentsDelta
    ["state", "owner", "revision", "declaration_head", "arity", "occurrence",
      "declaration_head", "inputs", "output", "remaining", "inputs",
      "accepted"]
    [ stateValue (.running owner revision declaration.function
        declaration.inputTypes.length (declaration :: remaining) accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName declaration.function)
    , abiValue (encodeNat declaration.inputTypes.length)
    , abiValue (encodeNat declaration.occurrence)
    , abiValue (encodeName declaration.function)
    , abiValue (encodeTerms declaration.inputTypes)
    , abiValue (encodeTerm declaration.outputType)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodeTerms declaration.inputTypes)
    , abiValue (encodePlans accepted) ] environment receipt _ storedOperands
    handled

/-- The premise-free arguments-finished delta preserves every authored field
and moves only from an empty argument cursor into result compilation. -/
theorem handler_argumentsFinished_delta_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining [] modes accepted))) :
    handler setCompileResultDelta
        [ stateValue (.arguments owner revision head arity declaration
            remaining [] modes accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , abiValue (encodeTerm declaration.outputType)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodeArgModes modes)
        , abiValue (encodePlans accepted) ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.result owner revision head arity declaration remaining
            modes accepted)) environment,
        externalReceipt setCompileResultDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, setCompileResult?,
    currentStateArgument?, stored, decodeStateValue?, decodeOwnerValue?,
    decodeNatValue?, decodeNameValue?, decodeTermsValue?, decodeTermValue?,
    decodeDeclarationsValue?, decodeArgModesValue?, decodePlansValue?,
    decodeAbiWith?, abiPayload?, stateValue, abiValue, writeState, valueUnit,
    node]

theorem argumentsFinished_delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (storedState :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining [] modes accepted)))
    (storedOperands : List.Forall₂
      (fun slot value => lookup? environment (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "occurrence",
        "declaration_head", "inputs", "output", "remaining", "modes",
        "accepted"]
      [ stateValue (.arguments owner revision head arity declaration remaining
          [] modes accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName head)
      , abiValue (encodeNat arity)
      , abiValue (encodeNat declaration.occurrence)
      , abiValue (encodeName declaration.function)
      , abiValue (encodeTerms declaration.inputTypes)
      , abiValue (encodeTerm declaration.outputType)
      , abiValue (encodeDeclarations remaining)
      , abiValue (encodeArgModes modes)
      , abiValue (encodePlans accepted) ]) :
    evaluate? handler
        (call setCompileResultDelta
          (["state", "owner", "revision", "head", "arity", "occurrence",
            "declaration_head", "inputs", "output", "remaining", "modes",
            "accepted"].map variableExpression))
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.result owner revision head arity declaration remaining
            modes accepted)) environment,
        externalReceipt setCompileResultDelta receipt⟩ := by
  have handled := handler_argumentsFinished_delta_exact owner revision head
    arity declaration remaining modes accepted environment receipt storedState
  exact evaluate_variable_call_exact handler setCompileResultDelta
    ["state", "owner", "revision", "head", "arity", "occurrence",
      "declaration_head", "inputs", "output", "remaining", "modes",
      "accepted"]
    [ stateValue (.arguments owner revision head arity declaration remaining []
        modes accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodeNat declaration.occurrence)
    , abiValue (encodeName declaration.function)
    , abiValue (encodeTerms declaration.inputTypes)
    , abiValue (encodeTerm declaration.outputType)
    , abiValue (encodeDeclarations remaining)
    , abiValue (encodeArgModes modes)
    , abiValue (encodePlans accepted) ] environment receipt _ storedOperands
    handled

private theorem appendArgumentMode?_canonical_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (mode : ArgMode)
    (environment receipt : Pattern)
    (classified : compileArgMode expected = some mode)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining (expected :: inputCursor) modes accepted))) :
    appendArgumentMode?
        [ stateValue (.arguments owner revision head arity declaration
            remaining (expected :: inputCursor) modes accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , abiValue (encodeTerm declaration.outputType)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodeTerms inputCursor)
        , abiValue (encodeArgModes modes)
        , abiValue (encodePlans accepted)
        , argumentModeTag mode
        , argumentModePayload mode ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.arguments owner revision head arity declaration
            remaining inputCursor (modes ++ [mode]) accepted)) environment,
        externalReceipt appendArgumentModeDelta receipt⟩ := by
  rcases declaration with ⟨occurrence, declarationHead, inputs, output⟩
  have current :
      currentStateArgument? environment
          (stateValue (.arguments owner revision head arity
            ⟨occurrence, declarationHead, inputs, output⟩ remaining
            (expected :: inputCursor) modes accepted)) =
        some (.arguments owner revision head arity
          ⟨occurrence, declarationHead, inputs, output⟩ remaining
          (expected :: inputCursor) modes accepted) := by
    simp [currentStateArgument?, stored, decodeStateValue?, stateValue,
      decodeAbiWith?, abiPayload?, abiValue, node]
  have ownerDecoded : decodeOwnerValue? (abiValue (encodeOwner owner)) =
      some owner := by
    simp [decodeOwnerValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have revisionDecoded : decodeNatValue? (abiValue (encodeNat revision)) =
      some revision := by
    simp [decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have headDecoded : decodeNameValue? (abiValue (encodeName head)) =
      some head := by
    simp [decodeNameValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have arityDecoded : decodeNatValue? (abiValue (encodeNat arity)) =
      some arity := by
    simp [decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have occurrenceDecoded :
      decodeNatValue? (abiValue (encodeNat occurrence)) = some occurrence := by
    simp [decodeNatValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have declarationHeadDecoded :
      decodeNameValue? (abiValue (encodeName declarationHead)) =
        some declarationHead := by
    simp [decodeNameValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have inputsDecoded : decodeTermsValue? (abiValue (encodeTerms inputs)) =
      some inputs := by
    simp [decodeTermsValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have outputDecoded : decodeTermValue? (abiValue (encodeTerm output)) =
      some output := by
    simp [decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have remainingDecoded :
      decodeDeclarationsValue? (abiValue (encodeDeclarations remaining)) =
        some remaining := by
    simp [decodeDeclarationsValue?, decodeAbiWith?, abiPayload?, abiValue,
      node]
  have cursorDecoded :
      decodeTermsValue? (abiValue (encodeTerms inputCursor)) =
        some inputCursor := by
    simp [decodeTermsValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have modesDecoded : decodeArgModesValue? (abiValue (encodeArgModes modes)) =
      some modes := by
    simp [decodeArgModesValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have acceptedDecoded : decodePlansValue? (abiValue (encodePlans accepted)) =
      some accepted := by
    simp [decodePlansValue?, decodeAbiWith?, abiPayload?, abiValue, node]
  have modeDecoded :
      decodeArgumentModeOperands? (argumentModeTag mode)
          (argumentModePayload mode) = some mode := by
    cases mode <;>
      simp [decodeArgumentModeOperands?, argumentModeTag, argumentModePayload,
        rawArgumentMode, uncheckedArgumentMode, checkedArgumentMode,
        noModePayload, decodeTermValue?, decodeAbiWith?, abiPayload?, abiValue,
        valueSymbol, identifier, node, token]
  simp [appendArgumentMode?, current, ownerDecoded, revisionDecoded,
    headDecoded, arityDecoded, occurrenceDecoded, declarationHeadDecoded,
    inputsDecoded, outputDecoded, remainingDecoded, cursorDecoded,
    modesDecoded, acceptedDecoded, modeDecoded, classified, writeState]

/-- The argument-mode delta reconstructs all supplied source fields, checks
the independent PeTTa classifier, consumes exactly one cursor head, and appends
exactly one canonical mode. -/
theorem handler_appendArgumentMode_delta_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (mode : ArgMode)
    (environment receipt : Pattern)
    (classified : compileArgMode expected = some mode)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining (expected :: inputCursor) modes accepted))) :
    handler appendArgumentModeDelta
        [ stateValue (.arguments owner revision head arity declaration
            remaining (expected :: inputCursor) modes accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , abiValue (encodeTerm declaration.outputType)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodeTerms inputCursor)
        , abiValue (encodeArgModes modes)
        , abiValue (encodePlans accepted)
        , argumentModeTag mode
        , argumentModePayload mode ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.arguments owner revision head arity declaration
            remaining inputCursor (modes ++ [mode]) accepted)) environment,
        externalReceipt appendArgumentModeDelta receipt⟩ := by
  have appended := appendArgumentMode?_canonical_exact owner revision head
    arity declaration remaining expected inputCursor modes accepted mode
    environment receipt classified stored
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, appended]

private theorem appendCompiledPlan?_canonical_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (resultMode : ResultMode) (environment receipt : Pattern)
    (classified : compileResultMode declaration.outputType = some resultMode)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.result owner revision head arity declaration
          remaining modes accepted))) :
    appendCompiledPlan?
        [ stateValue (.result owner revision head arity declaration remaining
            modes accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodePlans accepted)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeArgModes modes)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , resultOutputValue declaration.outputType
        , resultModeTag resultMode
        , resultModePayload resultMode ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := resultMode
              declaration := declaration }]))) environment,
        externalReceipt appendCompiledPlanDelta receipt⟩ := by
  rcases declaration with ⟨occurrence, declarationHead, inputs, output⟩
  simp [appendCompiledPlan?, currentStateArgument?, stored, decodeStateValue?,
    decodeOwnerValue?, decodeNatValue?, decodeNameValue?,
    decodeDeclarationsValue?, decodePlansValue?, decodeArgModesValue?,
    decodeTermsValue?, decodeResultOutputValue_exact,
    decodeResultModeOperands_exact, decodeAbiWith?, abiPayload?, stateValue,
    abiValue, classified, writeState, valueUnit, node]

/-- The result-plan delta reconstructs every supplied source field, checks the
independent PeTTa result classifier, constructs the exact guard plan, and
appends that plan before returning to the running phase. -/
theorem handler_appendCompiledPlan_delta_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (resultMode : ResultMode) (environment receipt : Pattern)
    (classified : compileResultMode declaration.outputType = some resultMode)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.result owner revision head arity declaration
          remaining modes accepted))) :
    handler appendCompiledPlanDelta
        [ stateValue (.result owner revision head arity declaration remaining
            modes accepted)
        , abiValue (encodeOwner owner)
        , abiValue (encodeNat revision)
        , abiValue (encodeName head)
        , abiValue (encodeNat arity)
        , abiValue (encodeDeclarations remaining)
        , abiValue (encodePlans accepted)
        , abiValue (encodeNat declaration.occurrence)
        , abiValue (encodeArgModes modes)
        , abiValue (encodeName declaration.function)
        , abiValue (encodeTerms declaration.inputTypes)
        , resultOutputValue declaration.outputType
        , resultModeTag resultMode
        , resultModePayload resultMode ] environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue (.running owner revision head arity remaining
            (accepted ++ [{
              declarationOccurrence := declaration.occurrence
              argumentModes := modes
              resultMode := resultMode
              declaration := declaration }]))) environment,
        externalReceipt appendCompiledPlanDelta receipt⟩ := by
  have appended := appendCompiledPlan?_canonical_exact owner revision head
    arity declaration remaining modes accepted resultMode environment receipt
    classified stored
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    appended]

/-- The outside-fragment delta is enabled only by the independently computed
absence of an argument mode.  It changes exactly the stored compiler state and
does not obtain an outcome from the generated branch that calls it. -/
theorem handler_setOutsideFragment_arguments_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (expected : Term) (inputCursor : List Term) (modes : List ArgMode)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (unsupported : compileArgMode expected = none)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.arguments owner revision head arity declaration
          remaining (expected :: inputCursor) modes accepted))) :
    handler setOutsideFragmentDelta
        [stateValue (.arguments owner revision head arity declaration remaining
          (expected :: inputCursor) modes accepted)] environment receipt =
      some ⟨.value valueUnit,
        bindName "state" (stateValue (.halted .outsideFragment)) environment,
        externalReceipt setOutsideFragmentDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, setOutsideFragment?, currentStateArgument?, stored,
    decodeStateValue?, decodeAbiWith?, abiPayload?, stateValue, abiValue,
    unsupported, writeState, valueUnit, node]

/-- The same fixed outside-fragment delta handles unsupported result terms,
but only while the stored compiler is in the exact result state and the
independent result classifier returns no mode. -/
theorem handler_setOutsideFragment_result_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (modes : List ArgMode) (accepted : List GuardPlan)
    (environment receipt : Pattern)
    (unsupported : compileResultMode declaration.outputType = none)
    (stored :
      lookup? environment (identifier "state") =
        some (stateValue (.result owner revision head arity declaration
          remaining modes accepted))) :
    handler setOutsideFragmentDelta
        [stateValue (.result owner revision head arity declaration remaining
          modes accepted)] environment receipt =
      some ⟨.value valueUnit,
        bindName "state" (stateValue (.halted .outsideFragment)) environment,
        externalReceipt setOutsideFragmentDelta receipt⟩ := by
  simp [handler, finishHandler, compilePhaseQuery, ownerProjection,
    revisionProjection, headProjection, arityProjection, acceptedProjection,
    declarationsAreEmptyQuery, setCompiledFamilyDelta,
    inputCursorIsEmptyQuery, remainingProjection, occurrenceProjection,
    declarationHeadProjection, inputsProjection, outputProjection,
    modesProjection, inputHeadProjection, inputTailProjection,
    setCompileRunningDelta, startCompileArgumentsDelta,
    appendArgumentModeDelta, setCompileResultDelta, appendCompiledPlanDelta,
    setOutsideFragmentDelta, setOutsideFragment?, currentStateArgument?, stored,
    decodeStateValue?, decodeAbiWith?, abiPayload?, stateValue, abiValue,
    unsupported, writeState, valueUnit, node]

/-- The generated finish call evaluates from its six exact variable operands
to the explicit compiled-family state update. -/
theorem finish_delta_evaluation_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (environment receipt : Pattern)
    (storedState :
      lookup? environment (identifier "state") =
        some (stateValue (.running owner revision head arity [] accepted)))
    (storedOperands : List.Forall₂
      (fun slot value =>
        lookup? environment (identifier slot) = some value)
      ["state", "owner", "revision", "head", "arity", "accepted"]
      [ stateValue (.running owner revision head arity [] accepted)
      , abiValue (encodeOwner owner)
      , abiValue (encodeNat revision)
      , abiValue (encodeName head)
      , abiValue (encodeNat arity)
      , abiValue (encodePlans accepted) ]) :
    evaluate? handler
        (call setCompiledFamilyDelta
          (["state", "owner", "revision", "head", "arity", "accepted"].map
            variableExpression))
        environment receipt =
      some ⟨.value valueUnit,
        bindName "state"
          (stateValue
            (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩)))
          environment,
        externalReceipt setCompiledFamilyDelta receipt⟩ := by
  have finishHandled := finishHandler_finishDelta_exact owner revision head
    arity accepted environment receipt storedState
  have handled := handler_of_finishHandler_exact setCompiledFamilyDelta
    [ stateValue (.running owner revision head arity [] accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodePlans accepted) ] environment receipt _ finishHandled
  exact evaluate_variable_call_exact handler setCompiledFamilyDelta
    ["state", "owner", "revision", "head", "arity", "accepted"]
    [ stateValue (.running owner revision head arity [] accepted)
    , abiValue (encodeOwner owner)
    , abiValue (encodeNat revision)
    , abiValue (encodeName head)
    , abiValue (encodeNat arity)
    , abiValue (encodePlans accepted) ] environment receipt _ storedOperands
    handled

/-- The generated outer dispatcher takes exactly one authored switch step.
The selected phase body is computed by structural case selection rather than
by a source-family oracle. -/
theorem phase_switch_rewrite_exact
    (control : CompileLanguageControl) (selected environment receipt : Pattern)
    (stored :
      lookup? environment (identifier "state") = some (stateValue control))
    (selectedExact :
      selectCase? (phaseValue control) generatedFaultBody
          generatedPhaseCases = some selected) :
    rewriteAt (engineBasePremises relations) StructuredC.language 1
        (run generatedColdBody environment receipt) =
      [run (StructuredC.appendStatements selected (statements [])) environment
        (externalReceipt compilePhaseQuery receipt)] := by
  have evaluated := phase_evaluation_exact control environment receipt stored
  rw [generatedColdBody_shape]
  simpa [relations, statements, node, StructuredC.a,
    StructuredC.consStatement] using
    switch_rewriteAt_exact_of_evaluate handler
      (call compilePhaseQuery [variableExpression "state"])
      generatedPhaseCases generatedFaultBody (statements [])
      environment receipt (phaseValue control) environment
      (externalReceipt compilePhaseQuery receipt) selected evaluated
      selectedExact

abbrev terminalNext? (control : CompileLanguageControl) :
    Option CompileLanguageControl :=
  terminalControl?
    (normalizeFirstUsing relations StructuredC.language 1 64
      (runControl control))

/-! ## One source-derived discriminator for every cold family -/

private def owner : SpaceOwner := ⟨3⟩

private def declaration
    (occurrence : Nat) (function : String) (inputs : List Term)
    (output : Term) : ArrowDeclaration :=
  ⟨occurrence, function, inputs, output⟩

private def closedChecked : Term := .list []
private def openExpected : Term := .variable "T"

private def finishSource : CompileLanguageControl :=
  .running owner 7 "f" 0 [] []

private def skipHeadSource : CompileLanguageControl :=
  .running owner 7 "f" 0 [declaration 0 "g" [] atomType] []

private def skipAritySource : CompileLanguageControl :=
  .running owner 7 "f" 0
    [declaration 1 "f" [atomType] undefinedType] []

private def beginDeclarationSource : CompileLanguageControl :=
  .running owner 7 "f" 1
    [declaration 2 "f" [atomType] undefinedType] []

private def argumentsFinishedSource : CompileLanguageControl :=
  .arguments owner 7 "f" 0 (declaration 3 "f" [] undefinedType)
    [] [] [] []

private def inputSource (expected : Term) : CompileLanguageControl :=
  .arguments owner 7 "f" 1 (declaration 4 "f" [expected] undefinedType)
    [] [expected] [] []

private def resultSource (output : Term) : CompileLanguageControl :=
  .result owner 7 "f" 0 (declaration 5 "f" [] output) [] [] []

def familySources : List CompileLanguageControl := [
  finishSource,
  skipHeadSource,
  skipAritySource,
  beginDeclarationSource,
  argumentsFinishedSource,
  inputSource atomType,
  inputSource undefinedType,
  inputSource holeType,
  inputSource closedChecked,
  inputSource openExpected,
  resultSource undefinedType,
  resultSource holeType,
  resultSource atomType,
  resultSource closedChecked,
  resultSource openExpected]

theorem familySources_cover_all_fifteen : familySources.length = 15 := by
  rfl

/-- Each independently executed generated target route has exactly the source
machine successor for its corresponding authored family. -/
theorem family_execution_matrix_exact :
    familySources.map terminalNext? =
      familySources.map compileLanguageStep? := by
  decide +kernel

theorem family_execution_matrix_all_terminate :
    (familySources.map terminalNext?).all Option.isSome = true := by
  decide +kernel

/-- A mutation of one explicit operand is rejected by the structural delta. -/
theorem append_mode_rejects_wrong_tail :
    appendArgumentMode?
      [ stateValue (inputSource atomType), abiValue (encodeOwner owner),
        abiValue (encodeNat 7), abiValue (encodeName "f"),
        abiValue (encodeNat 1), abiValue (encodeNat 4),
        abiValue (encodeName "f"), abiValue (encodeTerms [atomType]),
        abiValue (encodeTerm undefinedType), abiValue (encodeDeclarations []),
        abiValue (encodeTerms [atomType]), abiValue (encodeArgModes []),
        abiValue (encodePlans []), valueSymbol rawArgumentMode,
        valueSymbol noModePayload ]
      (initialEnvironment (inputSource atomType)) readyReceipt = none := by
  decide +kernel

#print axioms family_execution_matrix_exact
#print axioms family_execution_matrix_all_terminate
#print axioms append_mode_rejects_wrong_tail

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
