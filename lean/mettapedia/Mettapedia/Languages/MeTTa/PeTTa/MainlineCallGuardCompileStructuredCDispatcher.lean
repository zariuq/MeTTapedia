import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

/-!
# Ordered StructuredC dispatcher for the cold call-guard compiler

The source schedule consists of three contiguous pattern families:

1. running-state rows;
2. argument-state rows;
3. result-state rows.

This module assembles the fifteen authenticated matched-row bodies into that
same order.  Structural state inspection is exposed as narrow phase, shape,
literal, and projection calls.  Branching remains visible StructuredC syntax;
no external call selects a source row or a semantic result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

def noTransitionOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_NO_TRANSITION_V1"

def terminalOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_TERMINAL_V1"

def engineFaultOutcome : String :=
  "CETTA_PETTA_CALL_GUARD_ENGINE_FAULT_V1"

def runningPhase : String :=
  "CETTA_PETTA_CALL_GUARD_COMPILE_RUNNING_V1"

def argumentsPhase : String :=
  "CETTA_PETTA_CALL_GUARD_COMPILE_ARGUMENTS_V1"

def resultPhase : String :=
  "CETTA_PETTA_CALL_GUARD_COMPILE_RESULT_V1"

def haltedPhase : String :=
  "CETTA_PETTA_CALL_GUARD_COMPILE_HALTED_V1"

/-- Exact outer constructor projection for a cold compiler state. -/
def compilePhaseQuery : String :=
  "cetta_petta_call_guard_compile_phase_v1"

/-- Exact list-shape observation for `compileRunning`. -/
def declarationsAreEmptyQuery : String :=
  "cetta_petta_call_guard_declarations_are_empty_v1"

/-- Exact list-shape observation for `compileArguments`. -/
def inputCursorIsEmptyQuery : String :=
  "cetta_petta_call_guard_input_cursor_is_empty_v1"

def termIsAtomQuery : String :=
  "cetta_petta_call_guard_term_is_atom_v1"

def termIsUndefinedQuery : String :=
  "cetta_petta_call_guard_term_is_undefined_v1"

def termIsHoleQuery : String :=
  "cetta_petta_call_guard_term_is_hole_v1"

def ownerProjection : String :=
  "cetta_petta_call_guard_state_owner_v1"

def revisionProjection : String :=
  "cetta_petta_call_guard_state_revision_v1"

def headProjection : String :=
  "cetta_petta_call_guard_state_head_v1"

def arityProjection : String :=
  "cetta_petta_call_guard_state_arity_v1"

def acceptedProjection : String :=
  "cetta_petta_call_guard_state_accepted_v1"

def remainingProjection : String :=
  "cetta_petta_call_guard_state_remaining_v1"

def occurrenceProjection : String :=
  "cetta_petta_call_guard_state_occurrence_v1"

def declarationHeadProjection : String :=
  "cetta_petta_call_guard_state_declaration_head_v1"

def inputsProjection : String :=
  "cetta_petta_call_guard_state_inputs_v1"

def outputProjection : String :=
  "cetta_petta_call_guard_state_output_v1"

def modesProjection : String :=
  "cetta_petta_call_guard_state_modes_v1"

def inputHeadProjection : String :=
  "cetta_petta_call_guard_state_input_head_v1"

def inputTailProjection : String :=
  "cetta_petta_call_guard_state_input_tail_v1"

/-- The canonical operand row for queries that inspect the current cold
compiler state. -/
def stateArgument : List Pattern :=
  [variableExpression "state"]

/-- One visible StructuredC declaration that binds a structural state
projection. -/
def bindProjection (name typeName projection : String) : Pattern :=
  declare name (namedType typeName) (call projection stateArgument)

/-- The ordered field bindings shared by every nonterminal phase. -/
def commonBindings : Pattern :=
  statements [
    bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection,
    bindProjection "revision" "CettaPeTTaCallGuardNatV1" revisionProjection,
    bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection,
    bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection,
    bindProjection "accepted" "CettaPeTTaCallGuardPlansV1"
      acceptedProjection]

/-- The ordered bindings that expose the current authored declaration. -/
def declarationBindings : Pattern :=
  statements [
    bindProjection "remaining" "CettaPeTTaCallGuardDeclarationsV1"
      remainingProjection,
    bindProjection "occurrence" "CettaPeTTaCallGuardNatV1"
      occurrenceProjection,
    bindProjection "declaration_head" "CettaPeTTaCallGuardNameV1"
      declarationHeadProjection,
    bindProjection "inputs" "CettaPeTTaCallGuardTermsV1" inputsProjection,
    bindProjection "output" "CettaPeTTaCallGuardTermV1" outputProjection]

/-- The accumulated argument-mode binding. -/
def modesBinding : Pattern :=
  statements [bindProjection "modes" "CettaPeTTaCallGuardArgModesV1"
    modesProjection]

/-- The current argument and remaining input-cursor bindings. -/
def inputBindings : Pattern :=
  statements [
    bindProjection "expected" "CettaPeTTaCallGuardTermV1"
      inputHeadProjection,
    bindProjection "input_cursor" "CettaPeTTaCallGuardTermsV1"
      inputTailProjection]

/-- Splice a generated statement block in front of its continuation.  Concrete
`nil`, `cons`, and nested `append` spines are normalized to one cons list.  An
opaque block retains an explicit runtime append.  This guarantees that every
branch assembled solely from generated blocks is immediately reducible by the
authored StructuredC rules. -/
def spliceStatements : Pattern → Pattern → Pattern
  | .apply "structured-c:statements-nil" [], continuation => continuation
  | .apply "structured-c:statements-cons" [statement, rest], continuation =>
      node "structured-c:statements-cons"
        [statement, spliceStatements rest continuation]
  | .apply "structured-c:statements-append" [first, second], continuation =>
      spliceStatements first (spliceStatements second continuation)
  | block, continuation => appendStatements block continuation

/-- Sequential composition of already sorted `Statements` blocks. -/
def sequence : List Pattern → Pattern
  | [] => statements []
  | one :: rest => spliceStatements one (sequence rest)

/-- A generated terminal outcome block. -/
def outcomeBody (outcome : String) : Pattern :=
  statements [returnSymbol outcome]

/-- Preserve the first four source rows exactly: finish, skip-head,
skip-arity, then begin-declaration. -/
def runningDispatcher (finish skipHead skipArity beginDeclaration : Pattern) :
    Pattern :=
  sequence [
    commonBindings,
    statements [ifThenElse
      (call declarationsAreEmptyQuery stateArgument)
      finish
      (sequence [
        declarationBindings,
        skipHead,
        skipArity,
        beginDeclaration,
        outcomeBody noTransitionOutcome])]]

/-- Ordered literal-input discrimination used inside the argument phase. -/
def literalInputDispatcher
    (raw undefined hole checked openCase : Pattern) :
    Pattern :=
  statements [ifThenElse
    (call termIsAtomQuery [variableExpression "expected"])
    raw
    (statements [ifThenElse
      (call termIsUndefinedQuery [variableExpression "expected"])
      undefined
      (statements [ifThenElse
        (call termIsHoleQuery [variableExpression "expected"])
        hole
        (sequence [checked, openCase, outcomeBody noTransitionOutcome])])])]

/-- Preserve the six argument rows exactly: empty cursor, three literal rows,
checked input, then open input. -/
def argumentsDispatcher
    (finished raw undefined hole checked openCase : Pattern) :
    Pattern :=
  sequence [
    commonBindings,
    declarationBindings,
    modesBinding,
    statements [ifThenElse
      (call inputCursorIsEmptyQuery stateArgument)
      finished
      (sequence [inputBindings,
        literalInputDispatcher raw undefined hole checked openCase])]]

/-- Ordered literal-result discrimination used inside the result phase. -/
def literalResultDispatcher
    (undefined hole atom checked openCase : Pattern) : Pattern :=
  statements [ifThenElse
    (call termIsUndefinedQuery [variableExpression "output"])
    undefined
    (statements [ifThenElse
      (call termIsHoleQuery [variableExpression "output"])
      hole
      (statements [ifThenElse
        (call termIsAtomQuery [variableExpression "output"])
        atom
        (sequence [checked, openCase, outcomeBody noTransitionOutcome])])])]

/-- Preserve the final five source rows exactly: three literal results,
checked result, then open result. -/
def resultDispatcher
    (undefined hole atom checked openCase : Pattern) : Pattern :=
  sequence [commonBindings, declarationBindings, modesBinding,
    literalResultDispatcher undefined hole atom checked openCase]

/-- Assemble a dispatcher only from the exact fifteen-position target
inventory.  Each argument position remains load-bearing in the resulting AST. -/
def assembleDispatcherBody? : List Pattern → Option Pattern
  | [ finish, skipHead, skipArity, beginDeclaration, argumentsFinished
    , rawInput, undefinedInput, holeInput, checkedInput, openInput
    , undefinedResult, holeResult, atomResult, checkedResult, openResult ] =>
      some (statements [switch
        (call compilePhaseQuery stateArgument)
        [ caseBranch (valueSymbol runningPhase)
            (runningDispatcher finish skipHead skipArity beginDeclaration)
        , caseBranch (valueSymbol argumentsPhase)
            (argumentsDispatcher argumentsFinished rawInput undefinedInput
              holeInput checkedInput openInput)
        , caseBranch (valueSymbol resultPhase)
            (resultDispatcher undefinedResult holeResult atomResult
              checkedResult openResult)
        , caseBranch (valueSymbol haltedPhase) (outcomeBody terminalOutcome) ]
        (outcomeBody engineFaultOutcome)])
  | _ => none

def generatedFunctionName : String :=
  "cetta_generated_petta_call_guard_compile_transition_v1"

def assembleFunction? (bodies : List Pattern) : Option Pattern := do
  let body ← assembleDispatcherBody? bodies
  pure (function generatedFunctionName
    (namedType "CettaPeTTaCallGuardTransitionOutcomeV1")
    [parameter "state"
      (namedPointerType "CettaPeTTaCallGuardCompileStateV1")]
    body)

/-- Complete source-to-target construction for the cold dispatcher. -/
def lowerDecodedColdFunction? (source : LanguageDef) : Option Pattern := do
  let bodies ← lowerDecodedLanguage? source
  assembleFunction? bodies

/-- The executable statement body selected by the exact fifteen-row source
inventory.  Operational semantics runs this value directly; it is not
recovered by parsing the enclosing function after generation. -/
def generatedColdBody : Pattern :=
  (assembleDispatcherBody? allMatchedFamilyBodies).getD
    (node "structured-c:unreachable-cold-body")

/-- The fallthrough after the final running-state source row. -/
def generatedRunningAfterBeginDeclaration : Pattern :=
  outcomeBody noTransitionOutcome

/-- The ordered rows that remain if the skip-arity premise is false. -/
def generatedRunningAfterSkipArity : Pattern :=
  sequence [beginDeclarationBody, generatedRunningAfterBeginDeclaration]

/-- The ordered rows that remain if the skip-head premise is false. -/
def generatedRunningAfterSkipHead : Pattern :=
  sequence [skipArityBody, generatedRunningAfterSkipArity]

/-- The ordered nonempty-declaration continuation of the generated running
dispatcher. -/
def generatedRunningFallback : Pattern :=
  sequence [declarationBindings, skipHeadBody,
    generatedRunningAfterSkipHead]

/-- The exact generated decision following the five common state
projections. -/
def generatedRunningDecision : Pattern :=
  ifThenElse (call declarationsAreEmptyQuery stateArgument)
    finishBody generatedRunningFallback

def generatedRunningDispatcher : Pattern :=
  runningDispatcher finishBody skipHeadBody skipArityBody beginDeclarationBody

def generatedArgumentsDispatcher : Pattern :=
  argumentsDispatcher argumentsFinishedBody rawInputBody undefinedInputBody
    holeInputBody checkedInputBody openInputBody

/-- The exact generated literal/input-classification tree. -/
def generatedLiteralInputDispatcher : Pattern :=
  literalInputDispatcher rawInputBody undefinedInputBody holeInputBody
    checkedInputBody openInputBody

/-- The final non-literal fallback preserves the authored checked-before-open
ordering and the explicit no-transition outcome. -/
def generatedCheckedOpenInputFallback : Pattern :=
  sequence [checkedInputBody, openInputBody, outcomeBody noTransitionOutcome]

theorem generatedCheckedOpenInputFallback_shape :
    generatedCheckedOpenInputFallback =
      statements [checkedInputDecision, openInputDecision,
        returnSymbol noTransitionOutcome] := by
  rfl

def generatedHoleInputDecision : Pattern :=
  ifThenElse (call termIsHoleQuery [variableExpression "expected"])
    holeInputBody generatedCheckedOpenInputFallback

def generatedUndefinedInputFallback : Pattern :=
  statements [generatedHoleInputDecision]

def generatedUndefinedInputDecision : Pattern :=
  ifThenElse (call termIsUndefinedQuery [variableExpression "expected"])
    undefinedInputBody generatedUndefinedInputFallback

def generatedAtomInputFallback : Pattern :=
  statements [generatedUndefinedInputDecision]

def generatedAtomInputDecision : Pattern :=
  ifThenElse (call termIsAtomQuery [variableExpression "expected"])
    rawInputBody generatedAtomInputFallback

/-- The generated literal dispatcher is exactly the authored ordered decision
tree, not a table keyed by a claimed source-family name. -/
theorem generatedLiteralInputDispatcher_shape :
    generatedLiteralInputDispatcher =
      statements [generatedAtomInputDecision] := by
  rfl

/-- The ordered nonempty-cursor continuation of the generated argument
dispatcher. -/
def generatedArgumentsNonempty : Pattern :=
  sequence [inputBindings, generatedLiteralInputDispatcher]

/-- The exact generated decision following the common, declaration, and mode
projections of an argument state. -/
def generatedArgumentsDecision : Pattern :=
  ifThenElse (call inputCursorIsEmptyQuery stateArgument)
    argumentsFinishedBody generatedArgumentsNonempty

def generatedLiteralResultDispatcher : Pattern :=
  literalResultDispatcher undefinedResultBody holeResultBody atomResultBody
    checkedResultBody openResultBody

/-- The final non-literal result fallback preserves checked-before-open
ordering and the explicit no-transition outcome. -/
def generatedCheckedOpenResultFallback : Pattern :=
  sequence [checkedResultBody, openResultBody,
    outcomeBody noTransitionOutcome]

theorem generatedCheckedOpenResultFallback_shape :
    generatedCheckedOpenResultFallback =
      statements [checkedResultDecision, openResultDecision,
        returnSymbol noTransitionOutcome] := by
  rfl

def generatedAtomResultDecision : Pattern :=
  ifThenElse (call termIsAtomQuery [variableExpression "output"])
    atomResultBody generatedCheckedOpenResultFallback

def generatedHoleResultFallback : Pattern :=
  statements [generatedAtomResultDecision]

def generatedHoleResultDecision : Pattern :=
  ifThenElse (call termIsHoleQuery [variableExpression "output"])
    holeResultBody generatedHoleResultFallback

def generatedUndefinedResultFallback : Pattern :=
  statements [generatedHoleResultDecision]

def generatedUndefinedResultDecision : Pattern :=
  ifThenElse (call termIsUndefinedQuery [variableExpression "output"])
    undefinedResultBody generatedUndefinedResultFallback

theorem generatedLiteralResultDispatcher_shape :
    generatedLiteralResultDispatcher =
      statements [generatedUndefinedResultDecision] := by
  rfl

def generatedResultDispatcher : Pattern :=
  resultDispatcher undefinedResultBody holeResultBody atomResultBody
    checkedResultBody openResultBody

def generatedTerminalBody : Pattern :=
  statements [returnSymbol terminalOutcome]

def generatedFaultBody : Pattern :=
  statements [returnSymbol engineFaultOutcome]

def generatedPhaseCases : Pattern :=
  Mettapedia.GSLT.LanguageDef.StructuredC.Builder.cases
  [ caseBranch (valueSymbol runningPhase) generatedRunningDispatcher
  , caseBranch (valueSymbol argumentsPhase) generatedArgumentsDispatcher
  , caseBranch (valueSymbol resultPhase) generatedResultDispatcher
  , caseBranch (valueSymbol haltedPhase) generatedTerminalBody ]

/-- The generated running branch is a concrete six-statement spine: five
ordered projections followed by its visible declaration-list decision. -/
theorem generatedRunningDispatcher_shape : generatedRunningDispatcher =
    statements [
      bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection,
      bindProjection "revision" "CettaPeTTaCallGuardNatV1"
        revisionProjection,
      bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection,
      bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection,
      bindProjection "accepted" "CettaPeTTaCallGuardPlansV1"
        acceptedProjection,
      generatedRunningDecision] := by
  rfl

/-- The generated argument branch is an explicit twelve-statement spine:
five common projections, five declaration projections, the accumulated modes,
and the visible cursor-shape decision. -/
theorem generatedArgumentsDispatcher_shape : generatedArgumentsDispatcher =
    statements [
      bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection,
      bindProjection "revision" "CettaPeTTaCallGuardNatV1"
        revisionProjection,
      bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection,
      bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection,
      bindProjection "accepted" "CettaPeTTaCallGuardPlansV1"
        acceptedProjection,
      bindProjection "remaining" "CettaPeTTaCallGuardDeclarationsV1"
        remainingProjection,
      bindProjection "occurrence" "CettaPeTTaCallGuardNatV1"
        occurrenceProjection,
      bindProjection "declaration_head" "CettaPeTTaCallGuardNameV1"
        declarationHeadProjection,
      bindProjection "inputs" "CettaPeTTaCallGuardTermsV1" inputsProjection,
      bindProjection "output" "CettaPeTTaCallGuardTermV1" outputProjection,
      bindProjection "modes" "CettaPeTTaCallGuardArgModesV1" modesProjection,
      generatedArgumentsDecision] := by
  rfl

/-- The generated result branch is an explicit twelve-statement spine: five
common projections, five declaration projections, the accumulated modes, and
the ordered five-family result discriminator. -/
theorem generatedResultDispatcher_shape : generatedResultDispatcher =
    statements [
      bindProjection "owner" "CettaPeTTaCallGuardOwnerV1" ownerProjection,
      bindProjection "revision" "CettaPeTTaCallGuardNatV1"
        revisionProjection,
      bindProjection "head" "CettaPeTTaCallGuardNameV1" headProjection,
      bindProjection "arity" "CettaPeTTaCallGuardNatV1" arityProjection,
      bindProjection "accepted" "CettaPeTTaCallGuardPlansV1"
        acceptedProjection,
      bindProjection "remaining" "CettaPeTTaCallGuardDeclarationsV1"
        remainingProjection,
      bindProjection "occurrence" "CettaPeTTaCallGuardNatV1"
        occurrenceProjection,
      bindProjection "declaration_head" "CettaPeTTaCallGuardNameV1"
        declarationHeadProjection,
      bindProjection "inputs" "CettaPeTTaCallGuardTermsV1" inputsProjection,
      bindProjection "output" "CettaPeTTaCallGuardTermV1" outputProjection,
      bindProjection "modes" "CettaPeTTaCallGuardArgModesV1" modesProjection,
      generatedUndefinedResultDecision] := by
  rfl

theorem generatedArgumentsNonempty_shape : generatedArgumentsNonempty =
    StructuredC.consStatement
      (bindProjection "expected" "CettaPeTTaCallGuardTermV1"
        inputHeadProjection)
      (StructuredC.consStatement
        (bindProjection "input_cursor" "CettaPeTTaCallGuardTermsV1"
          inputTailProjection)
        generatedLiteralInputDispatcher) := by
  rfl

/-- The generated body is the visible three-phase dispatcher assembled from
the exact fifteen authenticated source families. -/
theorem generatedColdBody_shape : generatedColdBody =
    statements [node "structured-c:switch"
      [ call compilePhaseQuery [variableExpression "state"]
      , generatedPhaseCases, generatedFaultBody ]] := by
  rfl

theorem assemble_all_bodies_body :
    assembleDispatcherBody? allMatchedFamilyBodies = some generatedColdBody := by
  decide +kernel

def generatedColdFunction : Pattern :=
  function generatedFunctionName
    (namedType "CettaPeTTaCallGuardTransitionOutcomeV1")
    [parameter "state"
      (namedPointerType "CettaPeTTaCallGuardCompileStateV1")]
    generatedColdBody

theorem assemble_all_bodies :
    assembleFunction? allMatchedFamilyBodies = some generatedColdFunction := by
  decide +kernel

theorem language_lowers_to_generated_function :
    lowerDecodedColdFunction? language = some generatedColdFunction := by
  simp [lowerDecodedColdFunction?, language_lowers_all_families,
    assemble_all_bodies]

/-- Successful generation retains exact source authority and has one target. -/
theorem lowerDecodedColdFunction?_eq_some_iff
    (source : LanguageDef) (target : Pattern) :
    lowerDecodedColdFunction? source = some target ↔
      source.rewrites = transitions ∧ target = generatedColdFunction := by
  constructor
  · intro lowered
    unfold lowerDecodedColdFunction? at lowered
    cases bodiesResult : lowerDecodedLanguage? source with
    | none => simp [bodiesResult] at lowered
    | some bodies =>
        have sourceAndBodies :=
          (lowerDecodedLanguage?_eq_some_iff source bodies).mp bodiesResult
        obtain ⟨sourceExact, rfl⟩ := sourceAndBodies
        simp [bodiesResult, assemble_all_bodies] at lowered
        exact ⟨sourceExact, lowered.symm⟩
  · rintro ⟨sourceExact, rfl⟩
    have bodiesExact :
        lowerDecodedLanguage? source = some allMatchedFamilyBodies :=
      (lowerDecodedLanguage?_eq_some_iff source allMatchedFamilyBodies).2
        ⟨sourceExact, rfl⟩
    simp [lowerDecodedColdFunction?, bodiesExact, assemble_all_bodies]

theorem generatedColdFunction_target_typed :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] generatedColdFunction
      (.base "Function") = true := by
  decide +kernel

/-- Each contiguous source group is present in its original order. -/
theorem dispatcher_order_is_load_bearing :
    generatedColdFunction ≠
      (assembleFunction?
        [ finishBody, skipArityBody, skipHeadBody, beginDeclarationBody
        , argumentsFinishedBody, rawInputBody, undefinedInputBody, holeInputBody
        , checkedInputBody, openInputBody, undefinedResultBody, holeResultBody
        , atomResultBody, checkedResultBody, openResultBody ]).getD
          (node "structured-c:unreachable-cold-function") := by
  decide

#print axioms lowerDecodedColdFunction?_eq_some_iff
#print axioms generatedColdBody_shape
#print axioms generatedRunningDispatcher_shape
#print axioms generatedColdFunction_target_typed
#print axioms dispatcher_order_is_load_bearing

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
