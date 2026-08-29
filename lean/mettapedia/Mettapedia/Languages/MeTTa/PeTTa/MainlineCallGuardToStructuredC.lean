import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT
import Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# StructuredC lowering for PeTTa mainline call-guard transitions

The generated target contains one cold compiler transition and one executor
transition.  Iteration remains the responsibility of the surrounding machine
loop.  Every semantic observation is an explicit external call, while branch
selection, mode dispatch, currentness, and the exact-before-metatype soft cut
remain visible StructuredC control.

The external functions in this module are narrow hooks.  None returns a
precomputed plan, family decision, or successful-declaration list.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

set_option autoImplicit false

private def sc (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def token (name : String) : Pattern := sc name

private def identifier (name : String) : Pattern :=
  sc "structured-c:identifier" [token name]

private def functionName (name : String) : Pattern :=
  sc "structured-c:function-name" [token name]

private def externalName (name : String) : Pattern :=
  sc "structured-c:external-name" [token name]

private def namedType (name : String) : Pattern :=
  sc "structured-c:type-named" [identifier name]

private def pointerType (name : String) (isConst : Bool) : Pattern :=
  let base := namedType name
  let target := if isConst then sc "structured-c:type-const" [base] else base
  sc "structured-c:type-pointer" [target]

private def valueSymbol (name : String) : Pattern :=
  sc "structured-c:value-symbol" [identifier name]

private def constant (name : String) : Pattern :=
  sc "structured-c:expression-constant" [valueSymbol name]

private def variableExpression (name : String) : Pattern :=
  sc "structured-c:expression-variable" [identifier name]

private def expressionList : List Pattern → Pattern
  | [] => sc "structured-c:expressions-nil"
  | expression :: rest =>
      sc "structured-c:expressions-cons" [expression, expressionList rest]

private def call (name : String) (arguments : List Pattern) : Pattern :=
  sc "structured-c:expression-call" [externalName name,
    expressionList arguments]

private def statements : List Pattern → Pattern
  | [] => sc "structured-c:statements-nil"
  | statement :: rest =>
      sc "structured-c:statements-cons" [statement, statements rest]

private def effect (expression : Pattern) : Pattern :=
  sc "structured-c:effect" [expression]

private def returnSymbol (name : String) : Pattern :=
  sc "structured-c:return" [constant name]

private def ifStatement (condition thenBranch elseBranch : Pattern) : Pattern :=
  sc "structured-c:if" [condition, thenBranch, elseBranch]

private def caseStatement (value body : Pattern) : Pattern :=
  sc "structured-c:case" [value, body]

private def cases : List Pattern → Pattern
  | [] => sc "structured-c:cases-nil"
  | one :: rest => sc "structured-c:cases-cons" [one, cases rest]

private def switchStatement
    (scrutinee cases defaultBranch : Pattern) : Pattern :=
  sc "structured-c:switch" [scrutinee, cases, defaultBranch]

private def parameter (name typeName : String) (isConst : Bool) : Pattern :=
  sc "structured-c:parameter" [identifier name,
    pointerType typeName isConst]

private def valueParameter (name typeName : String) : Pattern :=
  sc "structured-c:parameter" [identifier name, namedType typeName]

private def parameterList : List Pattern → Pattern
  | [] => sc "structured-c:parameters-nil"
  | one :: rest =>
      sc "structured-c:parameters-cons" [one, parameterList rest]

private def function (name : String) (parameters body : Pattern) : Pattern :=
  sc "structured-c:function" [functionName name,
    namedType "CettaPeTTaCallGuardTransitionOutcomeV1", parameters, body]

private def externalFunction (name returnType : String)
    (parameters : Pattern) : Pattern :=
  sc "structured-c:external-function" [externalName name,
    namedType returnType, parameters]

private def externalFunctions : List Pattern → Pattern
  | [] => sc "structured-c:external-functions-nil"
  | one :: rest =>
      sc "structured-c:external-functions-cons" [one,
        externalFunctions rest]

private def functions : List Pattern → Pattern
  | [] => sc "structured-c:functions-nil"
  | one :: rest =>
      sc "structured-c:functions-cons" [one, functions rest]

private def stateParameters : Pattern := parameterList [
  parameter "state" "CettaPeTTaCallGuardTransitionStateV1" false,
  parameter "receipt" "CettaPeTTaCallGuardTransitionReceiptV1" false]

private def stateOnlyParameters : Pattern := parameterList [
  parameter "state" "CettaPeTTaCallGuardTransitionStateV1" false]

private def engineFault : Pattern := statements [
  returnSymbol "CETTA_PETTA_CALL_GUARD_ENGINE_FAULT_V1"]

private def advanced : Pattern := statements [
  returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]

private def rejected : Pattern := statements [
  effect (call "cetta_petta_call_guard_reject_plan_v1" [variableExpression "state"]),
  returnSymbol "CETTA_PETTA_CALL_GUARD_REJECTED_V1"]

private def fallback (reason : String) : Pattern := statements [
  effect (call "cetta_petta_call_guard_record_fallback_v1"
    [variableExpression "state", constant reason]),
  returnSymbol reason]

private def emitInputChecked : Pattern := statements [
  effect (call "cetta_petta_call_guard_emit_eval_checked_mode_v1"
    [variableExpression "state"]),
  returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]

private def emitInputUnchecked : Pattern := statements [
  effect (call "cetta_petta_call_guard_emit_eval_unchecked_mode_v1"
    [variableExpression "state"]),
  returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]

private def compileInputMode : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_expected_is_atom_v1" [variableExpression "state"])
  (statements [
    effect (call "cetta_petta_call_guard_emit_raw_mode_v1"
      [variableExpression "state"]),
    returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
  (statements [ifStatement
    (call "cetta_petta_call_guard_expected_is_undefined_v1"
      [variableExpression "state"])
    emitInputUnchecked
    (statements [ifStatement
      (call "cetta_petta_call_guard_expected_is_hole_v1"
        [variableExpression "state"])
      emitInputUnchecked
      (statements [ifStatement
        (call "cetta_petta_call_guard_expected_is_closed_v1"
          [variableExpression "state"])
        emitInputChecked
        (fallback
          "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1")])])])]

private def emitResultUnchecked : Pattern := statements [
  effect (call "cetta_petta_call_guard_emit_result_unchecked_mode_v1"
    [variableExpression "state"]),
  returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]

private def emitResultChecked : Pattern := statements [
  effect (call "cetta_petta_call_guard_emit_result_checked_mode_v1"
    [variableExpression "state"]),
  returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]

private def compileResultMode : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_expected_is_undefined_v1"
    [variableExpression "state"])
  emitResultUnchecked
  (statements [ifStatement
    (call "cetta_petta_call_guard_expected_is_hole_v1"
      [variableExpression "state"])
    emitResultUnchecked
    (statements [ifStatement
      (call "cetta_petta_call_guard_expected_is_atom_v1"
        [variableExpression "state"])
      emitResultUnchecked
      (statements [ifStatement
        (call "cetta_petta_call_guard_expected_is_closed_v1"
          [variableExpression "state"])
        emitResultChecked
        (fallback
          "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1")])])])]

private def compileStateCases : Pattern := cases [
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_FINISH_V1")
    (statements [
      effect (call "cetta_petta_call_guard_finish_compiled_family_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_COMPILED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_INSPECT_V1")
    (statements [ifStatement
      (call "cetta_petta_call_guard_declaration_relevant_v1"
        [variableExpression "state"])
      (statements [effect (call
        "cetta_petta_call_guard_begin_mode_compilation_v1"
        [variableExpression "state"])])
      (statements [effect (call
        "cetta_petta_call_guard_skip_declaration_v1"
        [variableExpression "state"])]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_INPUT_V1")
    compileInputMode,
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_RESULT_V1")
    compileResultMode,
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_EMIT_V1")
    (statements [
      effect (call "cetta_petta_call_guard_emit_plan_v1" [variableExpression "state"]),
      effect (call "cetta_petta_call_guard_advance_declaration_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]),
  caseStatement (valueSymbol
      "CETTA_PETTA_CALL_GUARD_COMPILE_OUTSIDE_FRAGMENT_V1")
    (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1"),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_COMPILE_HALTED_V1")
    (statements [returnSymbol "CETTA_PETTA_CALL_GUARD_TERMINAL_V1"])]

/-- One explicit cold compiler micro-transition. -/
def loweredCompileTransitionBody : Pattern := statements [
  switchStatement
    (call "cetta_petta_call_guard_compile_state_tag_v1" [variableExpression "state"])
    compileStateCases engineFault]

private def executeCheckedArgument : Pattern := statements [
  effect (call "cetta_petta_call_guard_evaluate_argument_v1"
    [variableExpression "state", variableExpression "receipt"]),
  ifStatement
    (call "cetta_petta_call_guard_get_type_v1"
      [variableExpression "state", variableExpression "receipt"])
    (statements [
      effect (call "cetta_petta_call_guard_advance_argument_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
    (statements [ifStatement
      (call "cetta_petta_call_guard_get_metatype_v1"
        [variableExpression "state", variableExpression "receipt"])
      (statements [
        effect (call "cetta_petta_call_guard_advance_argument_v1"
          [variableExpression "state"]),
        returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
      rejected])]

private def executeArgumentCases : Pattern := cases [
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_ARG_RAW_V1")
    (statements [ifStatement
      (call "cetta_petta_call_guard_raw_argument_equal_v1"
        [variableExpression "state", variableExpression "receipt"])
      (statements [
        effect (call "cetta_petta_call_guard_advance_argument_v1"
          [variableExpression "state"]),
        returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
      rejected]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_ARG_EVAL_UNCHECKED_V1")
    (statements [
      effect (call "cetta_petta_call_guard_evaluate_argument_v1"
        [variableExpression "state", variableExpression "receipt"]),
      effect (call "cetta_petta_call_guard_advance_argument_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_ARG_EVAL_CHECKED_V1")
    executeCheckedArgument]

private def executeCheckedResult : Pattern := statements [
  ifStatement
    (call "cetta_petta_call_guard_get_result_type_v1"
      [variableExpression "state", variableExpression "receipt"])
    (statements [
      effect (call "cetta_petta_call_guard_advance_result_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
    (statements [ifStatement
      (call "cetta_petta_call_guard_get_result_metatype_v1"
        [variableExpression "state", variableExpression "receipt"])
      (statements [
        effect (call "cetta_petta_call_guard_advance_result_v1"
          [variableExpression "state"]),
        returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
      rejected])]

private def executeResultCases : Pattern := cases [
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_RESULT_UNCHECKED_V1")
    (statements [
      effect (call "cetta_petta_call_guard_advance_result_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_RESULT_CHECKED_V1")
    executeCheckedResult]

private def arityCheck : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_arity_matches_v1" [variableExpression "state"])
  (statements [
    effect (call "cetta_petta_call_guard_begin_plan_v1"
      [variableExpression "state"]),
    returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"])
  (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_WRONG_ARITY_V1")]

private def headCheck : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_head_matches_v1" [variableExpression "state"])
  arityCheck
  (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_WRONG_HEAD_V1")]

private def revisionCheck : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_revision_current_v1" [variableExpression "state"])
  headCheck
  (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_STALE_REVISION_V1")]

private def currentnessChecks : Pattern := statements [ifStatement
  (call "cetta_petta_call_guard_owner_current_v1" [variableExpression "state"])
  revisionCheck
  (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_FOREIGN_OWNER_V1")]

private def executeStateCases : Pattern := cases [
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_AUTHORITY_V1")
    currentnessChecks,
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_ARGUMENT_V1")
    (statements [switchStatement
      (call "cetta_petta_call_guard_argument_mode_tag_v1" [variableExpression "state"])
      executeArgumentCases engineFault]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_BODY_V1")
    (statements [
      effect (call "cetta_petta_call_guard_evaluate_call_v1"
        [variableExpression "state", variableExpression "receipt"]),
      effect (call "cetta_petta_call_guard_begin_result_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_RESULT_V1")
    (statements [switchStatement
      (call "cetta_petta_call_guard_execution_result_mode_tag_v1"
        [variableExpression "state"])
      executeResultCases engineFault]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_INSTALL_V1")
    (statements [
      effect (call "cetta_petta_call_guard_install_occurrence_v1"
        [variableExpression "state", variableExpression "receipt"]),
      effect (call "cetta_petta_call_guard_advance_plan_v1"
        [variableExpression "state"]),
      returnSymbol "CETTA_PETTA_CALL_GUARD_INSTALLED_V1"]),
  /- `begin_plan` selects this explicit phase when the mode, source, and
     evaluated-argument vectors do not have the same shape. -/
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_REJECT_V1")
    rejected,
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_EMPTY_V1")
    (statements [returnSymbol "CETTA_PETTA_CALL_GUARD_EXECUTED_EMPTY_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_DONE_V1")
    (statements [returnSymbol "CETTA_PETTA_CALL_GUARD_EXECUTED_V1"]),
  caseStatement (valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTE_OUTSIDE_V1")
    (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1")]

/-- One explicit hot executor micro-transition. -/
def loweredExecuteTransitionBody : Pattern := statements [
  switchStatement
    (call "cetta_petta_call_guard_execute_state_tag_v1" [variableExpression "state"])
    executeStateCases engineFault]

def loweredCompileTransition : Pattern :=
  function "cetta_generated_petta_call_guard_compile_transition_v1"
    stateOnlyParameters loweredCompileTransitionBody

def loweredExecuteTransition : Pattern :=
  function "cetta_generated_petta_call_guard_execute_transition_v1"
    stateParameters loweredExecuteTransitionBody

private def stateHook (name returnType : String) : Pattern :=
  externalFunction name returnType stateOnlyParameters

private def stateReceiptHook (name returnType : String) : Pattern :=
  externalFunction name returnType stateParameters

def primitiveHooks : List Pattern := [
  stateHook "cetta_petta_call_guard_compile_state_tag_v1" "CettaTagV1",
  stateHook "cetta_petta_call_guard_declaration_relevant_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_begin_mode_compilation_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_skip_declaration_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_expected_is_atom_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_expected_is_undefined_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_expected_is_hole_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_expected_is_closed_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_emit_raw_mode_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_emit_eval_unchecked_mode_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_emit_eval_checked_mode_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_emit_result_unchecked_mode_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_emit_result_checked_mode_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_emit_plan_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_advance_declaration_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_finish_compiled_family_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_execute_state_tag_v1" "CettaTagV1",
  stateHook "cetta_petta_call_guard_owner_current_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_revision_current_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_head_matches_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_arity_matches_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_begin_plan_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_argument_mode_tag_v1" "CettaTagV1",
  stateReceiptHook "cetta_petta_call_guard_raw_argument_equal_v1" "CettaBoolV1",
  stateReceiptHook "cetta_petta_call_guard_evaluate_argument_v1" "CettaUnitV1",
  stateReceiptHook "cetta_petta_call_guard_get_type_v1" "CettaBoolV1",
  stateReceiptHook "cetta_petta_call_guard_get_metatype_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_advance_argument_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_reject_plan_v1" "CettaUnitV1",
  stateReceiptHook "cetta_petta_call_guard_evaluate_call_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_begin_result_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_execution_result_mode_tag_v1" "CettaTagV1",
  stateReceiptHook "cetta_petta_call_guard_get_result_type_v1" "CettaBoolV1",
  stateReceiptHook "cetta_petta_call_guard_get_result_metatype_v1" "CettaBoolV1",
  stateHook "cetta_petta_call_guard_advance_result_v1" "CettaUnitV1",
  stateReceiptHook "cetta_petta_call_guard_install_occurrence_v1" "CettaUnitV1",
  stateHook "cetta_petta_call_guard_advance_plan_v1" "CettaUnitV1",
  externalFunction "cetta_petta_call_guard_record_fallback_v1" "CettaUnitV1"
    (parameterList [
      parameter "state" "CettaPeTTaCallGuardTransitionStateV1" false,
      valueParameter "reason" "CettaPeTTaCallGuardTransitionOutcomeV1"])]

def loweredProgram : Pattern := sc "structured-c:program" [
  externalFunctions primitiveHooks,
  functions [loweredCompileTransition, loweredExecuteTransition]]

theorem lowered_compile_transition_has_type :
    CarrierWellSorted.HasType
      Mettapedia.GSLT.LanguageDef.StructuredC.language
      WellSorted.FreeTypeContext.empty [] loweredCompileTransition
      (.base "Function") := by
  apply CarrierWellSorted.checkHasType_sound
  set_option maxRecDepth 100000 in
    decide +kernel

theorem lowered_execute_transition_has_type :
    CarrierWellSorted.HasType
      Mettapedia.GSLT.LanguageDef.StructuredC.language
      WellSorted.FreeTypeContext.empty [] loweredExecuteTransition
      (.base "Function") := by
  apply CarrierWellSorted.checkHasType_sound
  set_option maxRecDepth 100000 in
    decide +kernel

theorem lowered_program_has_type :
    CarrierWellSorted.HasType
      Mettapedia.GSLT.LanguageDef.StructuredC.language
      WellSorted.FreeTypeContext.empty [] loweredProgram (.base "Program") := by
  apply CarrierWellSorted.checkHasType_sound
  set_option maxRecDepth 100000 in
    decide +kernel

/-! Syntactic mutation canaries for the load-bearing target order. -/

private def metatypeBeforeExactMutation : Pattern := statements [
  effect (call "cetta_petta_call_guard_evaluate_argument_v1"
    [variableExpression "state", variableExpression "receipt"]),
  ifStatement
    (call "cetta_petta_call_guard_get_metatype_v1"
      [variableExpression "state", variableExpression "receipt"])
    advanced
    (statements [ifStatement
      (call "cetta_petta_call_guard_get_type_v1"
        [variableExpression "state", variableExpression "receipt"])
      advanced rejected])]

private def revisionBeforeOwnerMutation : Pattern := statements [
  ifStatement
    (call "cetta_petta_call_guard_revision_current_v1" [variableExpression "state"])
    advanced
    (fallback "CETTA_PETTA_CALL_GUARD_FALLBACK_STALE_REVISION_V1")]

theorem exact_before_metatype_is_load_bearing :
    executeCheckedArgument ≠ metatypeBeforeExactMutation := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem owner_before_revision_is_load_bearing :
    currentnessChecks ≠ revisionBeforeOwnerMutation := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem compiled_empty_and_outside_fragment_are_distinct :
    valueSymbol "CETTA_PETTA_CALL_GUARD_EXECUTED_EMPTY_V1" ≠
      valueSymbol "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1" := by
  decide +kernel

#print axioms lowered_compile_transition_has_type
#print axioms lowered_execute_transition_has_type
#print axioms lowered_program_has_type
#print axioms exact_before_metatype_is_load_bearing
#print axioms owner_before_revision_is_load_bearing
#print axioms compiled_empty_and_outside_fragment_are_distinct

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC
