import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC

/-!
# Operational semantics of the PeTTa call-guard StructuredC lowering

The finite reference catalogs below execute the actual StructuredC statement
bodies.  Primitive calls record their names in the receipt, so control order is
observable.  Catalogs provide only state tags, local comparisons, evaluation
observations, and state-update acknowledgements; they never provide a plan or
family verdict.

The branch scenarios cover every compiler and executor dispatch faultClass.  The
generic semantic model at the end independently reconstructs compilation and
execution from the same local decisions and proves exact agreement with the G2
artifact and ordered execution observations.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredC

set_option autoImplicit false

private def sc (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def token (name : String) : Pattern := sc name

private def identifier (name : String) : Pattern :=
  sc "structured-c:identifier" [token name]

private def externalName (name : String) : Pattern :=
  sc "structured-c:external-name" [token name]

private def valueSymbol (name : String) : Pattern :=
  sc "structured-c:value-symbol" [identifier name]

private def valueUnit : Pattern := sc "structured-c:value-unit"

private def evaluationValue (value : Pattern) : Pattern :=
  sc "structured-c:evaluation-value" [value]

private def evaluationFault (fault : Pattern) : Pattern :=
  sc "structured-c:evaluation-fault" [fault]

private def outcomeReturn (value : Pattern) : Pattern :=
  sc "structured-c:outcome-return" [value]

private def outcomeFault (fault : Pattern) : Pattern :=
  sc "structured-c:outcome-fault" [fault]

private def environment : Pattern := sc "structured-c:environment-empty"

private def readyReceipt : Pattern := sc "structured-c:receipt-ready"

private def hookReceipt (name : String) (prior : Pattern) : Pattern :=
  sc "structured-c:receipt-external"
    [valueSymbol name, valueUnit, valueUnit, prior]

private def receipts (names : List String) : Pattern :=
  names.foldl (fun prior name => hookReceipt name prior) readyReceipt

private def trueValue : Pattern := valueSymbol "true"
private def falseValue : Pattern := valueSymbol "false"

inductive PrimitiveResult where
  | value (value : Pattern)
  | fault (fault : Pattern)
deriving DecidableEq, Repr

abbrev PrimitiveCatalog := String → Option PrimitiveResult

private def externalCallName? : Pattern → Option String
  | .apply "structured-c:expression-call"
      [.apply "structured-c:external-name" [.apply name []], _] => some name
  | _ => none

private def evaluateExpression
    (catalog : PrimitiveCatalog) : Pattern → Option PrimitiveResult
  | .apply "structured-c:expression-constant" [value] =>
      some (.value value)
  | expression => externalCallName? expression >>= catalog

private def selectBranch? (value thenBranch elseBranch : Pattern) :
    Option Pattern :=
  if value = trueValue then some thenBranch
  else if value = falseValue then some elseBranch
  else none

private def selectCase? (value : Pattern) : Pattern → Option Pattern
  | .apply "structured-c:cases-nil" [] => none
  | .apply "structured-c:cases-cons"
      [.apply "structured-c:case" [candidate, body], rest] =>
      if candidate = value then some body else selectCase? value rest
  | _ => none

private def referenceEnv (catalog : PrimitiveCatalog) : RelationEnv where
  tuples := fun relation arguments =>
    if relation = "StructuredCEvaluate" then
      match arguments with
      | expression :: currentEnvironment :: currentReceipt :: _ =>
          match evaluateExpression catalog expression with
          | some (.value value) => [[expression, currentEnvironment,
              currentReceipt, evaluationValue value, currentEnvironment,
              match externalCallName? expression with
              | some name => hookReceipt name currentReceipt
              | none => currentReceipt]]
          | some (.fault fault) => [[expression, currentEnvironment,
              currentReceipt, evaluationFault fault, currentEnvironment,
              match externalCallName? expression with
              | some name => hookReceipt name currentReceipt
              | none => currentReceipt]]
          | none => []
      | _ => []
    else if relation = "StructuredCSelectBranch" then
      match arguments with
      | value :: thenBranch :: elseBranch :: _ =>
          match selectBranch? value thenBranch elseBranch with
          | some selected => [[value, thenBranch, elseBranch, selected]]
          | none => []
      | _ => []
    else if relation = "StructuredCSelectCase" then
      match arguments with
      | authoredCases :: defaultBranch :: value :: _ =>
          let selected := (selectCase? value authoredCases).getD defaultBranch
          [[authoredCases, defaultBranch, value, selected]]
      | _ => []
    else
      []

private def unitHooks : List String := [
  "cetta_petta_call_guard_begin_mode_compilation_v1",
  "cetta_petta_call_guard_skip_declaration_v1",
  "cetta_petta_call_guard_emit_raw_mode_v1",
  "cetta_petta_call_guard_emit_eval_unchecked_mode_v1",
  "cetta_petta_call_guard_emit_eval_checked_mode_v1",
  "cetta_petta_call_guard_emit_result_unchecked_mode_v1",
  "cetta_petta_call_guard_emit_result_checked_mode_v1",
  "cetta_petta_call_guard_emit_plan_v1",
  "cetta_petta_call_guard_advance_declaration_v1",
  "cetta_petta_call_guard_finish_compiled_family_v1",
  "cetta_petta_call_guard_record_fallback_v1",
  "cetta_petta_call_guard_begin_plan_v1",
  "cetta_petta_call_guard_evaluate_argument_v1",
  "cetta_petta_call_guard_advance_argument_v1",
  "cetta_petta_call_guard_reject_plan_v1",
  "cetta_petta_call_guard_evaluate_call_v1",
  "cetta_petta_call_guard_begin_result_v1",
  "cetta_petta_call_guard_advance_result_v1",
  "cetta_petta_call_guard_install_occurrence_v1",
  "cetta_petta_call_guard_advance_plan_v1"]

private def unitOrNone (name : String) : Option PrimitiveResult :=
  if name ∈ unitHooks then some (.value valueUnit) else none

private def boolResult (answer : Bool) : PrimitiveResult :=
  .value (if answer then trueValue else falseValue)

/-! ## Complete compiler branch catalog -/

inductive CompileScenario where
  | finish
  | inspectRelevant
  | inspectIrrelevant
  | inputRaw
  | inputUndefined
  | inputHole
  | inputChecked
  | inputOpen
  | resultUndefined
  | resultHole
  | resultAtom
  | resultChecked
  | resultOpen
  | emit
  | outsideFragment
  | halted
  | unknown
deriving DecidableEq, Repr

private def CompileScenario.tag : CompileScenario → String
  | .finish => "CETTA_PETTA_CALL_GUARD_COMPILE_FINISH_V1"
  | .inspectRelevant | .inspectIrrelevant =>
      "CETTA_PETTA_CALL_GUARD_COMPILE_INSPECT_V1"
  | .inputRaw | .inputUndefined | .inputHole | .inputChecked | .inputOpen =>
      "CETTA_PETTA_CALL_GUARD_COMPILE_INPUT_V1"
  | .resultUndefined | .resultHole | .resultAtom | .resultChecked |
      .resultOpen => "CETTA_PETTA_CALL_GUARD_COMPILE_RESULT_V1"
  | .emit => "CETTA_PETTA_CALL_GUARD_COMPILE_EMIT_V1"
  | .outsideFragment =>
      "CETTA_PETTA_CALL_GUARD_COMPILE_OUTSIDE_FRAGMENT_V1"
  | .halted => "CETTA_PETTA_CALL_GUARD_COMPILE_HALTED_V1"
  | .unknown => "CETTA_PETTA_CALL_GUARD_COMPILE_UNKNOWN_V1"

private def CompileScenario.answer
    (scenario : CompileScenario) (name : String) : Option Bool :=
  match name with
  | "cetta_petta_call_guard_declaration_relevant_v1" =>
      match scenario with
      | .inspectRelevant => some true
      | .inspectIrrelevant => some false
      | _ => none
  | "cetta_petta_call_guard_expected_is_atom_v1" =>
      match scenario with
      | .inputRaw | .resultAtom => some true
      | .inputUndefined | .inputHole | .inputChecked | .inputOpen |
          .resultUndefined | .resultHole | .resultChecked | .resultOpen =>
          some false
      | _ => none
  | "cetta_petta_call_guard_expected_is_undefined_v1" =>
      match scenario with
      | .inputUndefined | .resultUndefined => some true
      | .inputHole | .inputChecked | .inputOpen | .resultHole |
          .resultAtom | .resultChecked | .resultOpen => some false
      | _ => none
  | "cetta_petta_call_guard_expected_is_hole_v1" =>
      match scenario with
      | .inputHole | .resultHole => some true
      | .inputChecked | .inputOpen | .resultAtom | .resultChecked |
          .resultOpen => some false
      | _ => none
  | "cetta_petta_call_guard_expected_is_closed_v1" =>
      match scenario with
      | .inputChecked | .resultChecked => some true
      | .inputOpen | .resultOpen => some false
      | _ => none
  | _ => none

private def compileCatalog (scenario : CompileScenario) : PrimitiveCatalog :=
  fun name =>
    if name = "cetta_petta_call_guard_compile_state_tag_v1" then
      some (.value (valueSymbol scenario.tag))
    else
      match scenario.answer name with
      | some answer => some (boolResult answer)
      | none => unitOrNone name

private def CompileScenario.outcome : CompileScenario → String
  | .finish => "CETTA_PETTA_CALL_GUARD_COMPILED_V1"
  | .inputOpen | .resultOpen | .outsideFragment =>
      "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1"
  | .halted => "CETTA_PETTA_CALL_GUARD_TERMINAL_V1"
  | .unknown => "CETTA_PETTA_CALL_GUARD_ENGINE_FAULT_V1"
  | _ => "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"

private def CompileScenario.hooks : CompileScenario → List String
  | .finish => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_finish_compiled_family_v1"]
  | .inspectRelevant => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_declaration_relevant_v1",
      "cetta_petta_call_guard_begin_mode_compilation_v1"]
  | .inspectIrrelevant => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_declaration_relevant_v1",
      "cetta_petta_call_guard_skip_declaration_v1"]
  | .inputRaw => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_emit_raw_mode_v1"]
  | .inputUndefined => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_emit_eval_unchecked_mode_v1"]
  | .inputHole => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_emit_eval_unchecked_mode_v1"]
  | .inputChecked => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_expected_is_closed_v1",
      "cetta_petta_call_guard_emit_eval_checked_mode_v1"]
  | .inputOpen => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_expected_is_closed_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .resultUndefined => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_emit_result_unchecked_mode_v1"]
  | .resultHole => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_emit_result_unchecked_mode_v1"]
  | .resultAtom => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_emit_result_unchecked_mode_v1"]
  | .resultChecked => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_closed_v1",
      "cetta_petta_call_guard_emit_result_checked_mode_v1"]
  | .resultOpen => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_expected_is_undefined_v1",
      "cetta_petta_call_guard_expected_is_hole_v1",
      "cetta_petta_call_guard_expected_is_atom_v1",
      "cetta_petta_call_guard_expected_is_closed_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .emit => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_emit_plan_v1",
      "cetta_petta_call_guard_advance_declaration_v1"]
  | .outsideFragment => ["cetta_petta_call_guard_compile_state_tag_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .halted | .unknown => ["cetta_petta_call_guard_compile_state_tag_v1"]

private def compileStart (_scenario : CompileScenario) : Pattern :=
  run loweredCompileTransitionBody environment readyReceipt

private def compileDone (scenario : CompileScenario) : Pattern :=
  halted (outcomeReturn (valueSymbol scenario.outcome)) environment
    (receipts scenario.hooks)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lowered_compile_transition_one_step_adequate
    (scenario : CompileScenario) :
    normalizeFirstUsing (referenceEnv (compileCatalog scenario))
        Mettapedia.GSLT.LanguageDef.StructuredC.language 1 64 (compileStart scenario) =
      compileDone scenario := by
  cases scenario <;> decide +kernel

/-! ## Complete executor branch catalog -/

inductive ExecuteScenario where
  | authorityCurrent
  | foreignOwner
  | staleRevision
  | wrongHead
  | wrongArity
  | rawAccept
  | rawReject
  | uncheckedArgument
  | exactArgument
  | metatypeArgument
  | rejectedArgument
  | body
  | uncheckedResult
  | exactResult
  | metatypeResult
  | rejectedResult
  | install
  | reject
  | empty
  | done
  | outsideFragment
  | unknown
deriving DecidableEq, Repr

private def ExecuteScenario.tag : ExecuteScenario → String
  | .authorityCurrent | .foreignOwner | .staleRevision | .wrongHead |
      .wrongArity => "CETTA_PETTA_CALL_GUARD_EXECUTE_AUTHORITY_V1"
  | .rawAccept | .rawReject | .uncheckedArgument | .exactArgument |
      .metatypeArgument | .rejectedArgument =>
      "CETTA_PETTA_CALL_GUARD_EXECUTE_ARGUMENT_V1"
  | .body => "CETTA_PETTA_CALL_GUARD_EXECUTE_BODY_V1"
  | .uncheckedResult | .exactResult | .metatypeResult | .rejectedResult =>
      "CETTA_PETTA_CALL_GUARD_EXECUTE_RESULT_V1"
  | .install => "CETTA_PETTA_CALL_GUARD_EXECUTE_INSTALL_V1"
  | .reject => "CETTA_PETTA_CALL_GUARD_EXECUTE_REJECT_V1"
  | .empty => "CETTA_PETTA_CALL_GUARD_EXECUTE_EMPTY_V1"
  | .done => "CETTA_PETTA_CALL_GUARD_EXECUTE_DONE_V1"
  | .outsideFragment => "CETTA_PETTA_CALL_GUARD_EXECUTE_OUTSIDE_V1"
  | .unknown => "CETTA_PETTA_CALL_GUARD_EXECUTE_UNKNOWN_V1"

private def ExecuteScenario.modeTag? : ExecuteScenario → Option String
  | .rawAccept | .rawReject => some "CETTA_PETTA_CALL_GUARD_ARG_RAW_V1"
  | .uncheckedArgument =>
      some "CETTA_PETTA_CALL_GUARD_ARG_EVAL_UNCHECKED_V1"
  | .exactArgument | .metatypeArgument | .rejectedArgument =>
      some "CETTA_PETTA_CALL_GUARD_ARG_EVAL_CHECKED_V1"
  | .uncheckedResult =>
      some "CETTA_PETTA_CALL_GUARD_RESULT_UNCHECKED_V1"
  | .exactResult | .metatypeResult | .rejectedResult =>
      some "CETTA_PETTA_CALL_GUARD_RESULT_CHECKED_V1"
  | _ => none

private def ExecuteScenario.answer
    (scenario : ExecuteScenario) (name : String) : Option Bool :=
  match name with
  | "cetta_petta_call_guard_owner_current_v1" =>
      match scenario with | .foreignOwner => some false | _ => some true
  | "cetta_petta_call_guard_revision_current_v1" =>
      match scenario with | .staleRevision => some false | _ => some true
  | "cetta_petta_call_guard_head_matches_v1" =>
      match scenario with | .wrongHead => some false | _ => some true
  | "cetta_petta_call_guard_arity_matches_v1" =>
      match scenario with | .wrongArity => some false | _ => some true
  | "cetta_petta_call_guard_raw_argument_equal_v1" =>
      match scenario with
      | .rawAccept => some true
      | .rawReject => some false
      | _ => none
  | "cetta_petta_call_guard_get_type_v1" =>
      match scenario with
      | .exactArgument => some true
      | .metatypeArgument | .rejectedArgument => some false
      | _ => none
  | "cetta_petta_call_guard_get_metatype_v1" =>
      match scenario with
      | .metatypeArgument => some true
      | .rejectedArgument => some false
      | _ => none
  | "cetta_petta_call_guard_get_result_type_v1" =>
      match scenario with
      | .exactResult => some true
      | .metatypeResult | .rejectedResult => some false
      | _ => none
  | "cetta_petta_call_guard_get_result_metatype_v1" =>
      match scenario with
      | .metatypeResult => some true
      | .rejectedResult => some false
      | _ => none
  | _ => none

private def executeCatalog (scenario : ExecuteScenario) : PrimitiveCatalog :=
  fun name =>
    if name = "cetta_petta_call_guard_execute_state_tag_v1" then
      some (.value (valueSymbol scenario.tag))
    else if name = "cetta_petta_call_guard_argument_mode_tag_v1" ||
        name = "cetta_petta_call_guard_execution_result_mode_tag_v1" then
      scenario.modeTag?.map fun tag => .value (valueSymbol tag)
    else
      match scenario.answer name with
      | some answer => some (boolResult answer)
      | none => unitOrNone name

private def ExecuteScenario.outcome : ExecuteScenario → String
  | .foreignOwner => "CETTA_PETTA_CALL_GUARD_FALLBACK_FOREIGN_OWNER_V1"
  | .staleRevision => "CETTA_PETTA_CALL_GUARD_FALLBACK_STALE_REVISION_V1"
  | .wrongHead => "CETTA_PETTA_CALL_GUARD_FALLBACK_WRONG_HEAD_V1"
  | .wrongArity => "CETTA_PETTA_CALL_GUARD_FALLBACK_WRONG_ARITY_V1"
  | .rawReject | .rejectedArgument | .rejectedResult | .reject =>
      "CETTA_PETTA_CALL_GUARD_REJECTED_V1"
  | .install => "CETTA_PETTA_CALL_GUARD_INSTALLED_V1"
  | .empty => "CETTA_PETTA_CALL_GUARD_EXECUTED_EMPTY_V1"
  | .done => "CETTA_PETTA_CALL_GUARD_EXECUTED_V1"
  | .outsideFragment =>
      "CETTA_PETTA_CALL_GUARD_FALLBACK_OUTSIDE_FRAGMENT_V1"
  | .unknown => "CETTA_PETTA_CALL_GUARD_ENGINE_FAULT_V1"
  | _ => "CETTA_PETTA_CALL_GUARD_ADVANCED_V1"

private def ExecuteScenario.hooks : ExecuteScenario → List String
  | .authorityCurrent => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_owner_current_v1",
      "cetta_petta_call_guard_revision_current_v1",
      "cetta_petta_call_guard_head_matches_v1",
      "cetta_petta_call_guard_arity_matches_v1",
      "cetta_petta_call_guard_begin_plan_v1"]
  | .foreignOwner => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_owner_current_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .staleRevision => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_owner_current_v1",
      "cetta_petta_call_guard_revision_current_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .wrongHead => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_owner_current_v1",
      "cetta_petta_call_guard_revision_current_v1",
      "cetta_petta_call_guard_head_matches_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .wrongArity => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_owner_current_v1",
      "cetta_petta_call_guard_revision_current_v1",
      "cetta_petta_call_guard_head_matches_v1",
      "cetta_petta_call_guard_arity_matches_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .rawAccept => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_raw_argument_equal_v1",
      "cetta_petta_call_guard_advance_argument_v1"]
  | .rawReject => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_raw_argument_equal_v1",
      "cetta_petta_call_guard_reject_plan_v1"]
  | .uncheckedArgument => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_evaluate_argument_v1",
      "cetta_petta_call_guard_advance_argument_v1"]
  | .exactArgument => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_evaluate_argument_v1",
      "cetta_petta_call_guard_get_type_v1",
      "cetta_petta_call_guard_advance_argument_v1"]
  | .metatypeArgument => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_evaluate_argument_v1",
      "cetta_petta_call_guard_get_type_v1",
      "cetta_petta_call_guard_get_metatype_v1",
      "cetta_petta_call_guard_advance_argument_v1"]
  | .rejectedArgument => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_argument_mode_tag_v1",
      "cetta_petta_call_guard_evaluate_argument_v1",
      "cetta_petta_call_guard_get_type_v1",
      "cetta_petta_call_guard_get_metatype_v1",
      "cetta_petta_call_guard_reject_plan_v1"]
  | .body => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_evaluate_call_v1",
      "cetta_petta_call_guard_begin_result_v1"]
  | .uncheckedResult => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_execution_result_mode_tag_v1",
      "cetta_petta_call_guard_advance_result_v1"]
  | .exactResult => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_execution_result_mode_tag_v1",
      "cetta_petta_call_guard_get_result_type_v1",
      "cetta_petta_call_guard_advance_result_v1"]
  | .metatypeResult => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_execution_result_mode_tag_v1",
      "cetta_petta_call_guard_get_result_type_v1",
      "cetta_petta_call_guard_get_result_metatype_v1",
      "cetta_petta_call_guard_advance_result_v1"]
  | .rejectedResult => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_execution_result_mode_tag_v1",
      "cetta_petta_call_guard_get_result_type_v1",
      "cetta_petta_call_guard_get_result_metatype_v1",
      "cetta_petta_call_guard_reject_plan_v1"]
  | .install => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_install_occurrence_v1",
      "cetta_petta_call_guard_advance_plan_v1"]
  | .reject => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_reject_plan_v1"]
  | .outsideFragment => ["cetta_petta_call_guard_execute_state_tag_v1",
      "cetta_petta_call_guard_record_fallback_v1"]
  | .empty | .done | .unknown =>
      ["cetta_petta_call_guard_execute_state_tag_v1"]

private def executeStart (_scenario : ExecuteScenario) : Pattern :=
  run loweredExecuteTransitionBody environment readyReceipt

private def executeDone (scenario : ExecuteScenario) : Pattern :=
  halted (outcomeReturn (valueSymbol scenario.outcome)) environment
    (receipts scenario.hooks)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem lowered_execute_transition_one_step_adequate
    (scenario : ExecuteScenario) :
    normalizeFirstUsing (referenceEnv (executeCatalog scenario))
        Mettapedia.GSLT.LanguageDef.StructuredC.language 1 256 (executeStart scenario) =
      executeDone scenario := by
  cases scenario <;> decide +kernel

/-! ## Fault, stuckness, and receipt canaries -/

private inductive FaultClass where
  | language
  | engine
  | resource
deriving DecidableEq, Repr

private def FaultClass.pattern : FaultClass → Pattern
  | .language => sc "structured-c:fault-language" [token "primitive"]
  | .engine => sc "structured-c:fault-engine" [token "primitive"]
  | .resource => sc "structured-c:fault-resource" [token "primitive"]

private def faultCatalog (faultClass : FaultClass) : PrimitiveCatalog :=
  fun name =>
    if name = "cetta_petta_call_guard_execute_state_tag_v1" then
      some (.fault faultClass.pattern)
    else none

private def faultDone (faultClass : FaultClass) : Pattern :=
  halted (outcomeFault faultClass.pattern) environment
    (hookReceipt "cetta_petta_call_guard_execute_state_tag_v1" readyReceipt)

set_option maxRecDepth 100000 in
theorem primitive_fault_classes_remain_distinct (faultClass : FaultClass) :
    normalizeFirstUsing (referenceEnv (faultCatalog faultClass))
        Mettapedia.GSLT.LanguageDef.StructuredC.language 1 4 (executeStart .done) = faultDone faultClass := by
  cases faultClass <;> decide +kernel

theorem language_engine_resource_faults_pairwise_distinct :
    faultDone .language ≠ faultDone .engine ∧
      faultDone .language ≠ faultDone .resource ∧
      faultDone .engine ≠ faultDone .resource := by
  decide +kernel

theorem exact_success_receipt_has_no_metatype :
    (ExecuteScenario.exactArgument.hooks.contains
      "cetta_petta_call_guard_get_metatype_v1") = false := by
  decide

theorem metatype_receipt_places_exact_query_first :
    ExecuteScenario.metatypeArgument.hooks =
      ["cetta_petta_call_guard_execute_state_tag_v1",
       "cetta_petta_call_guard_argument_mode_tag_v1",
       "cetta_petta_call_guard_evaluate_argument_v1",
       "cetta_petta_call_guard_get_type_v1",
       "cetta_petta_call_guard_get_metatype_v1",
       "cetta_petta_call_guard_advance_argument_v1"] := by
  rfl

theorem missing_compile_handler_is_stuck :
    rewriteAt (engineBasePremises RelationEnv.empty) Mettapedia.GSLT.LanguageDef.StructuredC.language 1
      (compileStart .finish) = [] := by
  decide +kernel

theorem missing_execute_handler_is_stuck :
    rewriteAt (engineBasePremises RelationEnv.empty) Mettapedia.GSLT.LanguageDef.StructuredC.language 1
      (executeStart .done) = [] := by
  decide +kernel

theorem compile_done_has_no_reducts (scenario : CompileScenario) :
    rewriteAt (engineBasePremises (referenceEnv (compileCatalog scenario)))
      Mettapedia.GSLT.LanguageDef.StructuredC.language 1 (compileDone scenario) = [] := by
  simpa [compileDone] using halted_rewriteAt_empty
    (referenceEnv (compileCatalog scenario))
    (outcomeReturn (valueSymbol scenario.outcome)) environment
    (receipts scenario.hooks)

theorem execute_done_has_no_reducts (scenario : ExecuteScenario) :
    rewriteAt (engineBasePremises (referenceEnv (executeCatalog scenario)))
      Mettapedia.GSLT.LanguageDef.StructuredC.language 1 (executeDone scenario) = [] := by
  simpa [executeDone] using halted_rewriteAt_empty
    (referenceEnv (executeCatalog scenario))
    (outcomeReturn (valueSymbol scenario.outcome)) environment
    (receipts scenario.hooks)

theorem compile_outcome_receipt_no_invention
    (scenario : CompileScenario) (outcome finalEnvironment finalReceipt : Pattern)
    (execution : normalizeFirstUsing (referenceEnv (compileCatalog scenario))
        Mettapedia.GSLT.LanguageDef.StructuredC.language 1 64 (compileStart scenario) =
      halted outcome finalEnvironment finalReceipt) :
    outcome = outcomeReturn (valueSymbol scenario.outcome) ∧
      finalEnvironment = environment ∧ finalReceipt = receipts scenario.hooks := by
  rw [lowered_compile_transition_one_step_adequate] at execution
  unfold compileDone halted at execution
  have argumentsExact := (Pattern.apply.inj execution).2
  have outcomeExact := (List.cons.inj argumentsExact)
  have environmentExact := (List.cons.inj outcomeExact.2)
  have receiptExact := (List.cons.inj environmentExact.2)
  exact ⟨outcomeExact.1.symm, environmentExact.1.symm,
    receiptExact.1.symm⟩

theorem execute_outcome_receipt_no_invention
    (scenario : ExecuteScenario) (outcome finalEnvironment finalReceipt : Pattern)
    (execution : normalizeFirstUsing (referenceEnv (executeCatalog scenario))
        Mettapedia.GSLT.LanguageDef.StructuredC.language 1 256 (executeStart scenario) =
      halted outcome finalEnvironment finalReceipt) :
    outcome = outcomeReturn (valueSymbol scenario.outcome) ∧
      finalEnvironment = environment ∧ finalReceipt = receipts scenario.hooks := by
  rw [lowered_execute_transition_one_step_adequate] at execution
  unfold executeDone halted at execution
  have argumentsExact := (Pattern.apply.inj execution).2
  have outcomeExact := (List.cons.inj argumentsExact)
  have environmentExact := (List.cons.inj outcomeExact.2)
  have receiptExact := (List.cons.inj environmentExact.2)
  exact ⟨outcomeExact.1.symm, environmentExact.1.symm,
    receiptExact.1.symm⟩

/-! ## Generic target semantic model and exact G2 agreement -/

def targetCompileArgMode (expected : Term) : Option ArgMode :=
  if expected == atomType then some .rawAtom
  else if expected == undefinedType then some .evalUnchecked
  else if expected == holeType then some .evalUnchecked
  else if termIsClosed expected then some (.evalSoftcutType expected)
  else none

def targetCompileResultMode (expected : Term) : Option ResultMode :=
  if expected == undefinedType then some .resultUnchecked
  else if expected == holeType then some .resultUnchecked
  else if expected == atomType then some .resultUnchecked
  else if termIsClosed expected then some (.resultSoftcutType expected)
  else none

def targetCompileArgumentModes : List Term → Option (List ArgMode)
  | [] => some []
  | expected :: rest => do
      let mode ← targetCompileArgMode expected
      let modes ← targetCompileArgumentModes rest
      pure (mode :: modes)

def targetCompileGuard (declaration : ArrowDeclaration) : Option GuardPlan := do
  let argumentModes ← targetCompileArgumentModes declaration.inputTypes
  let resultMode ← targetCompileResultMode declaration.outputType
  pure {
    declarationOccurrence := declaration.occurrence
    argumentModes := argumentModes
    resultMode := resultMode
    declaration := declaration }

def targetCompileRelevant (owner : SpaceOwner) (revision : Nat)
    (head : String) (arity : Nat) :
    List ArrowDeclaration → CompilationResult :=
  List.foldr (fun declaration suffix =>
    if Relevant declaration head arity then
      match targetCompileGuard declaration with
      | none => .outsideFragment
      | some plan =>
          match suffix with
          | .outsideFragment => .outsideFragment
          | .compiled family =>
              .compiled { family with plans := plan :: family.plans }
    else
      suffix) (.compiled ⟨owner, revision, head, arity, []⟩)

def targetCompileGuards (owned : OwnedSnapshot)
    (head : String) (arity : Nat) : CompilationResult :=
  targetCompileRelevant owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations

theorem targetCompileArgMode_exact (expected : Term) :
    targetCompileArgMode expected = compileArgMode expected := by
  by_cases atom : expected = atomType
  · simp [targetCompileArgMode, compileArgMode, atom]
  · by_cases undefined : expected = undefinedType
    · simp [targetCompileArgMode, compileArgMode, undefined]
    · by_cases hole : expected = holeType
      · simp [targetCompileArgMode, compileArgMode, hole]
      · simp [targetCompileArgMode, compileArgMode, atom, undefined, hole]

theorem targetCompileResultMode_exact (expected : Term) :
    targetCompileResultMode expected = compileResultMode expected := by
  by_cases undefined : expected = undefinedType
  · simp [targetCompileResultMode, compileResultMode, undefined]
  · by_cases hole : expected = holeType
    · simp [targetCompileResultMode, compileResultMode, hole]
    · by_cases atom : expected = atomType
      · simp [targetCompileResultMode, compileResultMode, atom]
      · simp [targetCompileResultMode, compileResultMode, undefined, hole,
          atom]

theorem targetCompileArgumentModes_exact (expected : List Term) :
    targetCompileArgumentModes expected = compileArgumentModes expected := by
  induction expected with
  | nil => rfl
  | cons one rest inductionHypothesis =>
      simp [targetCompileArgumentModes, compileArgumentModes,
        targetCompileArgMode_exact, inductionHypothesis]

theorem targetCompileGuard_exact (declaration : ArrowDeclaration) :
    targetCompileGuard declaration = compileGuard declaration := by
  simp [targetCompileGuard, compileGuard, targetCompileArgumentModes_exact,
    targetCompileResultMode_exact]

theorem targetCompileRelevant_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declarations : List ArrowDeclaration) :
    targetCompileRelevant owner revision head arity declarations =
      compileRelevantGuards owner revision head arity declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations inductionHypothesis =>
      change
        (if Relevant declaration head arity then
          match targetCompileGuard declaration with
          | none => .outsideFragment
          | some plan =>
              match targetCompileRelevant owner revision head arity
                  declarations with
              | .outsideFragment => .outsideFragment
              | .compiled family =>
                  .compiled { family with plans := plan :: family.plans }
        else targetCompileRelevant owner revision head arity declarations) =
        (if Relevant declaration head arity then
          match compileGuard declaration with
          | none => .outsideFragment
          | some plan =>
              match compileRelevantGuards owner revision head arity
                  declarations with
              | .outsideFragment => .outsideFragment
              | .compiled family =>
                  .compiled { family with plans := plan :: family.plans }
        else compileRelevantGuards owner revision head arity declarations)
      rw [targetCompileGuard_exact, inductionHypothesis]

theorem independent_target_compilation_exact
    (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    targetCompileGuards owned head arity = compileGuards owned head arity := by
  exact targetCompileRelevant_exact _ _ _ _ _

/-! ## Concrete external compiler state and hook simulation

`StructuredC` models the C expression and statement control directly.  The
state pointer mutated by external calls is intentionally opaque to that core
language, so the C-facing semantics is the product of the StructuredC step and
the following concrete hook state.  In particular, emitting a plan and
advancing the declaration cursor are separate mutations.
-/

inductive LoweredCompileTargetState where
  | inspect
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
  | input
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
      (accepted : List GuardPlan) (expected : Term)
      (remainingInputs : List Term) (argumentModes : List ArgMode)
  | result
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
      (accepted : List GuardPlan) (argumentModes : List ArgMode)
  | emit
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
      (plan : GuardPlan)
  /-- Internal ABI state after `emit_plan` and before `advance_declaration`. -/
  | emitted
      (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
      (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
  | halted (result : CompilationResult)
deriving DecidableEq, Repr

def loweredCompileTargetStart (owned : OwnedSnapshot)
    (head : String) (arity : Nat) : LoweredCompileTargetState :=
  .inspect owned.owner owned.snapshot.revision head arity
    owned.snapshot.declarations []

private def compileTargetBegin
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) : LoweredCompileTargetState :=
  match declaration.inputTypes with
  | [] => .result owner revision head arity declaration remaining accepted []
  | expected :: remainingInputs =>
      .input owner revision head arity declaration remaining accepted expected
        remainingInputs []

private def compileTargetAfterInput
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (remainingInputs : List Term)
    (argumentModes : List ArgMode) : LoweredCompileTargetState :=
  match remainingInputs with
  | [] =>
      .result owner revision head arity declaration remaining accepted
        argumentModes
  | expected :: rest =>
      .input owner revision head arity declaration remaining accepted expected
        rest argumentModes

def directCompileTargetStep? :
    LoweredCompileTargetState → Option LoweredCompileTargetState
  | .inspect owner revision head arity [] accepted =>
      some (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))
  | .inspect owner revision head arity (declaration :: remaining) accepted =>
      if Relevant declaration head arity then
        some (compileTargetBegin owner revision head arity declaration remaining
          accepted)
      else
        some (.inspect owner revision head arity remaining accepted)
  | .input owner revision head arity declaration remaining accepted expected
      remainingInputs argumentModes =>
      match targetCompileArgMode expected with
      | none => some (.halted .outsideFragment)
      | some mode =>
          some (compileTargetAfterInput owner revision head arity declaration
            remaining accepted remainingInputs (argumentModes ++ [mode]))
  | .result owner revision head arity declaration remaining accepted
      argumentModes =>
      match targetCompileResultMode declaration.outputType with
      | none => some (.halted .outsideFragment)
      | some resultMode =>
          some (.emit owner revision head arity remaining accepted {
            declarationOccurrence := declaration.occurrence
            argumentModes := argumentModes
            resultMode := resultMode
            declaration := declaration })
  | .emit owner revision head arity remaining accepted plan =>
      some (.inspect owner revision head arity remaining (accepted ++ [plan]))
  | .emitted _ _ _ _ _ _ => none
  | .halted _ => none

private def inputCompileScenario (expected : Term) : CompileScenario :=
  if expected = atomType then .inputRaw
  else if expected = undefinedType then .inputUndefined
  else if expected = holeType then .inputHole
  else if termIsClosed expected then .inputChecked
  else .inputOpen

private def resultCompileScenario (expected : Term) : CompileScenario :=
  if expected = undefinedType then .resultUndefined
  else if expected = holeType then .resultHole
  else if expected = atomType then .resultAtom
  else if termIsClosed expected then .resultChecked
  else .resultOpen

private def compileTargetScenario? :
    LoweredCompileTargetState → Option CompileScenario
  | .inspect _ _ _ _ [] _ => some .finish
  | .inspect _ _ head arity (declaration :: _) _ =>
      some (if Relevant declaration head arity then
        .inspectRelevant else .inspectIrrelevant)
  | .input _ _ _ _ _ _ _ expected _ _ => some (inputCompileScenario expected)
  | .result _ _ _ _ declaration _ _ _ =>
      some (resultCompileScenario declaration.outputType)
  | .emit _ _ _ _ _ _ _ => some .emit
  | .emitted _ _ _ _ _ _ | .halted _ => none

private def compileReadHook (name : String) : Bool :=
  name = "cetta_petta_call_guard_compile_state_tag_v1" ||
    name = "cetta_petta_call_guard_declaration_relevant_v1" ||
    name = "cetta_petta_call_guard_expected_is_atom_v1" ||
    name = "cetta_petta_call_guard_expected_is_undefined_v1" ||
    name = "cetta_petta_call_guard_expected_is_hole_v1" ||
    name = "cetta_petta_call_guard_expected_is_closed_v1"

private def applyCompileTargetHook
    (state : LoweredCompileTargetState) (name : String) :
    Option LoweredCompileTargetState :=
  if compileReadHook name then some state else
  match name, state with
  | "cetta_petta_call_guard_begin_mode_compilation_v1",
      .inspect owner revision head arity (declaration :: remaining) accepted =>
      if Relevant declaration head arity then
        some (compileTargetBegin owner revision head arity declaration remaining
          accepted)
      else none
  | "cetta_petta_call_guard_skip_declaration_v1",
      .inspect owner revision head arity (declaration :: remaining) accepted =>
      if Relevant declaration head arity then none
      else some (.inspect owner revision head arity remaining accepted)
  | "cetta_petta_call_guard_emit_raw_mode_v1",
      .input owner revision head arity declaration remaining accepted expected
        remainingInputs argumentModes =>
      if targetCompileArgMode expected = some .rawAtom then
        some (compileTargetAfterInput owner revision head arity declaration
          remaining accepted remainingInputs (argumentModes ++ [.rawAtom]))
      else none
  | "cetta_petta_call_guard_emit_eval_unchecked_mode_v1",
      .input owner revision head arity declaration remaining accepted expected
        remainingInputs argumentModes =>
      if targetCompileArgMode expected = some .evalUnchecked then
        some (compileTargetAfterInput owner revision head arity declaration
          remaining accepted remainingInputs
          (argumentModes ++ [.evalUnchecked]))
      else none
  | "cetta_petta_call_guard_emit_eval_checked_mode_v1",
      .input owner revision head arity declaration remaining accepted expected
        remainingInputs argumentModes =>
      match targetCompileArgMode expected with
      | some (.evalSoftcutType checked) =>
          some (compileTargetAfterInput owner revision head arity declaration
            remaining accepted remainingInputs
            (argumentModes ++ [.evalSoftcutType checked]))
      | _ => none
  | "cetta_petta_call_guard_emit_result_unchecked_mode_v1",
      .result owner revision head arity declaration remaining accepted
        argumentModes =>
      if targetCompileResultMode declaration.outputType =
          some .resultUnchecked then
        some (.emit owner revision head arity remaining accepted {
          declarationOccurrence := declaration.occurrence
          argumentModes := argumentModes
          resultMode := .resultUnchecked
          declaration := declaration })
      else none
  | "cetta_petta_call_guard_emit_result_checked_mode_v1",
      .result owner revision head arity declaration remaining accepted
        argumentModes =>
      match targetCompileResultMode declaration.outputType with
      | some (.resultSoftcutType checked) =>
          some (.emit owner revision head arity remaining accepted {
            declarationOccurrence := declaration.occurrence
            argumentModes := argumentModes
            resultMode := .resultSoftcutType checked
            declaration := declaration })
      | _ => none
  | "cetta_petta_call_guard_emit_plan_v1",
      .emit owner revision head arity remaining accepted plan =>
      some (.emitted owner revision head arity remaining (accepted ++ [plan]))
  | "cetta_petta_call_guard_advance_declaration_v1",
      .emitted owner revision head arity remaining accepted =>
      some (.inspect owner revision head arity remaining accepted)
  | "cetta_petta_call_guard_finish_compiled_family_v1",
      .inspect owner revision head arity [] accepted =>
      some (.halted (.compiled ⟨owner, revision, head, arity, accepted⟩))
  | "cetta_petta_call_guard_record_fallback_v1", .input _ _ _ _ _ _ _ _ _ _ =>
      some (.halted .outsideFragment)
  | "cetta_petta_call_guard_record_fallback_v1", .result _ _ _ _ _ _ _ _ =>
      some (.halted .outsideFragment)
  | _, _ => none

private def runCompileTargetHooks :
    LoweredCompileTargetState → List String → Option LoweredCompileTargetState
  | state, [] => some state
  | state, hook :: hooks => do
      let next ← applyCompileTargetHook state hook
      runCompileTargetHooks next hooks

def loweredCompileTargetStep?
    (state : LoweredCompileTargetState) : Option LoweredCompileTargetState := do
  let scenario ← compileTargetScenario? state
  runCompileTargetHooks state scenario.hooks

set_option maxHeartbeats 4000000 in
theorem loweredCompileTargetStep_exact
    (state : LoweredCompileTargetState) :
    loweredCompileTargetStep? state = directCompileTargetStep? state := by
  cases state with
  | inspect owner revision head arity remaining accepted =>
      cases remaining with
      | nil => rfl
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity <;>
            simp [loweredCompileTargetStep?, compileTargetScenario?,
              CompileScenario.hooks, runCompileTargetHooks,
              applyCompileTargetHook, compileReadHook,
              directCompileTargetStep?, relevant]
  | input owner revision head arity declaration remaining accepted expected
      remainingInputs argumentModes =>
      by_cases atom : expected = atomType
      · simp [loweredCompileTargetStep?, compileTargetScenario?,
          inputCompileScenario, CompileScenario.hooks, runCompileTargetHooks,
          applyCompileTargetHook, compileReadHook, directCompileTargetStep?,
          targetCompileArgMode, atom]
      · by_cases undefined : expected = undefinedType
        · have undefined_ne_atom : undefinedType ≠ atomType := by decide
          simp [loweredCompileTargetStep?, compileTargetScenario?,
            inputCompileScenario, CompileScenario.hooks, runCompileTargetHooks,
            applyCompileTargetHook, compileReadHook, directCompileTargetStep?,
            targetCompileArgMode, undefined, undefined_ne_atom]
        · by_cases hole : expected = holeType
          · have hole_ne_atom : holeType ≠ atomType := by decide
            have hole_ne_undefined : holeType ≠ undefinedType := by decide
            simp [loweredCompileTargetStep?, compileTargetScenario?,
              inputCompileScenario, CompileScenario.hooks,
              runCompileTargetHooks, applyCompileTargetHook, compileReadHook,
              directCompileTargetStep?, targetCompileArgMode, hole,
              hole_ne_atom, hole_ne_undefined]
          · cases closed : termIsClosed expected <;>
              simp [loweredCompileTargetStep?, compileTargetScenario?,
                inputCompileScenario, CompileScenario.hooks,
                runCompileTargetHooks, applyCompileTargetHook, compileReadHook,
                directCompileTargetStep?, targetCompileArgMode, atom,
                undefined, hole, closed]
  | result owner revision head arity declaration remaining accepted
      argumentModes =>
      by_cases undefined : declaration.outputType = undefinedType
      · have undefined_ne_hole : undefinedType ≠ holeType := by decide
        have undefined_ne_atom : undefinedType ≠ atomType := by decide
        simp [loweredCompileTargetStep?, compileTargetScenario?,
          resultCompileScenario, CompileScenario.hooks, runCompileTargetHooks,
          applyCompileTargetHook, compileReadHook, directCompileTargetStep?,
          targetCompileResultMode, undefined, undefined_ne_hole,
          undefined_ne_atom]
      · by_cases hole : declaration.outputType = holeType
        · have hole_ne_undefined : holeType ≠ undefinedType := by decide
          have hole_ne_atom : holeType ≠ atomType := by decide
          simp [loweredCompileTargetStep?, compileTargetScenario?,
            resultCompileScenario, CompileScenario.hooks,
            runCompileTargetHooks, applyCompileTargetHook, compileReadHook,
            directCompileTargetStep?, targetCompileResultMode, hole,
            hole_ne_undefined, hole_ne_atom]
        · by_cases atom : declaration.outputType = atomType
          · have atom_ne_undefined : atomType ≠ undefinedType := by decide
            have atom_ne_hole : atomType ≠ holeType := by decide
            simp [loweredCompileTargetStep?, compileTargetScenario?,
              resultCompileScenario, CompileScenario.hooks,
              runCompileTargetHooks, applyCompileTargetHook, compileReadHook,
              directCompileTargetStep?, targetCompileResultMode, atom,
              atom_ne_undefined, atom_ne_hole]
          · cases closed : termIsClosed declaration.outputType <;>
              simp [loweredCompileTargetStep?, compileTargetScenario?,
                resultCompileScenario, CompileScenario.hooks,
                runCompileTargetHooks, applyCompileTargetHook, compileReadHook,
                directCompileTargetStep?, targetCompileResultMode, undefined,
                hole, atom, closed]
  | emit owner revision head arity remaining accepted plan => rfl
  | emitted owner revision head arity remaining accepted => rfl
  | halted result => rfl

theorem lowered_compile_target_step_simulates
    (state next : LoweredCompileTargetState)
    (step : loweredCompileTargetStep? state = some next) :
    ∃ scenario,
      compileTargetScenario? state = some scenario ∧
      normalizeFirstUsing (referenceEnv (compileCatalog scenario))
          Mettapedia.GSLT.LanguageDef.StructuredC.language 1 64
          (compileStart scenario) = compileDone scenario ∧
      directCompileTargetStep? state = some next := by
  unfold loweredCompileTargetStep? at step
  cases scenarioEq : compileTargetScenario? state with
  | none => simp [scenarioEq] at step
  | some scenario =>
      refine ⟨scenario, rfl,
        lowered_compile_transition_one_step_adequate scenario, ?_⟩
      rw [← loweredCompileTargetStep_exact]
      unfold loweredCompileTargetStep?
      simpa [scenarioEq] using step

theorem omitted_compile_advance_stops_between_plan_and_cursor
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (remaining : List ArrowDeclaration) (accepted : List GuardPlan)
    (plan : GuardPlan) :
    runCompileTargetHooks
        (.emit owner revision head arity remaining accepted plan)
        ["cetta_petta_call_guard_compile_state_tag_v1",
         "cetta_petta_call_guard_emit_plan_v1"] =
      some (.emitted owner revision head arity remaining
        (accepted ++ [plan])) ∧
    runCompileTargetHooks
        (.emit owner revision head arity remaining accepted plan)
        ["cetta_petta_call_guard_compile_state_tag_v1",
         "cetta_petta_call_guard_emit_plan_v1"] ≠
      some (.inspect owner revision head arity remaining
        (accepted ++ [plan])) := by
  simp [runCompileTargetHooks, applyCompileTargetHook, compileReadHook]

def runLoweredCompileTarget :
    Nat → LoweredCompileTargetState → LoweredCompileTargetState
  | 0, state => state
  | fuel + 1, state =>
      match loweredCompileTargetStep? state with
      | none => state
      | some next => runLoweredCompileTarget fuel next

theorem runLoweredCompileTarget_of_no_step
    (fuel : Nat) (state : LoweredCompileTargetState)
    (noStep : loweredCompileTargetStep? state = none) :
    runLoweredCompileTarget fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [runLoweredCompileTarget, noStep]

theorem runLoweredCompileTarget_add
    (first second : Nat) (state : LoweredCompileTargetState) :
    runLoweredCompileTarget (first + second) state =
      runLoweredCompileTarget second (runLoweredCompileTarget first state) := by
  induction first generalizing state with
  | zero => simp [runLoweredCompileTarget]
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, runLoweredCompileTarget]
      cases step : loweredCompileTargetStep? state with
      | none =>
          exact (runLoweredCompileTarget_of_no_step second state step).symm
      | some next =>
          exact inductionHypothesis next

@[simp] theorem runLoweredCompileTarget_halted
    (fuel : Nat) (result : CompilationResult) :
    runLoweredCompileTarget fuel (.halted result) = .halted result := by
  cases fuel <;> rfl

private def compileTargetInputsState
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (expectedTypes : List Term)
    (argumentModes : List ArgMode) : LoweredCompileTargetState :=
  compileTargetAfterInput owner revision head arity declaration remaining
    accepted expectedTypes argumentModes

set_option maxHeartbeats 2000000 in
theorem runLoweredCompileTarget_inputs
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) (expectedTypes : List Term)
    (argumentModes : List ArgMode) :
    match targetCompileArgumentModes expectedTypes with
    | none =>
        runLoweredCompileTarget expectedTypes.length
            (compileTargetInputsState owner revision head arity declaration
              remaining accepted expectedTypes argumentModes) =
          .halted .outsideFragment
    | some compiledModes =>
        runLoweredCompileTarget expectedTypes.length
            (compileTargetInputsState owner revision head arity declaration
              remaining accepted expectedTypes argumentModes) =
          .result owner revision head arity declaration remaining accepted
            (argumentModes ++ compiledModes) := by
  induction expectedTypes generalizing argumentModes with
  | nil => simp [targetCompileArgumentModes, compileTargetInputsState,
      compileTargetAfterInput, runLoweredCompileTarget]
  | cons expected expectedTypes inductionHypothesis =>
      cases modeResult : targetCompileArgMode expected with
      | none =>
          simp [targetCompileArgumentModes, modeResult,
            compileTargetInputsState, compileTargetAfterInput,
            runLoweredCompileTarget, loweredCompileTargetStep_exact,
            directCompileTargetStep?]
      | some mode =>
          cases modesResult : targetCompileArgumentModes expectedTypes with
          | none =>
              simpa [targetCompileArgumentModes, modeResult,
                compileTargetInputsState, compileTargetAfterInput,
                runLoweredCompileTarget, loweredCompileTargetStep_exact,
                directCompileTargetStep?, modesResult] using
                inductionHypothesis (argumentModes ++ [mode])
          | some modes =>
              simpa [targetCompileArgumentModes, modeResult,
                compileTargetInputsState, compileTargetAfterInput,
                runLoweredCompileTarget, loweredCompileTargetStep_exact,
                directCompileTargetStep?, modesResult, List.append_assoc] using
                inductionHypothesis (argumentModes ++ [mode])

def targetCompileOrdered (owner : SpaceOwner) (revision : Nat)
    (head : String) (arity : Nat) (accepted : List GuardPlan) :
    List ArrowDeclaration → CompilationResult
  | [] => .compiled ⟨owner, revision, head, arity, accepted⟩
  | declaration :: remaining =>
      if Relevant declaration head arity then
        match targetCompileGuard declaration with
        | none => .outsideFragment
        | some plan =>
            targetCompileOrdered owner revision head arity
              (accepted ++ [plan]) remaining
      else
        targetCompileOrdered owner revision head arity accepted remaining

theorem targetCompileOrdered_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (accepted : List GuardPlan) (declarations : List ArrowDeclaration) :
    targetCompileOrdered owner revision head arity accepted declarations =
      compileOrdered owner revision head arity accepted declarations := by
  induction declarations generalizing accepted with
  | nil => rfl
  | cons declaration remaining inductionHypothesis =>
      by_cases relevant : Relevant declaration head arity
      · simp only [targetCompileOrdered, relevant, if_pos, compileOrdered]
        rw [targetCompileGuard_exact]
        cases compiled : compileGuard declaration <;>
          simp [inductionHypothesis]
      · simp [targetCompileOrdered, compileOrdered, relevant,
          inductionHypothesis]

def loweredCompileTargetBudget (head : String) (arity : Nat) :
    List ArrowDeclaration → Nat
  | [] => 1
  | declaration :: remaining =>
      if Relevant declaration head arity then
        declaration.inputTypes.length + 3 +
          loweredCompileTargetBudget head arity remaining
      else
        1 + loweredCompileTargetBudget head arity remaining

set_option maxHeartbeats 4000000 in
theorem runLoweredCompileTarget_inspect_exact
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declarations : List ArrowDeclaration) (accepted : List GuardPlan) :
    runLoweredCompileTarget (loweredCompileTargetBudget head arity declarations)
        (.inspect owner revision head arity declarations accepted) =
      .halted (targetCompileOrdered owner revision head arity accepted
        declarations) := by
  induction declarations generalizing accepted with
  | nil => rfl
  | cons declaration remaining inductionHypothesis =>
      by_cases relevant : Relevant declaration head arity
      · have beginStep :
            runLoweredCompileTarget 1
                (.inspect owner revision head arity
                  (declaration :: remaining) accepted) =
              compileTargetInputsState owner revision head arity declaration
                remaining accepted declaration.inputTypes [] := by
          cases inputTypes : declaration.inputTypes <;>
            simp [runLoweredCompileTarget, loweredCompileTargetStep_exact,
              directCompileTargetStep?, compileTargetInputsState,
              compileTargetBegin, compileTargetAfterInput, relevant,
              inputTypes]
        rw [loweredCompileTargetBudget, if_pos relevant]
        rw [show declaration.inputTypes.length + 3 +
              loweredCompileTargetBudget head arity remaining =
            1 + (declaration.inputTypes.length +
              (1 + (1 + loweredCompileTargetBudget head arity remaining))) by
              omega]
        rw [runLoweredCompileTarget_add, beginStep]
        rw [runLoweredCompileTarget_add]
        cases inputModes : targetCompileArgumentModes declaration.inputTypes with
        | none =>
            have inputsRun := runLoweredCompileTarget_inputs owner revision head
              arity declaration remaining accepted declaration.inputTypes []
            simp only [inputModes] at inputsRun
            rw [inputsRun]
            simp [inputModes, targetCompileOrdered, relevant,
              targetCompileGuard]
        | some argumentModes =>
            have inputsRun := runLoweredCompileTarget_inputs owner revision head
              arity declaration remaining accepted declaration.inputTypes []
            simp only [inputModes, List.nil_append] at inputsRun
            rw [inputsRun]
            rw [show 1 + (1 + loweredCompileTargetBudget head arity remaining) =
              1 + (1 + loweredCompileTargetBudget head arity remaining) by rfl]
            rw [runLoweredCompileTarget_add]
            cases resultMode : targetCompileResultMode declaration.outputType with
            | none =>
                simp [runLoweredCompileTarget, loweredCompileTargetStep_exact,
                  directCompileTargetStep?, resultMode, targetCompileOrdered,
                  relevant, targetCompileGuard, inputModes]
            | some mode =>
                simp only [runLoweredCompileTarget,
                  loweredCompileTargetStep_exact, directCompileTargetStep?,
                  resultMode]
                rw [runLoweredCompileTarget_add]
                simp only [runLoweredCompileTarget,
                  loweredCompileTargetStep_exact, directCompileTargetStep?]
                simpa [targetCompileOrdered, relevant, targetCompileGuard,
                  inputModes, resultMode] using
                  inductionHypothesis (accepted ++ [{
                    declarationOccurrence := declaration.occurrence
                    argumentModes := argumentModes
                    resultMode := mode
                    declaration := declaration }])
      · rw [loweredCompileTargetBudget, if_neg relevant]
        rw [runLoweredCompileTarget_add]
        simp only [runLoweredCompileTarget, loweredCompileTargetStep_exact,
          directCompileTargetStep?, relevant, ↓reduceIte]
        simpa [targetCompileOrdered, relevant] using
          inductionHypothesis accepted

theorem repeated_lowered_compile_transitions_normalize_exactly
    (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    runLoweredCompileTarget
        (loweredCompileTargetBudget head arity owned.snapshot.declarations)
        (loweredCompileTargetStart owned head arity) =
      .halted (compileGuards owned head arity) := by
  unfold loweredCompileTargetStart
  rw [runLoweredCompileTarget_inspect_exact]
  rw [targetCompileOrdered_exact]
  unfold compileGuards
  rw [compileOrdered_eq_reference]
  cases result : compileRelevantGuards owned.owner owned.snapshot.revision
      head arity owned.snapshot.declarations with
  | outsideFragment => rfl
  | compiled family => cases family; simp

def targetArgAccepts (snapshot : Snapshot) (mode : ArgMode)
    (source value : Term) : Bool :=
  match mode with
  | .rawAtom => decide (value = source)
  | .evalUnchecked => true
  | .evalSoftcutType expected =>
      getTypeDecision snapshot value expected ||
        (!getTypeDecision snapshot value expected &&
          getMetatypeDecision snapshot value expected)

def targetArgumentsAccept (snapshot : Snapshot) :
    List ArgMode → List Term → List Term → Bool
  | [], [], [] => true
  | mode :: modes, source :: sources, value :: values =>
      targetArgAccepts snapshot mode source value &&
        targetArgumentsAccept snapshot modes sources values
  | _, _, _ => false

def targetResultAccepts (snapshot : Snapshot) (mode : ResultMode)
    (value : Term) : Bool :=
  match mode with
  | .resultUnchecked => true
  | .resultSoftcutType expected =>
      getTypeDecision snapshot value expected ||
        (!getTypeDecision snapshot value expected &&
          getMetatypeDecision snapshot value expected)

def targetPlanAccepts (snapshot : Snapshot) (call : Call)
    (plan : GuardPlan) : Bool :=
  decide (plan.declaration.function = call.function) &&
    targetArgumentsAccept snapshot plan.argumentModes
      call.sourceArguments call.evaluatedArguments &&
    targetResultAccepts snapshot plan.resultMode call.result

def targetExecutePlans (snapshot : Snapshot) (call : Call) :
    List GuardPlan → List ArrowDeclaration :=
  List.filterMap fun plan =>
    if targetPlanAccepts snapshot call plan then some plan.declaration else none

def targetExecuteFamily (current : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) : GuardExecution :=
  if family.owner = current.owner then
    if family.revision = current.snapshot.revision then
      if family.head = call.function then
        if family.arity = call.sourceArguments.length then
          .executed (targetExecutePlans current.snapshot call family.plans)
        else .fallback .wrongArity
      else .fallback .wrongHead
    else .fallback .staleRevision
  else .fallback .foreignOwner

def targetExecuteCompilation (current : OwnedSnapshot) (call : Call) :
    CompilationResult → GuardExecution
  | .outsideFragment => .fallback .outsideFragment
  | .compiled family => targetExecuteFamily current call family

theorem targetArgAccepts_eq_runArgMode
    (snapshot : Snapshot) (index : Nat) (mode : ArgMode)
    (source value : Term) :
    targetArgAccepts snapshot mode source value =
      (runArgMode snapshot index mode source value).accepted := by
  cases mode with
  | rawAtom => simp [targetArgAccepts, runArgMode]
  | evalUnchecked => rfl
  | evalSoftcutType expected =>
      by_cases exact : getTypeDecision snapshot value expected = true
      · simp [targetArgAccepts, runArgMode, exact]
      · simp [targetArgAccepts, runArgMode, exact]

theorem targetArgumentsAccept_eq_runArguments
    (snapshot : Snapshot) (index : Nat) (modes : List ArgMode)
    (sources values : List Term) :
    targetArgumentsAccept snapshot modes sources values =
      (runArguments snapshot index modes sources values).accepted := by
  induction modes generalizing index sources values with
  | nil => cases sources <;> cases values <;> simp [targetArgumentsAccept,
      runArguments]
  | cons mode modes inductionHypothesis =>
      cases sources with
      | nil => cases values <;> simp [targetArgumentsAccept, runArguments]
      | cons source sources =>
          cases values with
          | nil => simp [targetArgumentsAccept, runArguments]
          | cons value values =>
              rw [targetArgumentsAccept, targetArgAccepts_eq_runArgMode]
              cases current : runArgMode snapshot index mode source value
              rename_i accepted events
              by_cases acceptedTrue : accepted = true
              · simp [runArguments, current, acceptedTrue]
                exact inductionHypothesis (index + 1) sources values
              · have acceptedFalse : accepted = false :=
                  Bool.eq_false_of_not_eq_true acceptedTrue
                simp [runArguments, current, acceptedFalse]

theorem targetResultAccepts_eq_runResultMode
    (snapshot : Snapshot) (mode : ResultMode) (value : Term) :
    targetResultAccepts snapshot mode value =
      (runResultMode snapshot mode value).accepted := by
  cases mode with
  | resultUnchecked => rfl
  | resultSoftcutType expected =>
      by_cases exact : getTypeDecision snapshot value expected = true
      · simp [targetResultAccepts, runResultMode, exact]
      · simp [targetResultAccepts, runResultMode, exact]

theorem targetPlanAccepts_eq_runPlan
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan) :
    targetPlanAccepts snapshot call plan =
      (runPlan snapshot call plan).accepted := by
  unfold targetPlanAccepts
  rw [targetArgumentsAccept_eq_runArguments,
    targetResultAccepts_eq_runResultMode]
  by_cases head : plan.declaration.function = call.function
  · simp only [head, decide_true, Bool.true_and]
    cases arguments : runArguments snapshot 0 plan.argumentModes
      call.sourceArguments call.evaluatedArguments
    cases result : runResultMode snapshot plan.resultMode call.result
    rename_i argumentAccepted argumentEvents resultAccepted resultEvents
    cases argumentAccepted <;> cases resultAccepted <;>
      simp [runPlan, head, arguments, result]
  · simp [runPlan, head]

theorem targetPlanAccepts_eq_true_iff
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan) :
    targetPlanAccepts snapshot call plan = true ↔
      plan.Accepts snapshot call := by
  rw [targetPlanAccepts_eq_runPlan]
  exact runPlan_accepted_iff snapshot call plan

theorem targetExecutePlans_cons
    (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (plans : List GuardPlan) :
    targetExecutePlans snapshot call (plan :: plans) =
      if targetPlanAccepts snapshot call plan then
        plan.declaration :: targetExecutePlans snapshot call plans
      else targetExecutePlans snapshot call plans := by
  unfold targetExecutePlans
  rw [List.filterMap_cons]
  by_cases accepted : targetPlanAccepts snapshot call plan = true <;>
    simp [accepted]

theorem targetExecutePlans_exact
    (snapshot : Snapshot) (call : Call) (plans : List GuardPlan) :
    targetExecutePlans snapshot call plans = executePlanList snapshot call plans := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      rw [targetExecutePlans_cons, executePlanList, inductionHypothesis]
      by_cases accepts : plan.Accepts snapshot call
      · have targetAccepts :=
          (targetPlanAccepts_eq_true_iff snapshot call plan).2 accepts
        simp [accepts, targetAccepts]
      · have targetRejects : targetPlanAccepts snapshot call plan = false :=
          Bool.eq_false_of_not_eq_true fun targetAccepts =>
            accepts ((targetPlanAccepts_eq_true_iff snapshot call plan).1
              targetAccepts)
        simp [accepts, targetRejects]

theorem targetExecuteFamily_exact
    (current : OwnedSnapshot) (call : Call)
    (family : CompiledGuardFamily) :
    targetExecuteFamily current call family =
      executeGuardFamily current call family := by
  by_cases ownerCurrent : family.owner = current.owner
  · by_cases revisionCurrent : family.revision = current.snapshot.revision
    · by_cases headMatches : family.head = call.function
      · by_cases arityMatches : family.arity = call.sourceArguments.length
        · simp [targetExecuteFamily, executeGuardFamily, ownerCurrent,
            revisionCurrent, headMatches, arityMatches,
            targetExecutePlans_exact]
        · simp [targetExecuteFamily, executeGuardFamily, ownerCurrent,
            revisionCurrent, headMatches, arityMatches]
      · simp [targetExecuteFamily, executeGuardFamily, ownerCurrent,
          revisionCurrent, headMatches]
    · simp [targetExecuteFamily, executeGuardFamily, ownerCurrent,
        revisionCurrent]
  · simp [targetExecuteFamily, executeGuardFamily, ownerCurrent]

theorem independent_target_execution_exact
    (current : OwnedSnapshot) (call : Call) (result : CompilationResult) :
    targetExecuteCompilation current call result =
      executeCompilation current call result := by
  cases result with
  | outsideFragment => rfl
  | compiled family => exact targetExecuteFamily_exact current call family

/-! ## Concrete external executor state and hook simulation -/

structure ExecuteTargetFrame where
  current : OwnedSnapshot
  call : Call
  remainingPlans : List GuardPlan
  accepted : List ArrowDeclaration
  events : List ControlEvent
deriving DecidableEq, Repr

inductive LoweredExecuteTargetState where
  | authority
      (current : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
  | argument
      (frame : ExecuteTargetFrame) (plan : GuardPlan) (index : Nat)
      (mode : ArgMode) (remainingModes : List ArgMode)
      (source : Term) (remainingSources : List Term)
      (value : Term) (remainingValues : List Term)
  | body (frame : ExecuteTargetFrame) (plan : GuardPlan)
  | result (frame : ExecuteTargetFrame) (plan : GuardPlan)
  | install (frame : ExecuteTargetFrame) (plan : GuardPlan)
  /-- Internal ABI state after installation and before advancing the plan. -/
  | installed (frame : ExecuteTargetFrame)
  | reject (frame : ExecuteTargetFrame) (plan : GuardPlan)
  | empty (events : List ControlEvent)
  | done (accepted : List ArrowDeclaration) (events : List ControlEvent)
  | outsideFragment (events : List ControlEvent)
  | halted (outcome : GuardExecution) (events : List ControlEvent)
deriving DecidableEq, Repr

def loweredExecuteTargetStart (current : OwnedSnapshot) (call : Call) :
    CompilationResult → LoweredExecuteTargetState
  | .outsideFragment => .outsideFragment []
  | .compiled family => .authority current call family

private def executeTargetArgumentsStart
    (frame : ExecuteTargetFrame) (plan : GuardPlan) (index : Nat) :
    List ArgMode → List Term → List Term → LoweredExecuteTargetState
  | [], [], [] => .body frame plan
  | mode :: modes, source :: sources, value :: values =>
      .argument frame plan index mode modes source sources value values
  | _, _, _ =>
      .reject { frame with events := frame.events ++
        [.argumentShapeMismatch index] } plan

private def executeTargetPlanStart
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    LoweredExecuteTargetState :=
  if plan.declaration.function = frame.call.function then
    executeTargetArgumentsStart frame plan 0 plan.argumentModes
      frame.call.sourceArguments frame.call.evaluatedArguments
  else
    .reject frame plan

private def executeTargetBeginPlan
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    LoweredExecuteTargetState :=
  executeTargetPlanStart { frame with events := frame.events ++
    [.beginPlan plan.declarationOccurrence] } plan

private def executeTargetFirstPlan
    (current : OwnedSnapshot) (call : Call) :
    List GuardPlan → LoweredExecuteTargetState
  | [] => .empty []
  | plan :: remainingPlans =>
      executeTargetBeginPlan {
        current := current
        call := call
        remainingPlans := remainingPlans
        accepted := []
        events := [] } plan

private def executeTargetNextPlan
    (frame : ExecuteTargetFrame) : LoweredExecuteTargetState :=
  match frame.remainingPlans with
  | [] => .done frame.accepted frame.events
  | plan :: remainingPlans =>
      executeTargetBeginPlan {
        frame with
        remainingPlans := remainingPlans
      } plan

private def executeTargetAdvanceArgument
    (frame : ExecuteTargetFrame) (plan : GuardPlan) (index : Nat)
    (remainingModes : List ArgMode) (remainingSources remainingValues : List Term) :
    LoweredExecuteTargetState :=
  executeTargetArgumentsStart frame plan (index + 1) remainingModes
    remainingSources remainingValues

private def executeTargetReject
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    LoweredExecuteTargetState :=
  executeTargetNextPlan { frame with events := frame.events ++
    [.rejectOccurrence plan.declarationOccurrence] }

def directExecuteTargetStep? :
    LoweredExecuteTargetState → Option LoweredExecuteTargetState
  | .authority current call family =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then
            if family.arity = call.sourceArguments.length then
              some (executeTargetFirstPlan current call family.plans)
            else some (.halted (.fallback .wrongArity)
              [.fallback .wrongArity])
          else some (.halted (.fallback .wrongHead) [.fallback .wrongHead])
        else some (.halted (.fallback .staleRevision)
          [.fallback .staleRevision])
      else some (.halted (.fallback .foreignOwner) [.fallback .foreignOwner])
  | .argument frame plan index mode remainingModes source remainingSources value
      remainingValues =>
      match mode with
      | .rawAtom =>
          let observed := { frame with events := frame.events ++
            [.useRawArgument index] }
          if value = source then
            some (executeTargetAdvanceArgument observed plan index remainingModes
              remainingSources remainingValues)
          else some (executeTargetReject observed plan)
      | .evalUnchecked =>
          let observed := { frame with events := frame.events ++
            [.evaluateArgument index] }
          some (executeTargetAdvanceArgument observed plan index remainingModes
            remainingSources remainingValues)
      | .evalSoftcutType expected =>
          let exact := getTypeDecision frame.current.snapshot value expected
          let observed := { frame with events := frame.events ++
            [.evaluateArgument index, .queryExactType index expected exact] }
          if exact then
            some (executeTargetAdvanceArgument observed plan index remainingModes
              remainingSources remainingValues)
          else
            let metatype := getMetatypeDecision frame.current.snapshot value expected
            let observed := { observed with events := observed.events ++
              [.queryMetatype index expected metatype] }
            if metatype then
              some (executeTargetAdvanceArgument observed plan index remainingModes
                remainingSources remainingValues)
            else some (executeTargetReject observed plan)
  | .body frame plan =>
      some (.result { frame with events := frame.events ++
        [.evaluateCall plan.declarationOccurrence] } plan)
  | .result frame plan =>
      match plan.resultMode with
      | .resultUnchecked => some (.install frame plan)
      | .resultSoftcutType expected =>
          let exact := getTypeDecision frame.current.snapshot frame.call.result expected
          let observed := { frame with events := frame.events ++
            [.queryResultType expected exact] }
          if exact then some (.install observed plan)
          else
            let metatype := getMetatypeDecision frame.current.snapshot
              frame.call.result expected
            let observed := { observed with events := observed.events ++
              [.queryResultMetatype expected metatype] }
            if metatype then some (.install observed plan)
            else some (executeTargetReject observed plan)
  | .install frame plan =>
      some (executeTargetNextPlan { frame with
        accepted := frame.accepted ++ [plan.declaration]
        events := frame.events ++
          [.installOccurrence plan.declarationOccurrence] })
  | .reject frame plan => some (executeTargetReject frame plan)
  | .empty events => some (.halted (.executed []) events)
  | .done accepted events => some (.halted (.executed accepted) events)
  | .outsideFragment events =>
      some (.halted (.fallback .outsideFragment)
        (events ++ [.fallback .outsideFragment]))
  | .installed _ | .halted _ _ => none

private def executeTargetScenario? :
    LoweredExecuteTargetState → Option ExecuteScenario
  | .authority current call family =>
      some (if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then
            if family.arity = call.sourceArguments.length then
              .authorityCurrent else .wrongArity
          else .wrongHead
        else .staleRevision
      else .foreignOwner)
  | .argument frame _ _ mode _ source _ value _ =>
      match mode with
      | .rawAtom => some (if value = source then .rawAccept else .rawReject)
      | .evalUnchecked => some .uncheckedArgument
      | .evalSoftcutType expected =>
          some (if getTypeDecision frame.current.snapshot value expected then
            .exactArgument
          else if getMetatypeDecision frame.current.snapshot value expected then
            .metatypeArgument
          else .rejectedArgument)
  | .body _ _ => some .body
  | .result frame plan =>
      match plan.resultMode with
      | .resultUnchecked => some .uncheckedResult
      | .resultSoftcutType expected =>
          some (if getTypeDecision frame.current.snapshot frame.call.result
              expected then .exactResult
            else if getMetatypeDecision frame.current.snapshot frame.call.result
                expected then .metatypeResult
            else .rejectedResult)
  | .install _ _ => some .install
  | .reject _ _ => some .reject
  | .empty _ => some .empty
  | .done _ _ => some .done
  | .outsideFragment _ => some .outsideFragment
  | .installed _ | .halted _ _ => none

private def executeReadHook (name : String) : Bool :=
  name = "cetta_petta_call_guard_execute_state_tag_v1" ||
    name = "cetta_petta_call_guard_owner_current_v1" ||
    name = "cetta_petta_call_guard_revision_current_v1" ||
    name = "cetta_petta_call_guard_head_matches_v1" ||
    name = "cetta_petta_call_guard_arity_matches_v1" ||
    name = "cetta_petta_call_guard_argument_mode_tag_v1" ||
    name = "cetta_petta_call_guard_execution_result_mode_tag_v1"

private def applyExecuteTargetHook
    (state : LoweredExecuteTargetState) (name : String) :
    Option LoweredExecuteTargetState :=
  if executeReadHook name then some state else
  match name, state with
  | "cetta_petta_call_guard_begin_plan_v1", .authority current call family =>
      if family.owner = current.owner ∧
          family.revision = current.snapshot.revision ∧
          family.head = call.function ∧
          family.arity = call.sourceArguments.length then
        some (executeTargetFirstPlan current call family.plans)
      else none
  | "cetta_petta_call_guard_raw_argument_equal_v1",
      .argument frame plan index .rawAtom remainingModes source remainingSources
        value remainingValues =>
      some (.argument { frame with events := frame.events ++
        [.useRawArgument index] } plan index .rawAtom remainingModes source
        remainingSources value remainingValues)
  | "cetta_petta_call_guard_evaluate_argument_v1",
      .argument frame plan index mode remainingModes source remainingSources
        value remainingValues =>
      match mode with
      | .rawAtom => none
      | _ => some (.argument { frame with events := frame.events ++
          [.evaluateArgument index] } plan index mode remainingModes source
          remainingSources value remainingValues)
  | "cetta_petta_call_guard_get_type_v1",
      .argument frame plan index (.evalSoftcutType expected) remainingModes
        source remainingSources value remainingValues =>
      let exact := getTypeDecision frame.current.snapshot value expected
      some (.argument { frame with events := frame.events ++
        [.queryExactType index expected exact] } plan index
        (.evalSoftcutType expected) remainingModes source remainingSources value
        remainingValues)
  | "cetta_petta_call_guard_get_metatype_v1",
      .argument frame plan index (.evalSoftcutType expected) remainingModes
        source remainingSources value remainingValues =>
      let metatype := getMetatypeDecision frame.current.snapshot value expected
      some (.argument { frame with events := frame.events ++
        [.queryMetatype index expected metatype] } plan index
        (.evalSoftcutType expected) remainingModes source remainingSources value
        remainingValues)
  | "cetta_petta_call_guard_advance_argument_v1",
      .argument frame plan index _ remainingModes _ remainingSources _
        remainingValues =>
      some (executeTargetAdvanceArgument frame plan index remainingModes
        remainingSources remainingValues)
  | "cetta_petta_call_guard_reject_plan_v1", .argument frame plan _ _ _ _ _ _ _ =>
      some (executeTargetReject frame plan)
  | "cetta_petta_call_guard_evaluate_call_v1", .body frame plan =>
      some (.body { frame with events := frame.events ++
        [.evaluateCall plan.declarationOccurrence] } plan)
  | "cetta_petta_call_guard_begin_result_v1", .body frame plan =>
      some (.result frame plan)
  | "cetta_petta_call_guard_get_result_type_v1", .result frame plan =>
      match plan.resultMode with
      | .resultUnchecked => none
      | .resultSoftcutType expected =>
          let exact := getTypeDecision frame.current.snapshot frame.call.result
            expected
          some (.result { frame with events := frame.events ++
            [.queryResultType expected exact] } plan)
  | "cetta_petta_call_guard_get_result_metatype_v1", .result frame plan =>
      match plan.resultMode with
      | .resultUnchecked => none
      | .resultSoftcutType expected =>
          let metatype := getMetatypeDecision frame.current.snapshot
            frame.call.result expected
          some (.result { frame with events := frame.events ++
            [.queryResultMetatype expected metatype] } plan)
  | "cetta_petta_call_guard_advance_result_v1", .result frame plan =>
      some (.install frame plan)
  | "cetta_petta_call_guard_reject_plan_v1", .result frame plan =>
      some (executeTargetReject frame plan)
  | "cetta_petta_call_guard_install_occurrence_v1", .install frame plan =>
      some (.installed { frame with
        accepted := frame.accepted ++ [plan.declaration]
        events := frame.events ++
          [.installOccurrence plan.declarationOccurrence] })
  | "cetta_petta_call_guard_advance_plan_v1", .installed frame =>
      some (executeTargetNextPlan frame)
  | "cetta_petta_call_guard_reject_plan_v1", .reject frame plan =>
      some (executeTargetReject frame plan)
  | "cetta_petta_call_guard_record_fallback_v1",
      .authority current call family =>
      if family.owner ≠ current.owner then
        some (.halted (.fallback .foreignOwner) [.fallback .foreignOwner])
      else if family.revision ≠ current.snapshot.revision then
        some (.halted (.fallback .staleRevision) [.fallback .staleRevision])
      else if family.head ≠ call.function then
        some (.halted (.fallback .wrongHead) [.fallback .wrongHead])
      else if family.arity ≠ call.sourceArguments.length then
        some (.halted (.fallback .wrongArity) [.fallback .wrongArity])
      else none
  | "cetta_petta_call_guard_record_fallback_v1", .outsideFragment events =>
      some (.halted (.fallback .outsideFragment)
        (events ++ [.fallback .outsideFragment]))
  | _, _ => none

private def runExecuteTargetHooks :
    LoweredExecuteTargetState → List String → Option LoweredExecuteTargetState
  | state, [] => some state
  | state, hook :: hooks => do
      let next ← applyExecuteTargetHook state hook
      runExecuteTargetHooks next hooks

private def finishExecuteTargetScenario
    (scenario : ExecuteScenario) (state : LoweredExecuteTargetState) :
    LoweredExecuteTargetState :=
  match scenario, state with
  | .empty, .empty events => .halted (.executed []) events
  | .done, .done accepted events => .halted (.executed accepted) events
  | _, _ => state

def loweredExecuteTargetStep?
    (state : LoweredExecuteTargetState) : Option LoweredExecuteTargetState := do
  let scenario ← executeTargetScenario? state
  let next ← runExecuteTargetHooks state scenario.hooks
  pure (finishExecuteTargetScenario scenario next)

set_option maxHeartbeats 12000000 in
theorem loweredExecuteTargetStep_exact (state : LoweredExecuteTargetState) :
    loweredExecuteTargetStep? state = directExecuteTargetStep? state := by
  cases state with
  | authority current call family =>
      by_cases ownerCurrent : family.owner = current.owner
      · by_cases revisionCurrent :
            family.revision = current.snapshot.revision
        · by_cases headMatches : family.head = call.function
          · by_cases arityMatches :
                family.arity = call.sourceArguments.length
            · simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                ownerCurrent, revisionCurrent, headMatches, arityMatches]
            · simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                ownerCurrent, revisionCurrent, headMatches, arityMatches]
          · simp [loweredExecuteTargetStep?, executeTargetScenario?,
              ExecuteScenario.hooks, runExecuteTargetHooks,
              applyExecuteTargetHook, executeReadHook,
              finishExecuteTargetScenario, directExecuteTargetStep?,
              ownerCurrent, revisionCurrent, headMatches]
        · simp [loweredExecuteTargetStep?, executeTargetScenario?,
            ExecuteScenario.hooks, runExecuteTargetHooks,
            applyExecuteTargetHook, executeReadHook,
            finishExecuteTargetScenario, directExecuteTargetStep?,
            ownerCurrent, revisionCurrent]
      · simp [loweredExecuteTargetStep?, executeTargetScenario?,
          ExecuteScenario.hooks, runExecuteTargetHooks,
          applyExecuteTargetHook, executeReadHook,
          finishExecuteTargetScenario, directExecuteTargetStep?, ownerCurrent]
  | argument frame plan index mode remainingModes source remainingSources value
      remainingValues =>
      cases mode with
      | rawAtom =>
          by_cases equal : value = source
          · simp [loweredExecuteTargetStep?, executeTargetScenario?,
              ExecuteScenario.hooks, runExecuteTargetHooks,
              applyExecuteTargetHook, executeReadHook,
              finishExecuteTargetScenario, directExecuteTargetStep?, equal]
          · simp [loweredExecuteTargetStep?, executeTargetScenario?,
              ExecuteScenario.hooks, runExecuteTargetHooks,
              applyExecuteTargetHook, executeReadHook,
              finishExecuteTargetScenario, directExecuteTargetStep?, equal]
      | evalUnchecked =>
          simp [loweredExecuteTargetStep?, executeTargetScenario?,
            ExecuteScenario.hooks, runExecuteTargetHooks,
            applyExecuteTargetHook, executeReadHook,
            finishExecuteTargetScenario, directExecuteTargetStep?]
      | evalSoftcutType expected =>
          by_cases exact :
              getTypeDecision frame.current.snapshot value expected = true
          · simp [loweredExecuteTargetStep?, executeTargetScenario?,
              ExecuteScenario.hooks, runExecuteTargetHooks,
              applyExecuteTargetHook, executeReadHook,
              finishExecuteTargetScenario, directExecuteTargetStep?, exact]
          · have exactFalse :
                getTypeDecision frame.current.snapshot value expected = false :=
              Bool.eq_false_of_not_eq_true exact
            by_cases metatype :
                getMetatypeDecision frame.current.snapshot value expected = true
            · simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                exactFalse, metatype]
            · have metatypeFalse :
                  getMetatypeDecision frame.current.snapshot value expected =
                    false :=
                Bool.eq_false_of_not_eq_true metatype
              simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                exactFalse, metatypeFalse]
  | body frame plan =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | result frame plan =>
      cases resultMode : plan.resultMode with
      | resultUnchecked =>
          simp [loweredExecuteTargetStep?, executeTargetScenario?,
            ExecuteScenario.hooks, runExecuteTargetHooks,
            applyExecuteTargetHook, executeReadHook,
            finishExecuteTargetScenario, directExecuteTargetStep?, resultMode]
      | resultSoftcutType expected =>
          by_cases exact : getTypeDecision frame.current.snapshot
              frame.call.result expected = true
          · simp [loweredExecuteTargetStep?, executeTargetScenario?,
              ExecuteScenario.hooks, runExecuteTargetHooks,
              applyExecuteTargetHook, executeReadHook,
              finishExecuteTargetScenario, directExecuteTargetStep?,
              resultMode, exact]
          · have exactFalse : getTypeDecision frame.current.snapshot
                frame.call.result expected = false :=
              Bool.eq_false_of_not_eq_true exact
            by_cases metatype : getMetatypeDecision frame.current.snapshot
                frame.call.result expected = true
            · simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                resultMode, exactFalse, metatype]
            · have metatypeFalse : getMetatypeDecision frame.current.snapshot
                  frame.call.result expected = false :=
                Bool.eq_false_of_not_eq_true metatype
              simp [loweredExecuteTargetStep?, executeTargetScenario?,
                ExecuteScenario.hooks, runExecuteTargetHooks,
                applyExecuteTargetHook, executeReadHook,
                finishExecuteTargetScenario, directExecuteTargetStep?,
                resultMode, exactFalse, metatypeFalse]
  | install frame plan =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | installed frame =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        directExecuteTargetStep?]
  | reject frame plan =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | empty events =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | done accepted events =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | outsideFragment events =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        ExecuteScenario.hooks, runExecuteTargetHooks, applyExecuteTargetHook,
        executeReadHook, finishExecuteTargetScenario,
        directExecuteTargetStep?]
  | halted outcome events =>
      simp [loweredExecuteTargetStep?, executeTargetScenario?,
        directExecuteTargetStep?]

theorem lowered_execute_target_step_simulates
    (state next : LoweredExecuteTargetState)
    (step : loweredExecuteTargetStep? state = some next) :
    ∃ scenario,
      executeTargetScenario? state = some scenario ∧
      normalizeFirstUsing (referenceEnv (executeCatalog scenario))
          Mettapedia.GSLT.LanguageDef.StructuredC.language 1 256
          (executeStart scenario) = executeDone scenario ∧
      directExecuteTargetStep? state = some next := by
  unfold loweredExecuteTargetStep? at step
  cases scenarioEq : executeTargetScenario? state with
  | none => simp [scenarioEq] at step
  | some scenario =>
      refine ⟨scenario, rfl,
        lowered_execute_transition_one_step_adequate scenario, ?_⟩
      rw [← loweredExecuteTargetStep_exact]
      unfold loweredExecuteTargetStep?
      simpa [scenarioEq] using step

def runLoweredExecuteTarget :
    Nat → LoweredExecuteTargetState → LoweredExecuteTargetState
  | 0, state => state
  | fuel + 1, state =>
      match loweredExecuteTargetStep? state with
      | none => state
      | some next => runLoweredExecuteTarget fuel next

theorem runLoweredExecuteTarget_of_no_step
    (fuel : Nat) (state : LoweredExecuteTargetState)
    (noStep : loweredExecuteTargetStep? state = none) :
    runLoweredExecuteTarget fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [runLoweredExecuteTarget, noStep]

theorem runLoweredExecuteTarget_add
    (first second : Nat) (state : LoweredExecuteTargetState) :
    runLoweredExecuteTarget (first + second) state =
      runLoweredExecuteTarget second (runLoweredExecuteTarget first state) := by
  induction first generalizing state with
  | zero => simp [runLoweredExecuteTarget]
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, runLoweredExecuteTarget]
      cases step : loweredExecuteTargetStep? state with
      | none =>
          rw [runLoweredExecuteTarget_of_no_step second state step]
      | some next => exact inductionHypothesis next

theorem runLoweredExecuteTarget_succ_of_step
    (fuel : Nat) (state next : LoweredExecuteTargetState)
    (step : loweredExecuteTargetStep? state = some next) :
    runLoweredExecuteTarget (Nat.succ fuel) state =
      runLoweredExecuteTarget fuel next := by
  simp [runLoweredExecuteTarget, step]

@[simp] theorem runLoweredExecuteTarget_halted
    (fuel : Nat) (outcome : GuardExecution) (events : List ControlEvent) :
    runLoweredExecuteTarget fuel (.halted outcome events) =
      .halted outcome events := by
  apply runLoweredExecuteTarget_of_no_step
  rfl

theorem stale_authority_falls_back_and_halts
    (current : OwnedSnapshot) (call : Call) (family : CompiledGuardFamily)
    (ownerCurrent : family.owner = current.owner)
    (revisionStale : family.revision ≠ current.snapshot.revision) :
    loweredExecuteTargetStep? (.authority current call family) =
      some (.halted (.fallback .staleRevision)
        [.fallback .staleRevision]) := by
  rw [loweredExecuteTargetStep_exact]
  simp [directExecuteTargetStep?, ownerCurrent, revisionStale]

theorem fallback_execution_has_no_continuation
    (reason : GuardFallbackReason) (events : List ControlEvent) :
    loweredExecuteTargetStep? (.halted (.fallback reason) events) = none := by
  rfl

theorem install_after_rejection_is_impossible
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    applyExecuteTargetHook (.reject frame plan)
        "cetta_petta_call_guard_install_occurrence_v1" = none := by
  simp [applyExecuteTargetHook, executeReadHook]

theorem omitted_execute_advance_stops_after_install
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    runExecuteTargetHooks (.install frame plan)
        ["cetta_petta_call_guard_execute_state_tag_v1",
         "cetta_petta_call_guard_install_occurrence_v1"] =
      some (.installed { frame with
        accepted := frame.accepted ++ [plan.declaration]
        events := frame.events ++
          [.installOccurrence plan.declarationOccurrence] }) := by
  simp [runExecuteTargetHooks, applyExecuteTargetHook, executeReadHook]

theorem reversed_checked_argument_queries_change_receipt
    (frame : ExecuteTargetFrame) (plan : GuardPlan) (index : Nat)
    (expected source value : Term) (remainingModes : List ArgMode)
    (remainingSources remainingValues : List Term) :
    runExecuteTargetHooks
        (.argument frame plan index (.evalSoftcutType expected)
          remainingModes source remainingSources value remainingValues)
        ["cetta_petta_call_guard_evaluate_argument_v1",
         "cetta_petta_call_guard_get_metatype_v1",
         "cetta_petta_call_guard_get_type_v1"] ≠
      runExecuteTargetHooks
        (.argument frame plan index (.evalSoftcutType expected)
          remainingModes source remainingSources value remainingValues)
        ["cetta_petta_call_guard_evaluate_argument_v1",
         "cetta_petta_call_guard_get_type_v1",
         "cetta_petta_call_guard_get_metatype_v1"] := by
  simp [runExecuteTargetHooks, applyExecuteTargetHook, executeReadHook]

def loweredArgumentTargetSteps (snapshot : Snapshot) :
    Nat → List ArgMode → List Term → List Term → Nat
  | _, [], [], [] => 0
  | index, mode :: modes, source :: sources, value :: values =>
      let current := runArgMode snapshot index mode source value
      if current.accepted then
        1 + loweredArgumentTargetSteps snapshot (index + 1) modes sources values
      else 1
  | _, _, _, _ => 1

theorem runLoweredExecuteTarget_arguments_exact
    (frame : ExecuteTargetFrame) (plan : GuardPlan) (index : Nat)
    (modes : List ArgMode) (sources values : List Term) :
    let trace := runArguments frame.current.snapshot index modes sources values
    runLoweredExecuteTarget
        (loweredArgumentTargetSteps frame.current.snapshot index modes sources
          values)
        (executeTargetArgumentsStart frame plan index modes sources values) =
      if trace.accepted then
        .body { frame with events := frame.events ++ trace.events } plan
      else
        executeTargetNextPlan { frame with events := frame.events ++
          trace.events ++ [.rejectOccurrence plan.declarationOccurrence] } := by
  induction modes generalizing frame index sources values with
  | nil =>
      cases sources <;> cases values <;>
        simp [loweredArgumentTargetSteps, executeTargetArgumentsStart,
          runArguments, runLoweredExecuteTarget,
          loweredExecuteTargetStep_exact, directExecuteTargetStep?,
          executeTargetReject, List.append_assoc]
  | cons mode modes inductionHypothesis =>
      cases sources with
      | nil =>
          cases values <;>
            simp [loweredArgumentTargetSteps, executeTargetArgumentsStart,
              runArguments, runLoweredExecuteTarget,
              loweredExecuteTargetStep_exact, directExecuteTargetStep?,
              executeTargetReject, List.append_assoc]
      | cons source sources =>
          cases values with
          | nil =>
              simp [loweredArgumentTargetSteps, executeTargetArgumentsStart,
                runArguments, runLoweredExecuteTarget,
                loweredExecuteTargetStep_exact, directExecuteTargetStep?,
                executeTargetReject, List.append_assoc]
          | cons value values =>
              cases mode with
              | rawAtom =>
                  by_cases equal : value = source
                  · simp only [loweredArgumentTargetSteps, runArgMode, equal,
                      decide_true, if_true, runArguments,
                      executeTargetArgumentsStart]
                    rw [Nat.one_add]
                    simp only [runLoweredExecuteTarget]
                    rw [loweredExecuteTargetStep_exact]
                    simp only [directExecuteTargetStep?, if_pos]
                    simp only [executeTargetAdvanceArgument]
                    simpa [List.append_assoc] using
                      (inductionHypothesis
                        { frame with events := frame.events ++
                          [.useRawArgument index] }
                        (index + 1) sources values)
                  · simp [loweredArgumentTargetSteps,
                      executeTargetArgumentsStart, runArguments, runArgMode,
                      equal, runLoweredExecuteTarget,
                      loweredExecuteTargetStep_exact,
                      directExecuteTargetStep?, executeTargetReject,
                      List.append_assoc]
              | evalUnchecked =>
                  simp only [loweredArgumentTargetSteps, runArgMode, if_true,
                    runArguments, executeTargetArgumentsStart]
                  rw [Nat.one_add]
                  simp only [runLoweredExecuteTarget]
                  rw [loweredExecuteTargetStep_exact]
                  simp only [directExecuteTargetStep?]
                  simp only [executeTargetAdvanceArgument]
                  simpa [List.append_assoc] using
                    (inductionHypothesis
                      { frame with events := frame.events ++
                        [.evaluateArgument index] }
                      (index + 1) sources values)
              | evalSoftcutType expected =>
                  by_cases exact : getTypeDecision frame.current.snapshot
                      value expected = true
                  · simp only [loweredArgumentTargetSteps, runArgMode, exact,
                      if_true, runArguments, executeTargetArgumentsStart]
                    rw [Nat.one_add]
                    simp only [runLoweredExecuteTarget]
                    rw [loweredExecuteTargetStep_exact]
                    simp only [directExecuteTargetStep?, exact, if_pos]
                    simp only [executeTargetAdvanceArgument]
                    simpa [List.append_assoc] using
                      (inductionHypothesis
                        { frame with events := frame.events ++
                          [.evaluateArgument index,
                            .queryExactType index expected true] }
                        (index + 1) sources values)
                  · have exactFalse : getTypeDecision frame.current.snapshot
                        value expected = false :=
                      Bool.eq_false_of_not_eq_true exact
                    by_cases metatype : getMetatypeDecision
                        frame.current.snapshot value expected = true
                    · simp [loweredArgumentTargetSteps, runArgMode,
                        exactFalse, metatype, runArguments,
                        executeTargetArgumentsStart]
                      rw [Nat.one_add]
                      simp only [runLoweredExecuteTarget]
                      rw [loweredExecuteTargetStep_exact]
                      simp [directExecuteTargetStep?, exactFalse, metatype]
                      simp only [executeTargetAdvanceArgument]
                      simpa [List.append_assoc] using
                        (inductionHypothesis
                          { frame with events := frame.events ++
                            [.evaluateArgument index,
                              .queryExactType index expected false,
                              .queryMetatype index expected true] }
                          (index + 1) sources values)
                    · have metatypeFalse : getMetatypeDecision
                          frame.current.snapshot value expected = false :=
                        Bool.eq_false_of_not_eq_true metatype
                      simp [loweredArgumentTargetSteps,
                        executeTargetArgumentsStart, runArguments, runArgMode,
                        exactFalse, metatypeFalse, runLoweredExecuteTarget,
                        loweredExecuteTargetStep_exact,
                        directExecuteTargetStep?, executeTargetReject,
                        List.append_assoc]

def loweredResultTargetSteps (snapshot : Snapshot) (mode : ResultMode)
    (value : Term) : Nat :=
  if (runResultMode snapshot mode value).accepted then 2 else 1

theorem runLoweredExecuteTarget_result_exact
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    let trace := runResultMode frame.current.snapshot plan.resultMode
      frame.call.result
    runLoweredExecuteTarget
        (loweredResultTargetSteps frame.current.snapshot plan.resultMode
          frame.call.result)
        (.result frame plan) =
      if trace.accepted then
        executeTargetNextPlan { frame with
          accepted := frame.accepted ++ [plan.declaration]
          events := frame.events ++ trace.events ++
            [.installOccurrence plan.declarationOccurrence] }
      else
        executeTargetNextPlan { frame with
          events := frame.events ++ trace.events ++
            [.rejectOccurrence plan.declarationOccurrence] } := by
  cases resultMode : plan.resultMode with
  | resultUnchecked =>
      simp [loweredResultTargetSteps, runResultMode,
        runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
        directExecuteTargetStep?, resultMode]
  | resultSoftcutType expected =>
      by_cases exact : getTypeDecision frame.current.snapshot
          frame.call.result expected = true
      · simp [loweredResultTargetSteps, runResultMode,
          runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
          directExecuteTargetStep?, resultMode, exact, List.append_assoc]
      · have exactFalse : getTypeDecision frame.current.snapshot
            frame.call.result expected = false :=
          Bool.eq_false_of_not_eq_true exact
        by_cases metatype : getMetatypeDecision frame.current.snapshot
            frame.call.result expected = true
        · simp [loweredResultTargetSteps, runResultMode,
            runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
            directExecuteTargetStep?, resultMode, exactFalse, metatype,
            List.append_assoc]
        · have metatypeFalse : getMetatypeDecision frame.current.snapshot
              frame.call.result expected = false :=
            Bool.eq_false_of_not_eq_true metatype
          simp [loweredResultTargetSteps, runResultMode,
            runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
            directExecuteTargetStep?, executeTargetReject, resultMode,
            exactFalse, metatypeFalse, List.append_assoc]

def loweredPlanTargetSteps (snapshot : Snapshot) (call : Call)
    (plan : GuardPlan) : Nat :=
  if plan.declaration.function = call.function then
    let arguments := runArguments snapshot 0 plan.argumentModes
      call.sourceArguments call.evaluatedArguments
    let argumentSteps := loweredArgumentTargetSteps snapshot 0
      plan.argumentModes call.sourceArguments call.evaluatedArguments
    if arguments.accepted then
      argumentSteps + 1 +
        loweredResultTargetSteps snapshot plan.resultMode call.result
    else argumentSteps
  else 1

theorem runLoweredExecuteTarget_plan_exact
    (frame : ExecuteTargetFrame) (plan : GuardPlan) :
    let trace := runPlan frame.current.snapshot frame.call plan
    runLoweredExecuteTarget
        (loweredPlanTargetSteps frame.current.snapshot frame.call plan)
        (executeTargetBeginPlan frame plan) =
      if trace.accepted then
        executeTargetNextPlan { frame with
          accepted := frame.accepted ++ [plan.declaration]
          events := frame.events ++ trace.events }
      else
        executeTargetNextPlan { frame with
          events := frame.events ++ trace.events } := by
  by_cases headMatches : plan.declaration.function = frame.call.function
  · by_cases argumentsAccepted :
        (runArguments frame.current.snapshot 0 plan.argumentModes
          frame.call.sourceArguments frame.call.evaluatedArguments).accepted =
          true
    · let argumentFrame : ExecuteTargetFrame := { frame with
          events := frame.events ++
            [.beginPlan plan.declarationOccurrence] }
      let argumentSteps := loweredArgumentTargetSteps frame.current.snapshot 0
        plan.argumentModes frame.call.sourceArguments
          frame.call.evaluatedArguments
      let resultSteps := loweredResultTargetSteps frame.current.snapshot
        plan.resultMode frame.call.result
      rw [show loweredPlanTargetSteps frame.current.snapshot frame.call plan =
          argumentSteps + (1 + resultSteps) by
        simp only [loweredPlanTargetSteps, headMatches, if_pos,
          argumentsAccepted, argumentSteps, resultSteps]
        omega]
      rw [runLoweredExecuteTarget_add]
      have argumentsExact :
          runLoweredExecuteTarget argumentSteps
              (executeTargetArgumentsStart argumentFrame plan 0
                plan.argumentModes frame.call.sourceArguments
                frame.call.evaluatedArguments) =
            .body { argumentFrame with events := argumentFrame.events ++
              (runArguments frame.current.snapshot 0 plan.argumentModes
                frame.call.sourceArguments
                frame.call.evaluatedArguments).events } plan := by
        simpa [argumentFrame, argumentSteps, argumentsAccepted] using
          (runLoweredExecuteTarget_arguments_exact argumentFrame plan 0
            plan.argumentModes frame.call.sourceArguments
              frame.call.evaluatedArguments)
      simp only [executeTargetBeginPlan, executeTargetPlanStart, headMatches,
        if_pos]
      rw [argumentsExact]
      rw [Nat.one_add]
      simp only [runLoweredExecuteTarget]
      rw [loweredExecuteTargetStep_exact]
      simp only [directExecuteTargetStep?]
      let resultFrame : ExecuteTargetFrame := { argumentFrame with
        events := argumentFrame.events ++
          (runArguments frame.current.snapshot 0 plan.argumentModes
            frame.call.sourceArguments frame.call.evaluatedArguments).events ++
          [.evaluateCall plan.declarationOccurrence] }
      change runLoweredExecuteTarget resultSteps (.result resultFrame plan) = _
      have resultExact :=
        runLoweredExecuteTarget_result_exact resultFrame plan
      simp only [resultFrame] at resultExact
      rw [resultExact]
      by_cases resultAccepted :
          (runResultMode frame.current.snapshot plan.resultMode
            frame.call.result).accepted = true
      · simp [runPlan, headMatches, argumentsAccepted, resultAccepted,
          argumentFrame, List.append_assoc]
      · have resultRejected :
            (runResultMode frame.current.snapshot plan.resultMode
              frame.call.result).accepted = false :=
          Bool.eq_false_of_not_eq_true resultAccepted
        simp [runPlan, headMatches, argumentsAccepted, resultRejected,
          argumentFrame, List.append_assoc]
    · have argumentsRejected :
          (runArguments frame.current.snapshot 0 plan.argumentModes
            frame.call.sourceArguments frame.call.evaluatedArguments).accepted =
            false :=
        Bool.eq_false_of_not_eq_true argumentsAccepted
      have argumentsExact := runLoweredExecuteTarget_arguments_exact
        { frame with events := frame.events ++
          [.beginPlan plan.declarationOccurrence] }
        plan 0 plan.argumentModes frame.call.sourceArguments
          frame.call.evaluatedArguments
      simpa [loweredPlanTargetSteps, executeTargetBeginPlan,
        executeTargetPlanStart, headMatches, runPlan, argumentsRejected,
        List.append_assoc] using argumentsExact
  · simp [loweredPlanTargetSteps, executeTargetBeginPlan,
      executeTargetPlanStart, headMatches, runPlan, runLoweredExecuteTarget,
      loweredExecuteTargetStep_exact, directExecuteTargetStep?,
      executeTargetReject, List.append_assoc]

def loweredPlanListTargetSteps (snapshot : Snapshot) (call : Call) :
    List GuardPlan → Nat
  | [] => 0
  | plan :: plans =>
      loweredPlanTargetSteps snapshot call plan +
        loweredPlanListTargetSteps snapshot call plans

theorem runLoweredExecuteTarget_planList_exact
    (frame : ExecuteTargetFrame) (plans : List GuardPlan) :
    let trace := runPlanList frame.current.snapshot frame.call plans
    runLoweredExecuteTarget
        (loweredPlanListTargetSteps frame.current.snapshot frame.call plans)
        (executeTargetNextPlan { frame with remainingPlans := plans }) =
      .done (frame.accepted ++ trace.declarations)
        (frame.events ++ trace.events) := by
  induction plans generalizing frame with
  | nil =>
      simp [loweredPlanListTargetSteps, executeTargetNextPlan, runPlanList,
        runLoweredExecuteTarget]
  | cons plan plans inductionHypothesis =>
      rw [show loweredPlanListTargetSteps frame.current.snapshot frame.call
            (plan :: plans) =
          loweredPlanTargetSteps frame.current.snapshot frame.call plan +
            loweredPlanListTargetSteps frame.current.snapshot frame.call plans
        by rfl]
      rw [runLoweredExecuteTarget_add]
      simp only [executeTargetNextPlan]
      have planExact := runLoweredExecuteTarget_plan_exact
        { frame with remainingPlans := plans } plan
      rw [planExact]
      cases current : runPlan frame.current.snapshot frame.call plan with
      | mk accepted events =>
          cases accepted with
          | false =>
              have tailExact := inductionHypothesis
                { frame with
                  remainingPlans := plans
                  events := frame.events ++ events }
              simpa [runPlanList, current, List.append_assoc] using tailExact
          | true =>
              have tailExact := inductionHypothesis
                { frame with
                  remainingPlans := plans
                  accepted := frame.accepted ++ [plan.declaration]
                  events := frame.events ++ events }
              simpa [runPlanList, current, List.append_assoc] using tailExact

def loweredExecuteTargetBudget (current : OwnedSnapshot) (call : Call) :
    CompilationResult → Nat
  | .outsideFragment => 1
  | .compiled family =>
      loweredPlanListTargetSteps current.snapshot call family.plans + 2

set_option maxHeartbeats 12000000 in
theorem repeated_lowered_execute_transitions_normalize_exactly
    (current : OwnedSnapshot) (call : Call) (result : CompilationResult) :
    runLoweredExecuteTarget (loweredExecuteTargetBudget current call result)
        (loweredExecuteTargetStart current call result) =
      .halted (executeCompilation current call result)
        (executeControl current call result).events := by
  cases result with
  | outsideFragment =>
      simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
        runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
        directExecuteTargetStep?, executeControl, executeCompilation]
  | compiled family =>
      by_cases ownerCurrent : family.owner = current.owner
      · by_cases revisionCurrent :
            family.revision = current.snapshot.revision
        · by_cases headMatches : family.head = call.function
          · by_cases arityMatches :
                family.arity = call.sourceArguments.length
            · cases plansEq : family.plans with
              | nil =>
                  simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
                    runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
                    directExecuteTargetStep?, executeTargetFirstPlan,
                    executeControl, executeFamilyControl, executeCompilation,
                    executeGuardFamily, executePlanList, runPlanList,
                    ownerCurrent, revisionCurrent, headMatches, arityMatches,
                    plansEq]
              | cons plan plans =>
                  let initial : ExecuteTargetFrame := {
                    current := current
                    call := call
                    remainingPlans := family.plans
                    accepted := []
                    events := [] }
                  let steps := loweredPlanListTargetSteps current.snapshot call
                    family.plans
                  have listExact :
                      runLoweredExecuteTarget steps
                          (executeTargetFirstPlan current call family.plans) =
                        .done
                          (runPlanList current.snapshot call family.plans).declarations
                          (runPlanList current.snapshot call family.plans).events := by
                    simpa [initial, steps, executeTargetFirstPlan,
                      executeTargetNextPlan, plansEq] using
                      (runLoweredExecuteTarget_planList_exact initial
                        family.plans)
                  rw [show loweredExecuteTargetBudget current call
                        (.compiled family) = 1 + (steps + 1) by
                    simp [loweredExecuteTargetBudget, steps]
                    omega]
                  rw [runLoweredExecuteTarget_add]
                  have authorityStep :
                      runLoweredExecuteTarget 1
                          (loweredExecuteTargetStart current call
                            (.compiled family)) =
                        executeTargetFirstPlan current call family.plans := by
                    simp [runLoweredExecuteTarget,
                      loweredExecuteTargetStep_exact,
                      directExecuteTargetStep?, loweredExecuteTargetStart,
                      ownerCurrent, revisionCurrent, headMatches, arityMatches]
                  rw [authorityStep]
                  rw [runLoweredExecuteTarget_add steps 1]
                  rw [listExact]
                  simp [runLoweredExecuteTarget,
                    loweredExecuteTargetStep_exact, directExecuteTargetStep?,
                    executeControl, executeFamilyControl, executeCompilation,
                    executeGuardFamily, ownerCurrent, revisionCurrent,
                    headMatches, arityMatches,
                    runPlanList_declarations_exact]
            · simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
                runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
                directExecuteTargetStep?, executeControl, executeFamilyControl,
                executeCompilation, executeGuardFamily, ownerCurrent,
                revisionCurrent, headMatches, arityMatches]
          · simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
              runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
              directExecuteTargetStep?, executeControl, executeFamilyControl,
              executeCompilation, executeGuardFamily, ownerCurrent,
              revisionCurrent, headMatches]
        · simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
            runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
            directExecuteTargetStep?, executeControl, executeFamilyControl,
            executeCompilation, executeGuardFamily, ownerCurrent,
            revisionCurrent]
      · simp [loweredExecuteTargetBudget, loweredExecuteTargetStart,
          runLoweredExecuteTarget, loweredExecuteTargetStep_exact,
          directExecuteTargetStep?, executeControl, executeFamilyControl,
          executeCompilation, executeGuardFamily, ownerCurrent]

theorem independent_target_valid_execution_successfulDeclarations_exact
    {owned : OwnedSnapshot} {call : Call} {family : CompiledGuardFamily}
    (valid : family.ValidFor owned) (requestMatches : family.MatchesCall call) :
    targetExecuteCompilation owned call (.compiled family) =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  rw [independent_target_execution_exact]
  exact executeCompilation_eq_successfulDeclarations
    owned call family valid requestMatches

theorem lowered_valid_execution_successfulDeclarations_exact
    {owned : OwnedSnapshot} {call : Call} {family : CompiledGuardFamily}
    (valid : family.ValidFor owned) (requestMatches : family.MatchesCall call) :
    runLoweredExecuteTarget
        (loweredExecuteTargetBudget owned call (.compiled family))
        (loweredExecuteTargetStart owned call (.compiled family)) =
      .halted
        (.executed (successfulDeclarations ⟨owned.snapshot, call⟩))
        (executeControl owned call (.compiled family)).events := by
  rw [repeated_lowered_execute_transitions_normalize_exactly]
  rw [executeCompilation_eq_successfulDeclarations
    owned call family valid requestMatches]

theorem target_execution_no_invention
    (snapshot : Snapshot) (call : Call) (plans : List GuardPlan)
    {declaration : ArrowDeclaration}
    (member : declaration ∈ targetExecutePlans snapshot call plans) :
    declaration ∈ plans.map (·.declaration) := by
  rw [targetExecutePlans_exact, ← runPlanList_declarations_exact] at member
  obtain ⟨plan, planMember, declarationExact⟩ :=
    runPlanList_occurrences_no_invention snapshot call plans member
  exact List.mem_map.mpr ⟨plan, planMember, declarationExact⟩

#print axioms lowered_compile_transition_one_step_adequate
#print axioms lowered_execute_transition_one_step_adequate
#print axioms primitive_fault_classes_remain_distinct
#print axioms language_engine_resource_faults_pairwise_distinct
#print axioms exact_success_receipt_has_no_metatype
#print axioms metatype_receipt_places_exact_query_first
#print axioms missing_compile_handler_is_stuck
#print axioms missing_execute_handler_is_stuck
#print axioms compile_done_has_no_reducts
#print axioms execute_done_has_no_reducts
#print axioms compile_outcome_receipt_no_invention
#print axioms execute_outcome_receipt_no_invention
#print axioms independent_target_compilation_exact
#print axioms loweredCompileTargetStep_exact
#print axioms lowered_compile_target_step_simulates
#print axioms omitted_compile_advance_stops_between_plan_and_cursor
#print axioms repeated_lowered_compile_transitions_normalize_exactly
#print axioms independent_target_execution_exact
#print axioms loweredExecuteTargetStep_exact
#print axioms lowered_execute_target_step_simulates
#print axioms stale_authority_falls_back_and_halts
#print axioms install_after_rejection_is_impossible
#print axioms omitted_execute_advance_stops_after_install
#print axioms reversed_checked_argument_queries_change_receipt
#print axioms runLoweredExecuteTarget_arguments_exact
#print axioms runLoweredExecuteTarget_result_exact
#print axioms runLoweredExecuteTarget_plan_exact
#print axioms runLoweredExecuteTarget_planList_exact
#print axioms repeated_lowered_execute_transitions_normalize_exactly
#print axioms lowered_valid_execution_successfulDeclarations_exact
#print axioms target_execution_no_invention

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardToStructuredCSemantics
