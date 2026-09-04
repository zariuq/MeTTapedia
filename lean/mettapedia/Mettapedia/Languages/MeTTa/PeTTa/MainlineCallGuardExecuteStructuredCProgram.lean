import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram
import Mettapedia.GSLT.LanguageDef.StructuredCBuilder
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Source-derived StructuredC dispatch for hot PeTTa call guards

The completed-call executor has a finite, inspectable instruction program.
This module lowers the five instructions which determine argument and result
mode behavior into two small StructuredC dispatch functions.  The surrounding
CeTTa scheduler remains responsible for evaluation, type queries,
continuations, choicepoints, and rollback; these generated functions decide
which of those operations the authored guard plan requires.

Every target switch case is produced by the corresponding source instruction.
The lowering rejects a source inventory with a missing or duplicated
load-bearing mode instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram

structure ActionCase where
  instruction : Instruction
  inputSymbol : String
  actionSymbol : String
deriving DecidableEq, Repr

def argumentActionCase? : Instruction -> Option ActionCase
  | .argumentRaw => some {
      instruction := .argumentRaw
      inputSymbol := "PETTA_MAINLINE_CALL_GUARD_ARG_RAW_ATOM"
      actionSymbol := "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_RAW_V1" }
  | .argumentUnchecked => some {
      instruction := .argumentUnchecked
      inputSymbol := "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_UNCHECKED"
      actionSymbol := "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_UNCHECKED_V1" }
  | .argumentChecked => some {
      instruction := .argumentChecked
      inputSymbol := "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_SOFTCUT_TYPE"
      actionSymbol := "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_CHECKED_V1" }
  | _ => none

def resultActionCase? : Instruction -> Option ActionCase
  | .resultUnchecked => some {
      instruction := .resultUnchecked
      inputSymbol := "PETTA_MAINLINE_CALL_GUARD_RESULT_UNCHECKED"
      actionSymbol := "CETTA_PETTA_CALL_GUARD_HOT_ACCEPT_UNCHECKED_RESULT_V1" }
  | .resultChecked => some {
      instruction := .resultChecked
      inputSymbol := "PETTA_MAINLINE_CALL_GUARD_RESULT_SOFTCUT_TYPE"
      actionSymbol := "CETTA_PETTA_CALL_GUARD_HOT_CHECK_RESULT_V1" }
  | _ => none

def actionCases (decode : Instruction -> Option ActionCase) :
    List Instruction -> List ActionCase
  | [] => []
  | instruction :: rest =>
      match decode instruction with
      | some action => action :: actionCases decode rest
      | none => actionCases decode rest

def requiredModeInstructions : List Instruction := [
  .argumentRaw,
  .argumentUnchecked,
  .argumentChecked,
  .resultUnchecked,
  .resultChecked]

def modeInventoryValid (source : List Instruction) : Bool :=
  decide source.Nodup &&
    requiredModeInstructions.all source.contains

private def lowerActionCase (action : ActionCase) : Pattern :=
  caseBranch (valueSymbol action.inputSymbol)
    (statements [returnSymbol action.actionSymbol])

private def actionFunction (source : List Instruction)
    (decode : Instruction -> Option ActionCase)
    (name parameterName parameterType : String) : Pattern :=
  function name (namedType "CettaPeTTaCallGuardHotActionV1")
    [parameter parameterName (namedType parameterType)]
    (statements [switch (variableExpression parameterName)
      ((actionCases decode source).map lowerActionCase)
      (statements [returnSymbol
        "CETTA_PETTA_CALL_GUARD_HOT_ENGINE_FAULT_V1"])])

def argumentActionFunction (source : List Instruction) : Pattern :=
  actionFunction source argumentActionCase?
    "cetta_generated_petta_call_guard_argument_action_v1"
    "mode" "PettaMainlineCallGuardArgModeTag"

def resultActionFunction (source : List Instruction) : Pattern :=
  actionFunction source resultActionCase?
    "cetta_generated_petta_call_guard_result_action_v1"
    "mode" "PettaMainlineCallGuardResultModeTag"

def lowerHotModeProgram? (source : List Instruction) : Option Pattern :=
  if modeInventoryValid source then
    some (Mettapedia.GSLT.LanguageDef.StructuredC.Builder.program [] [
      argumentActionFunction source,
      resultActionFunction source])
  else
    none

/-- The exported target is structurally assembled from the authentic hot
instruction inventory. -/
def generatedHotModeProgram : Pattern :=
  Mettapedia.GSLT.LanguageDef.StructuredC.Builder.program [] [
    argumentActionFunction program,
    resultActionFunction program]

theorem lower_authentic_program_exact :
    lowerHotModeProgram? program = some generatedHotModeProgram := by
  rfl

theorem generatedHotModeProgram_target_typed :
    CarrierWellSorted.HasType StructuredC.language
      WellSorted.FreeTypeContext.empty [] generatedHotModeProgram
      (.base "Program") := by
  apply CarrierWellSorted.checkHasType_sound
  decide +kernel

namespace Canary

theorem argument_cases_are_source_ordered :
    (actionCases argumentActionCase? program).map ActionCase.instruction = [
      .argumentRaw, .argumentUnchecked, .argumentChecked] := by
  rfl

theorem result_cases_are_source_ordered :
    (actionCases resultActionCase? program).map ActionCase.instruction = [
      .resultUnchecked, .resultChecked] := by
  rfl

theorem removing_checked_argument_rejects_lowering :
    lowerHotModeProgram? (program.filter (. != .argumentChecked)) = none := by
  decide

theorem removing_checked_result_rejects_lowering :
    lowerHotModeProgram? (program.filter (. != .resultChecked)) = none := by
  decide

theorem duplicating_raw_argument_rejects_lowering :
    lowerHotModeProgram? (.argumentRaw :: program) = none := by
  decide

end Canary

#print axioms lower_authentic_program_exact
#print axioms generatedHotModeProgram_target_typed
#print axioms Canary.argument_cases_are_source_ordered
#print axioms Canary.result_cases_are_source_ordered
#print axioms Canary.removing_checked_argument_rejects_lowering
#print axioms Canary.removing_checked_result_rejects_lowering
#print axioms Canary.duplicating_raw_argument_rejects_lowering

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
