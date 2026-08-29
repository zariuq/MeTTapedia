import Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall
import Mettapedia.GSLT.LanguageDef.StructuredCNTT
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# External-call programs lowered to StructuredC programs

This is the theorem-side reference for the second fixed-language compiler
stage.  Its input is an actual program in the authored external-call language;
its output is an actual `StructuredC` function or program pattern.  Provider
calls, partial-operation guards, receipts, cases, and returns therefore remain
visible target syntax rather than being hidden in a parallel implementation
record.
-/

namespace Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def identifier (name : String) : Pattern :=
  a "structured-c:identifier" [a name]

private def functionName (name : String) : Pattern :=
  a "structured-c:function-name" [a name]

private def externalName (name : String) : Pattern :=
  a "structured-c:external-name" [a name]

private def namedType (name : String) : Pattern :=
  a "structured-c:type-named" [identifier name]

private def pointerType (name : String) (isConst : Bool) : Pattern :=
  let base := namedType name
  let target := if isConst then a "structured-c:type-const" [base] else base
  a "structured-c:type-pointer" [target]

private def variableExpression (name : String) : Pattern :=
  a "structured-c:expression-variable" [identifier name]

private def symbol (name : String) : Pattern :=
  a "structured-c:expression-constant"
    [a "structured-c:value-symbol" [identifier name]]

private def integer (value : Nat) : Pattern :=
  a "structured-c:expression-constant"
    [a "structured-c:value-integer" [a (toString value)]]

private def expressionList : List Pattern → Pattern
  | [] => a "structured-c:expressions-nil"
  | expression :: rest =>
      a "structured-c:expressions-cons" [expression, expressionList rest]

private def call (name : String) (arguments : List Pattern) : Pattern :=
  a "structured-c:expression-call"
    [externalName name, expressionList arguments]

private def statements : List Pattern → Pattern
  | [] => a "structured-c:statements-nil"
  | statement :: rest =>
      a "structured-c:statements-cons" [statement, statements rest]

private def effect (expression : Pattern) : Pattern :=
  a "structured-c:effect" [expression]

private def returnExpression (expression : Pattern) : Pattern :=
  a "structured-c:return" [expression]

private def recordStep (programCounter : Nat) : Pattern :=
  effect (call "cetta_external_call_generated_record_step_v1"
    [variableExpression "receipt", integer programCounter])

private def recordExternal (programCounter : Nat) : Pattern :=
  effect (call "cetta_external_call_generated_record_external_v1"
    [variableExpression "receipt", integer programCounter, integer 0,
     variableExpression "external_status"])

private def finish (outcome : String) : Pattern :=
  call "cetta_external_call_generated_finish_v1"
    [variableExpression "receipt", symbol outcome]

private def outcomeCases (valueProgramCounter : Nat) : Pattern :=
  let cases := [
    ("CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_VALUE_V1",
      "CETTA_EXTERNAL_CALL_GENERATED_VALUE_V1"),
    ("CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_LANGUAGE_FAULT_V1",
      "CETTA_EXTERNAL_CALL_GENERATED_LANGUAGE_FAULT_V1"),
    ("CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_ENGINE_FAULT_V1",
      "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1"),
    ("CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_RESOURCE_FAULT_V1",
      "CETTA_EXTERNAL_CALL_GENERATED_RESOURCE_FAULT_V1")]
  cases.zipIdx.foldr (fun entry rest =>
      a "structured-c:cases-cons" [
        a "structured-c:case" [
          a "structured-c:value-symbol" [identifier entry.1.1],
          statements [recordStep (valueProgramCounter + entry.2),
            returnExpression (finish entry.1.2)]],
        rest])
    (a "structured-c:cases-nil")

private def guardedPrefix : List Pattern := [
  recordStep 0,
  a "structured-c:if" [
    call "cetta_external_call_exact_integer_is_zero_v1"
      [variableExpression "second"],
    statements [recordStep 1,
      returnExpression (finish
        "CETTA_EXTERNAL_CALL_GENERATED_DECLINED_V1")],
    statements []]]

def generatedFunctionName : CoreOp → String
  | .add => "cetta_generated_exact_integer_add_v1"
  | .sub => "cetta_generated_exact_integer_sub_v1"
  | .mul => "cetta_generated_exact_integer_mul_v1"
  | .tquot => "cetta_generated_exact_integer_tquot_v1"
  | .fquot => "cetta_generated_exact_integer_fquot_v1"
  | .trem => "cetta_generated_exact_integer_trem_v1"
  | .frem => "cetta_generated_exact_integer_frem_v1"

private def parameter (name typeName : String)
    (pointer isConst : Bool) : Pattern :=
  a "structured-c:parameter" [identifier name,
    if pointer then pointerType typeName isConst else namedType typeName]

private def parameterList : List Pattern → Pattern
  | [] => a "structured-c:parameters-nil"
  | item :: rest =>
      a "structured-c:parameters-cons" [item, parameterList rest]

private def generatedParameters : Pattern := parameterList [
  parameter "first" "CettaExternalCallExactIntegerV1" true true,
  parameter "second" "CettaExternalCallExactIntegerV1" true true,
  parameter "output" "CettaExternalCallExactIntegerV1" true false,
  parameter "receipt" "CettaExternalCallGeneratedReceiptV1" true false]

private def externalParameters : Pattern := parameterList [
  parameter "first" "CettaExternalCallExactIntegerV1" true true,
  parameter "second" "CettaExternalCallExactIntegerV1" true true,
  parameter "output" "CettaExternalCallExactIntegerV1" true false]

/-- The executable statement body selected for one source operation.  Keeping
this target term public lets semantic and emission proofs consume exactly the
same StructuredC program fragment. -/
def lowerCoreOperationBody (operation : CoreOp) : Pattern :=
  let guarded := operation.isPartial
  let callPc := if guarded then 2 else 0
  let valuePc := if guarded then 3 else 1
  let missingReceipt := a "structured-c:if" [
    call "cetta_external_call_generated_receipt_missing_v1"
      [variableExpression "receipt"],
    statements [returnExpression
      (symbol "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")],
    statements []]
  let beginReceipt := effect
    (call "cetta_external_call_generated_begin_v1"
      [variableExpression "receipt"])
  let invoke := a "structured-c:declare" [identifier "external_status",
    namedType "CettaExternalCallGeneratedExternalV1",
    call (targetLinkName operation)
      [variableExpression "first", variableExpression "second",
       variableExpression "output"]]
  let dispatch := a "structured-c:switch"
    [variableExpression "external_status",
    outcomeCases valuePc,
    statements [
      effect (call "cetta_external_call_generated_mark_incomplete_v1"
        [variableExpression "receipt"]),
      returnExpression (finish
        "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")]]
  statements ([missingReceipt, beginReceipt] ++
    (if guarded then guardedPrefix else []) ++
    [recordStep callPc, invoke, recordExternal callPc, dispatch])

/-- The target function obtained from one decoded external-call program. -/
def lowerCoreOperation (operation : CoreOp) : Pattern :=
  a "structured-c:function" [functionName (generatedFunctionName operation),
    namedType "CettaExternalCallGeneratedOutcomeV1", generatedParameters,
    lowerCoreOperationBody operation]

def lowerExternalCallProgram? (program : Pattern) : Option Pattern :=
  (decodeCompiledOperation? program).map lowerCoreOperation

def operations : List CoreOp :=
  [.add, .sub, .mul, .tquot, .fquot, .trem, .frem]

private def externalDeclaration (operation : CoreOp) : Pattern :=
  a "structured-c:external-function" [externalName (targetLinkName operation),
    namedType "CettaExternalCallGeneratedExternalV1", externalParameters]

private def externalDeclarations : List Pattern → Pattern
  | [] => a "structured-c:external-functions-nil"
  | item :: rest =>
      a "structured-c:external-functions-cons"
        [item, externalDeclarations rest]

private def functions : List Pattern → Pattern
  | [] => a "structured-c:functions-nil"
  | item :: rest =>
      a "structured-c:functions-cons" [item, functions rest]

/-- The complete target program for the seven-operation exact-arithmetic
interface.  Its subterms are all StructuredC constructors. -/
def arithmeticProgram : Pattern :=
  a "structured-c:program"
    [externalDeclarations (operations.map externalDeclaration),
     functions (operations.map lowerCoreOperation)]

@[simp] theorem lower_compiled_external_call (operation : CoreOp) :
    lowerExternalCallProgram? (compileCoreOperation operation) =
      some (lowerCoreOperation operation) := by
  simp [lowerExternalCallProgram?]

theorem operation_provider_is_load_bearing :
    lowerCoreOperation .add ≠ lowerCoreOperation .sub := by
  decide

theorem invented_program_is_rejected :
    CarrierWellSorted.checkHasType StructuredC.language
      WellSorted.FreeTypeContext.empty []
      (a "structured-c:invented-program") (.base "Program") = false := by
  decide +kernel

#print axioms lower_compiled_external_call
#print axioms invented_program_is_rejected

end Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredC
