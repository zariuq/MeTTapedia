import Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredCTyping
import Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

/-!
# Operational adequacy of the ExternalCall-to-StructuredC lowering

This module runs the actual statement body emitted by the fixed-language
lowering in the authored StructuredC GSLT.  The primitive handler exposes all
state changes: expression evaluation returns both the next environment and the
next receipt.  External output, status, step receipts, external-call receipts,
and final outcome storage are therefore visible in the target configuration.
-/

namespace Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredCSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

private def sc (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def token (name : String) : Pattern := sc name

private def identifier (name : String) : Pattern :=
  sc "structured-c:identifier" [token name]

private def externalName (name : String) : Pattern :=
  sc "structured-c:external-name" [token name]

private def valueInteger (value : Int) : Pattern :=
  sc "structured-c:value-integer" [token (toString value)]

private def valueSymbol (name : String) : Pattern :=
  sc "structured-c:value-symbol" [identifier name]

private def valueUnit : Pattern := sc "structured-c:value-unit"

private def variableExpression (name : String) : Pattern :=
  sc "structured-c:expression-variable" [identifier name]

private def constantExpression (value : Pattern) : Pattern :=
  sc "structured-c:expression-constant" [value]

private def expressionList : List Pattern → Pattern
  | [] => sc "structured-c:expressions-nil"
  | expression :: rest =>
      sc "structured-c:expressions-cons" [expression, expressionList rest]

private def call (name : String) (arguments : List Pattern) : Pattern :=
  sc "structured-c:expression-call"
    [externalName name, expressionList arguments]

private def statements : List Pattern → Pattern
  | [] => nilStatements
  | statement :: rest => consStatement statement (statements rest)

private def effect (expression : Pattern) : Pattern :=
  sc "structured-c:effect" [expression]

private def returnExpression (expression : Pattern) : Pattern :=
  sc "structured-c:return" [expression]

private def namedType (name : String) : Pattern :=
  sc "structured-c:type-named" [identifier name]

private def caseStatement (value body : Pattern) : Pattern :=
  sc "structured-c:case" [value, body]

private def cases : List Pattern → Pattern
  | [] => sc "structured-c:cases-nil"
  | one :: rest => sc "structured-c:cases-cons" [one, cases rest]

private def environmentEmpty : Pattern :=
  sc "structured-c:environment-empty"

private def environmentBind
    (name : String) (value rest : Pattern) : Pattern :=
  sc "structured-c:environment-bind" [identifier name, value, rest]

def initialEnvironment (first second : Int) : Pattern :=
  environmentBind "receipt" valueUnit
    (environmentBind "output" valueUnit
      (environmentBind "second" (valueInteger second)
        (environmentBind "first" (valueInteger first) environmentEmpty)))

def resultEnvironment
    (operation : CoreOp) (first second : Int) : Pattern :=
  environmentBind "output" (valueInteger (targetValue operation first second))
    (initialEnvironment first second)

private def externalValueStatus : Pattern :=
  valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_VALUE_V1"

def statusEnvironment
    (operation : CoreOp) (first second : Int) : Pattern :=
  environmentBind "external_status" externalValueStatus
    (resultEnvironment operation first second)

def readyReceipt : Pattern := sc "structured-c:receipt-ready"
def emptyReceipt : Pattern := sc "structured-c:receipt-empty"

def stepReceipt (programCounter : Nat) (prior : Pattern) : Pattern :=
  sc "structured-c:receipt-step" [valueInteger programCounter, prior]

def externalReceipt (programCounter : Nat)
    (outcome prior : Pattern) : Pattern :=
  sc "structured-c:receipt-external"
    [valueInteger programCounter, valueInteger 0, outcome, prior]

def finishedReceipt (outcome prior : Pattern) : Pattern :=
  sc "structured-c:receipt-finished" [outcome, prior]

private def falseValue : Pattern := valueSymbol "false"
private def trueValue : Pattern := valueSymbol "true"

private theorem trueValue_ne_falseValue : trueValue ≠ falseValue := by
  decide +kernel

private def missingReceiptThen : Pattern :=
  statements [returnExpression (constantExpression
    (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1"))]

private def guardThen : Pattern :=
  statements [
    effect (call "cetta_external_call_generated_record_step_v1"
      [variableExpression "receipt", constantExpression (valueInteger 1)]),
    returnExpression (call "cetta_external_call_generated_finish_v1"
      [variableExpression "receipt", constantExpression
        (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_DECLINED_V1")])]

private def resultCases (valueProgramCounter : Nat) : Pattern :=
  cases [
    caseStatement externalValueStatus
      (statements [
        effect (call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger valueProgramCounter)]),
        returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression
            (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_VALUE_V1")])]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_LANGUAGE_FAULT_V1")
      (statements [
        effect (call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (valueProgramCounter + 1))]),
        returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression
            (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_LANGUAGE_FAULT_V1")])]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_ENGINE_FAULT_V1")
      (statements [
        effect (call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (valueProgramCounter + 2))]),
        returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression
            (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")])]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_RESOURCE_FAULT_V1")
      (statements [
        effect (call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (valueProgramCounter + 3))]),
        returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression
            (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_RESOURCE_FAULT_V1")])])]

private def defaultCase : Pattern :=
  statements [
    effect (call "cetta_external_call_generated_mark_incomplete_v1"
      [variableExpression "receipt"]),
    returnExpression (call "cetta_external_call_generated_finish_v1"
      [variableExpression "receipt", constantExpression
        (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")])]

private def callProgramCounter (operation : CoreOp) : Nat :=
  if operation.isPartial then 2 else 0

private def valueProgramCounter (operation : CoreOp) : Nat :=
  if operation.isPartial then 3 else 1

private def missingCondition : Pattern :=
  call "cetta_external_call_generated_receipt_missing_v1"
    [variableExpression "receipt"]

private def missingStatement : Pattern :=
  sc "structured-c:if"
    [missingCondition, missingReceiptThen, nilStatements]

private def beginStatement : Pattern :=
  effect (call "cetta_external_call_generated_begin_v1"
    [variableExpression "receipt"])

private def recordStepStatement (programCounter : Nat) : Pattern :=
  effect (call "cetta_external_call_generated_record_step_v1"
    [variableExpression "receipt", constantExpression
      (valueInteger programCounter)])

private def zeroGuardStatement : Pattern :=
  sc "structured-c:if"
    [call "cetta_external_call_exact_integer_is_zero_v1"
      [variableExpression "second"], guardThen, nilStatements]

private def invokeStatement (operation : CoreOp) : Pattern :=
  sc "structured-c:declare"
    [identifier "external_status",
     namedType "CettaExternalCallGeneratedExternalV1",
     call (targetLinkName operation)
       [variableExpression "first", variableExpression "second",
        variableExpression "output"]]

private def recordExternalStatement (programCounter : Nat) : Pattern :=
  effect (call "cetta_external_call_generated_record_external_v1"
    [variableExpression "receipt", constantExpression
      (valueInteger programCounter), constantExpression (valueInteger 0),
     variableExpression "external_status"])

private def dispatchStatement (operation : CoreOp) : Pattern :=
  sc "structured-c:switch"
    [variableExpression "external_status",
     resultCases (valueProgramCounter operation), defaultCase]

private def operationStatements (operation : CoreOp) : List Pattern :=
  [missingStatement, beginStatement] ++
    (if operation.isPartial then
      [recordStepStatement 0, zeroGuardStatement]
    else []) ++
    [recordStepStatement (callProgramCounter operation),
     invokeStatement operation,
     recordExternalStatement (callProgramCounter operation),
     dispatchStatement operation]

private theorem loweredBody_is_operationStatements (operation : CoreOp) :
    ExternalCallToStructuredC.lowerCoreOperationBody operation =
      statements (operationStatements operation) := by
  cases operation <;> rfl

private def receiptAtCall (operation : CoreOp) : Pattern :=
  if operation.isPartial then stepReceipt 2 (stepReceipt 0 emptyReceipt)
  else stepReceipt 0 emptyReceipt

private def receiptAfterExternal (operation : CoreOp) : Pattern :=
  externalReceipt (callProgramCounter operation) externalValueStatus
    (receiptAtCall operation)

private def receiptBeforeFinish (operation : CoreOp) : Pattern :=
  stepReceipt (valueProgramCounter operation) (receiptAfterExternal operation)

private def valueOutcome : Pattern :=
  valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_VALUE_V1"

private def declinedOutcome : Pattern :=
  valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_DECLINED_V1"

def expectedOutcome (operation : CoreOp) (second : Int) : Pattern :=
  if targetUndefinedAt operation second then declinedOutcome else valueOutcome

def expectedReceipt (operation : CoreOp) (second : Int) : Pattern :=
  if targetUndefinedAt operation second then
    finishedReceipt declinedOutcome (stepReceipt 1 (stepReceipt 0 emptyReceipt))
  else
    finishedReceipt valueOutcome (receiptBeforeFinish operation)

def finalEnvironment
    (operation : CoreOp) (first second : Int) : Pattern :=
  if targetUndefinedAt operation second then initialEnvironment first second
  else statusEnvironment operation first second

private def evaluateRows
    (operation : CoreOp) (first second : Int) : List (List Pattern) :=
  let initial := initialEnvironment first second
  let afterStepZero := stepReceipt 0 emptyReceipt
  let missing := call "cetta_external_call_generated_receipt_missing_v1"
    [variableExpression "receipt"]
  let begin := call "cetta_external_call_generated_begin_v1"
    [variableExpression "receipt"]
  let recordZero := call "cetta_external_call_generated_record_step_v1"
    [variableExpression "receipt", constantExpression (valueInteger 0)]
  let zeroTest := call "cetta_external_call_exact_integer_is_zero_v1"
    [variableExpression "second"]
  let base := [
    [missing, initial, readyReceipt, evaluationValue falseValue,
      initial, readyReceipt],
    [begin, initial, readyReceipt, evaluationValue valueUnit,
      initial, emptyReceipt],
    [recordZero, initial, emptyReceipt, evaluationValue valueUnit,
      initial, afterStepZero]]
  if targetUndefinedAt operation second then
    base ++ [
      [zeroTest, initial, afterStepZero, evaluationValue trueValue,
        initial, afterStepZero],
      [call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression (valueInteger 1)],
        initial, afterStepZero, evaluationValue valueUnit,
        initial, stepReceipt 1 afterStepZero],
      [call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression declinedOutcome],
        initial, stepReceipt 1 afterStepZero,
        evaluationValue declinedOutcome, initial,
        expectedReceipt operation second]]
  else
    let atCall := receiptAtCall operation
    let result := resultEnvironment operation first second
    let status := statusEnvironment operation first second
    let afterExternal := receiptAfterExternal operation
    let beforeFinish := receiptBeforeFinish operation
    base ++
      (if operation.isPartial then [
        [zeroTest, initial, afterStepZero, evaluationValue falseValue,
          initial, afterStepZero],
        [call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression (valueInteger 2)],
          initial, afterStepZero, evaluationValue valueUnit, initial, atCall]]
      else []) ++ [
      [call (targetLinkName operation)
          [variableExpression "first", variableExpression "second",
           variableExpression "output"],
        initial, atCall, evaluationValue externalValueStatus, result, atCall],
      [call "cetta_external_call_generated_record_external_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (callProgramCounter operation)),
           constantExpression (valueInteger 0),
           variableExpression "external_status"],
        status, atCall, evaluationValue valueUnit, status, afterExternal],
      [variableExpression "external_status", status, afterExternal,
        evaluationValue externalValueStatus, status, afterExternal],
      [call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (valueProgramCounter operation))],
        status, afterExternal, evaluationValue valueUnit, status, beforeFinish],
      [call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome],
        status, beforeFinish, evaluationValue valueOutcome, status,
        expectedReceipt operation second]]

private def branchRows
    (operation : CoreOp) (second : Int) : List (List Pattern) :=
  let missingRow := [falseValue, missingReceiptThen, nilStatements, nilStatements]
  if operation.isPartial then
    let selected := if targetUndefinedAt operation second then guardThen
      else nilStatements
    [missingRow,
      [if targetUndefinedAt operation second then trueValue else falseValue,
       guardThen, nilStatements, selected]]
  else
    [missingRow]

private def caseRows (operation : CoreOp) : List (List Pattern) :=
  [[resultCases (valueProgramCounter operation), defaultCase,
    externalValueStatus,
    statements [
      effect (call "cetta_external_call_generated_record_step_v1"
        [variableExpression "receipt",
         constantExpression (valueInteger (valueProgramCounter operation))]),
      returnExpression (call "cetta_external_call_generated_finish_v1"
        [variableExpression "receipt", constantExpression valueOutcome])]]]

private def storeRows
    (operation : CoreOp) (first second : Int) : List (List Pattern) :=
  if targetUndefinedAt operation second then [] else
    [[resultEnvironment operation first second, identifier "external_status",
      externalValueStatus, statusEnvironment operation first second]]

private theorem guardThen_ne_missingReceiptThen :
    guardThen ≠ missingReceiptThen := by
  decide +kernel

private theorem missingReceiptThen_ne_guardThen :
    missingReceiptThen ≠ guardThen := by
  decide +kernel

/-- A catalog is admissible only when no two primitive rows have the same
already-bound request prefix. -/
def InputKeysUnique
    (inputCount : Nat) (rows : List (List Pattern)) : Prop :=
  (rows.map fun row => row.take inputCount).Nodup

set_option maxHeartbeats 800000 in
theorem evaluateRows_input_keys_unique
    (operation : CoreOp) (first second : Int) :
    InputKeysUnique 3 (evaluateRows operation first second) := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [InputKeysUnique, evaluateRows, targetUndefinedAt_iff, undefinedAt,
      CoreOp.isPartial, zero, targetLinkName, callProgramCounter,
      valueProgramCounter, call, externalName, expressionList,
      variableExpression, constantExpression, valueInteger, identifier, token,
      sc]

theorem branchRows_input_keys_unique
    (operation : CoreOp) (second : Int) :
    InputKeysUnique 3 (branchRows operation second) := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [InputKeysUnique, branchRows, targetUndefinedAt_iff, undefinedAt,
      CoreOp.isPartial, zero, missingReceiptThen_ne_guardThen]

theorem caseRows_input_keys_unique (operation : CoreOp) :
    InputKeysUnique 3 (caseRows operation) := by
  simp [InputKeysUnique, caseRows]

theorem storeRows_input_keys_unique
    (operation : CoreOp) (first second : Int) :
    InputKeysUnique 3 (storeRows operation first second) := by
  unfold InputKeysUnique storeRows
  split <;> simp

/-- Select from a catalog whose input keys have already been proved unique.
The proof argument prevents first-match lookup from masking a duplicate row. -/
def selectInputRows
    (inputCount : Nat) (arguments : List Pattern)
    (rows : List (List Pattern))
    (_unique : InputKeysUnique inputCount rows) : List (List Pattern) :=
  match rows.find? fun row => row.take inputCount == arguments.take inputCount with
  | some row => [row]
  | none => []

/-- Request-local primitive semantics for the exact generated function.  All
effects are returned as target-language environment and receipt states; the
handler cannot mutate an object outside the StructuredC configuration. -/
def referenceEnv
    (operation : CoreOp) (first second : Int) : RelationEnv where
  tuples := fun relation arguments =>
    if relation == "StructuredCEvaluate" then
      selectInputRows 3 arguments (evaluateRows operation first second)
        (evaluateRows_input_keys_unique operation first second)
    else if relation == "StructuredCStore" then
      selectInputRows 3 arguments (storeRows operation first second)
        (storeRows_input_keys_unique operation first second)
    else if relation == "StructuredCSelectBranch" then
      selectInputRows 3 arguments (branchRows operation second)
        (branchRows_input_keys_unique operation second)
    else if relation == "StructuredCSelectCase" then
      selectInputRows 3 arguments (caseRows operation)
        (caseRows_input_keys_unique operation)
    else
      []

def start (operation : CoreOp) (first second : Int) : Pattern :=
  run (ExternalCallToStructuredC.lowerCoreOperationBody operation)
    (initialEnvironment first second) readyReceipt

def done (operation : CoreOp) (first second : Int) : Pattern :=
  halted (sc "structured-c:outcome-return"
      [expectedOutcome operation second])
    (finalEnvironment operation first second)
    (expectedReceipt operation second)

private def afterMissing (operation : CoreOp) : Pattern :=
  statements (operationStatements operation).tail

private theorem start_is_missing_phase
    (operation : CoreOp) (first second : Int) :
    start operation first second =
      run (consStatement missingStatement (afterMissing operation))
        (initialEnvironment first second) readyReceipt := by
  rw [start, loweredBody_is_operationStatements]
  cases operation <;> rfl

private theorem missing_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (result environment receipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [missingCondition, initialEnvironment first second, readyReceipt,
         result, environment, receipt] =
      [[missingCondition, initialEnvironment first second, readyReceipt,
        evaluationValue falseValue, initialEnvironment first second,
        readyReceipt]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, branchRows, caseRows,
      storeRows, targetUndefinedAt_iff, undefinedAt, CoreOp.isPartial, zero,
      missingCondition, falseValue, readyReceipt, initialEnvironment,
      sc, call, externalName, expressionList, variableExpression,
      constantExpression, valueInteger, valueSymbol, valueUnit, identifier,
      token]

private theorem missing_selection_tuples_exact
    (operation : CoreOp) (first second : Int) (selected : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCSelectBranch"
        [falseValue, missingReceiptThen, nilStatements, selected] =
      [[falseValue, missingReceiptThen, nilStatements, nilStatements]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, branchRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero,
      falseValue, missingReceiptThen, sc, statements,
      returnExpression, constantExpression, valueSymbol, trueValue, guardThen,
      identifier, token]

private theorem missing_evaluation_exact
    (operation : CoreOp) (first second : Int) :
    premiseStepWithEnv (referenceEnv operation first second) language
        (ifMatchBindings missingCondition missingReceiptThen nilStatements
          (afterMissing operation) (initialEnvironment first second) readyReceipt)
        (query "StructuredCEvaluate"
          [v "condition", v "environment", v "receipt",
           evaluationValue (v "value"), v "evaluatedEnvironment",
           v "evaluatedReceipt"]) =
      [ifValueBindings missingCondition missingReceiptThen nilStatements
        (afterMissing operation) (initialEnvironment first second) readyReceipt
        falseValue (initialEnvironment first second) readyReceipt] := by
  change relationQueryStep (referenceEnv operation first second) language
    (ifMatchBindings missingCondition missingReceiptThen nilStatements
      (afterMissing operation) (initialEnvironment first second) readyReceipt)
    "StructuredCEvaluate"
      [v "condition", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"] = _
  simp [relationQueryStep, builtinRelationTuples,
    missing_evaluation_tuples_exact,
    ifMatchBindings, ifValueBindings, evaluationValue,
    StructuredC.v, StructuredC.a,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup,
    applyBindings, mergeBindings]

private theorem missing_selection_exact
    (operation : CoreOp) (first second : Int) :
    premiseStepWithEnv (referenceEnv operation first second) language
        (ifValueBindings missingCondition missingReceiptThen nilStatements
          (afterMissing operation) (initialEnvironment first second) readyReceipt
          falseValue (initialEnvironment first second) readyReceipt)
        (query "StructuredCSelectBranch"
          [v "value", v "thenBranch", v "elseBranch", v "selected"]) =
      [ifSelectedBindings missingCondition missingReceiptThen nilStatements
        (afterMissing operation) (initialEnvironment first second) readyReceipt
        falseValue (initialEnvironment first second) readyReceipt
        nilStatements] := by
  change relationQueryStep (referenceEnv operation first second) language
    (ifValueBindings missingCondition missingReceiptThen nilStatements
      (afterMissing operation) (initialEnvironment first second) readyReceipt
      falseValue (initialEnvironment first second) readyReceipt)
    "StructuredCSelectBranch"
      [v "value", v "thenBranch", v "elseBranch", v "selected"] = _
  simp [relationQueryStep, builtinRelationTuples,
    missing_selection_tuples_exact,
    ifMatchBindings, ifValueBindings, ifSelectedBindings,
    StructuredC.v,
    matchRelationArgs, matchRelationArgument,
    Bindings.lookup,
    applyBindings, mergeBindings]

private theorem missing_fault_exact
    (operation : CoreOp) (first second : Int) :
    premiseStepWithEnv (referenceEnv operation first second) language
        (ifMatchBindings missingCondition missingReceiptThen nilStatements
          (afterMissing operation) (initialEnvironment first second) readyReceipt)
        (query "StructuredCEvaluate"
          [v "condition", v "environment", v "receipt",
           evaluationFault (v "fault"), v "evaluatedEnvironment",
           v "evaluatedReceipt"]) = [] := by
  change relationQueryStep (referenceEnv operation first second) language
    (ifMatchBindings missingCondition missingReceiptThen nilStatements
      (afterMissing operation) (initialEnvironment first second) readyReceipt)
    "StructuredCEvaluate"
      [v "condition", v "environment", v "receipt",
       evaluationFault (v "fault"), v "evaluatedEnvironment",
       v "evaluatedReceipt"] = []
  simp [relationQueryStep, builtinRelationTuples,
    missing_evaluation_tuples_exact,
    ifMatchBindings, evaluationFault, evaluationValue,
    StructuredC.v, StructuredC.a,
    matchRelationArgs, matchRelationArgument, matchPattern,
    Bindings.lookup,
    applyBindings, mergeBindings]

theorem missing_phase_rewrite_exact
    (operation : CoreOp) (first second : Int) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1 (start operation first second) =
      [run (appendStatements nilStatements (afterMissing operation))
        (initialEnvironment first second) readyReceipt] := by
  rw [start_is_missing_phase]
  simpa [missingStatement, sc, StructuredC.a] using
    ifValueTransition_rewriteAt_exact
      (referenceEnv operation first second)
      missingCondition missingReceiptThen nilStatements
      (afterMissing operation) (initialEnvironment first second) readyReceipt
      falseValue (initialEnvironment first second) readyReceipt nilStatements
      (missing_evaluation_exact operation first second)
      (missing_selection_exact operation first second)
      (missing_fault_exact operation first second)

theorem missing_append_rewrite_exact
    (operation : CoreOp) (first second : Int) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (appendStatements nilStatements (afterMissing operation))
          (initialEnvironment first second) readyReceipt) =
      [run (afterMissing operation) (initialEnvironment first second)
        readyReceipt] :=
  appendEmptyTransition_rewriteAt_exact
    (referenceEnv operation first second) (afterMissing operation)
    (initialEnvironment first second) readyReceipt

private theorem begin_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_begin_v1"
            [variableExpression "receipt"],
         initialEnvironment first second, readyReceipt,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_begin_v1"
          [variableExpression "receipt"],
        initialEnvironment first second, readyReceipt,
        evaluationValue valueUnit, initialEnvironment first second,
        emptyReceipt]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, valueUnit, readyReceipt,
      initialEnvironment, sc, valueInteger, identifier, token]

private theorem record_zero_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression (valueInteger 0)],
         initialEnvironment first second, emptyReceipt,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression (valueInteger 0)],
        initialEnvironment first second, emptyReceipt,
        evaluationValue valueUnit, initialEnvironment first second,
        stepReceipt 0 emptyReceipt]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      emptyReceipt, stepReceipt, initialEnvironment, sc, valueInteger,
      identifier, token]

theorem begin_phase_rewrite_exact
    (operation : CoreOp) (first second : Int) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement beginStatement rest)
          (initialEnvironment first second) readyReceipt) =
      [run rest (initialEnvironment first second) emptyReceipt] := by
  simpa [beginStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_begin_v1"
        [variableExpression "receipt"])
      rest (initialEnvironment first second) readyReceipt valueUnit
      (initialEnvironment first second) emptyReceipt
      (begin_evaluation_tuples_exact operation first second)

theorem record_zero_phase_rewrite_exact
    (operation : CoreOp) (first second : Int) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement (recordStepStatement 0) rest)
          (initialEnvironment first second) emptyReceipt) =
      [run rest (initialEnvironment first second)
        (stepReceipt 0 emptyReceipt)] := by
  simpa [recordStepStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_record_step_v1"
        [variableExpression "receipt", constantExpression (valueInteger 0)])
      rest (initialEnvironment first second) emptyReceipt valueUnit
      (initialEnvironment first second) (stepReceipt 0 emptyReceipt)
      (record_zero_evaluation_tuples_exact operation first second)

private theorem invoke_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call (targetLinkName operation)
            [variableExpression "first", variableExpression "second",
             variableExpression "output"],
         initialEnvironment first second, receiptAtCall operation,
         result, outputEnvironment, outputReceipt] =
      [[call (targetLinkName operation)
          [variableExpression "first", variableExpression "second",
           variableExpression "output"],
        initialEnvironment first second, receiptAtCall operation,
        evaluationValue externalValueStatus,
        resultEnvironment operation first second, receiptAtCall operation]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, targetLinkName, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      externalValueStatus, receiptAtCall, receiptAfterExternal,
      receiptBeforeFinish, resultEnvironment, statusEnvironment,
      expectedReceipt, initialEnvironment, emptyReceipt, stepReceipt,
      externalReceipt, finishedReceipt, sc, valueInteger, valueSymbol,
      identifier, token] at defined ⊢

private theorem invoke_store_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (output : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCStore"
        [resultEnvironment operation first second, identifier "external_status",
         externalValueStatus, output] =
      [[resultEnvironment operation first second, identifier "external_status",
        externalValueStatus, statusEnvironment operation first second]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, storeRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, resultEnvironment,
      statusEnvironment, externalValueStatus, initialEnvironment,
      sc, valueInteger, valueSymbol, valueUnit, identifier, token]
      at defined ⊢

private theorem record_external_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_record_external_v1"
            [variableExpression "receipt",
             constantExpression (valueInteger (callProgramCounter operation)),
             constantExpression (valueInteger 0),
             variableExpression "external_status"],
         statusEnvironment operation first second, receiptAtCall operation,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_record_external_v1"
          [variableExpression "receipt",
           constantExpression (valueInteger (callProgramCounter operation)),
           constantExpression (valueInteger 0),
           variableExpression "external_status"],
        statusEnvironment operation first second, receiptAtCall operation,
        evaluationValue valueUnit, statusEnvironment operation first second,
        receiptAfterExternal operation]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, targetLinkName, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      expectedReceipt, initialEnvironment, emptyReceipt, stepReceipt,
      finishedReceipt, sc, valueInteger, identifier, token]
      at defined ⊢

private theorem status_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [variableExpression "external_status",
         statusEnvironment operation first second,
         receiptAfterExternal operation, result, outputEnvironment,
         outputReceipt] =
      [[variableExpression "external_status",
        statusEnvironment operation first second,
        receiptAfterExternal operation, evaluationValue externalValueStatus,
        statusEnvironment operation first second,
        receiptAfterExternal operation]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      externalValueStatus, callProgramCounter, valueProgramCounter,
      receiptAtCall, receiptAfterExternal, receiptBeforeFinish,
      resultEnvironment, statusEnvironment, expectedReceipt,
      initialEnvironment, emptyReceipt, stepReceipt, externalReceipt,
      finishedReceipt, sc, valueInteger, valueSymbol, identifier, token]
      at defined ⊢

private theorem result_case_tuples_exact
    (operation : CoreOp) (first second : Int) (output : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCSelectCase"
        [resultCases (valueProgramCounter operation), defaultCase,
         externalValueStatus, output] =
      [[resultCases (valueProgramCounter operation), defaultCase,
        externalValueStatus,
        statements [
          effect (call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression
              (valueInteger (valueProgramCounter operation))]),
          returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome])]]] := by
  cases operation <;>
    simp [referenceEnv, selectInputRows, caseRows, valueProgramCounter,
      resultCases, defaultCase, externalValueStatus, valueOutcome,
      statements, effect, returnExpression, call, externalName,
      expressionList, variableExpression, constantExpression, sc,
      valueInteger, valueSymbol, identifier, token]

set_option maxHeartbeats 1000000 in
private theorem record_value_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression
              (valueInteger (valueProgramCounter operation))],
         statusEnvironment operation first second,
         receiptAfterExternal operation, result, outputEnvironment,
         outputReceipt] =
      [[call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression
            (valueInteger (valueProgramCounter operation))],
        statusEnvironment operation first second,
        receiptAfterExternal operation, evaluationValue valueUnit,
        statusEnvironment operation first second,
        receiptBeforeFinish operation]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, targetLinkName, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      externalValueStatus, callProgramCounter, valueProgramCounter,
      receiptAtCall, receiptAfterExternal, receiptBeforeFinish,
      resultEnvironment, statusEnvironment, expectedReceipt,
      initialEnvironment, emptyReceipt, stepReceipt, externalReceipt,
      finishedReceipt, sc, valueInteger, valueSymbol, identifier, token]
      at defined ⊢

set_option maxHeartbeats 1000000 in
private theorem finish_value_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome],
         statusEnvironment operation first second,
         receiptBeforeFinish operation, result, outputEnvironment,
         outputReceipt] =
      [[call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome],
        statusEnvironment operation first second,
        receiptBeforeFinish operation, evaluationValue valueOutcome,
        statusEnvironment operation first second,
        expectedReceipt operation second]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, targetLinkName, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      externalValueStatus, valueOutcome, callProgramCounter,
      valueProgramCounter, receiptAtCall, receiptAfterExternal,
      receiptBeforeFinish, resultEnvironment, statusEnvironment,
      expectedReceipt, initialEnvironment, emptyReceipt, stepReceipt,
      externalReceipt, finishedReceipt, sc, valueInteger, valueSymbol,
      identifier, token] at defined ⊢

theorem invoke_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement (invokeStatement operation) rest)
          (initialEnvironment first second) (receiptAtCall operation)) =
      [run rest (statusEnvironment operation first second)
        (receiptAtCall operation)] := by
  simpa [invokeStatement, sc, StructuredC.a] using
    declareValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (identifier "external_status")
      (namedType "CettaExternalCallGeneratedExternalV1")
      (call (targetLinkName operation)
        [variableExpression "first", variableExpression "second",
         variableExpression "output"])
      rest (initialEnvironment first second) (receiptAtCall operation)
      externalValueStatus (resultEnvironment operation first second)
      (receiptAtCall operation) (statusEnvironment operation first second)
      (invoke_evaluation_tuples_exact operation first second defined)
      (invoke_store_tuples_exact operation first second defined)

theorem record_external_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement
          (recordExternalStatement (callProgramCounter operation)) rest)
          (statusEnvironment operation first second) (receiptAtCall operation)) =
      [run rest (statusEnvironment operation first second)
        (receiptAfterExternal operation)] := by
  simpa [recordExternalStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_record_external_v1"
        [variableExpression "receipt",
         constantExpression (valueInteger (callProgramCounter operation)),
         constantExpression (valueInteger 0),
         variableExpression "external_status"])
      rest (statusEnvironment operation first second) (receiptAtCall operation)
      valueUnit (statusEnvironment operation first second)
      (receiptAfterExternal operation)
      (record_external_evaluation_tuples_exact operation first second defined)

theorem dispatch_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement (dispatchStatement operation) rest)
          (statusEnvironment operation first second)
          (receiptAfterExternal operation)) =
      [run (appendStatements
          (statements [
            effect (call "cetta_external_call_generated_record_step_v1"
              [variableExpression "receipt", constantExpression
                (valueInteger (valueProgramCounter operation))]),
            returnExpression (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])])
          rest)
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)] := by
  simpa [dispatchStatement, sc, StructuredC.a] using
    switchValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (variableExpression "external_status")
      (resultCases (valueProgramCounter operation)) defaultCase rest
      (statusEnvironment operation first second) (receiptAfterExternal operation)
      externalValueStatus (statusEnvironment operation first second)
      (receiptAfterExternal operation)
      (statements [
        effect (call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression
            (valueInteger (valueProgramCounter operation))]),
        returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome])])
      (status_evaluation_tuples_exact operation first second defined)
      (result_case_tuples_exact operation first second)

theorem record_value_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement
          (recordStepStatement (valueProgramCounter operation)) rest)
          (statusEnvironment operation first second)
          (receiptAfterExternal operation)) =
      [run rest (statusEnvironment operation first second)
        (receiptBeforeFinish operation)] := by
  simpa [recordStepStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_record_step_v1"
        [variableExpression "receipt", constantExpression
          (valueInteger (valueProgramCounter operation))])
      rest (statusEnvironment operation first second)
      (receiptAfterExternal operation) valueUnit
      (statusEnvironment operation first second) (receiptBeforeFinish operation)
      (record_value_evaluation_tuples_exact operation first second defined)

theorem finish_value_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome])) rest)
          (statusEnvironment operation first second)
          (receiptBeforeFinish operation)) =
      [halted (sc "structured-c:outcome-return" [valueOutcome])
        (statusEnvironment operation first second)
        (expectedReceipt operation second)] := by
  simpa [returnExpression, sc, StructuredC.a] using
    returnValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_finish_v1"
        [variableExpression "receipt", constantExpression valueOutcome])
      rest (statusEnvironment operation first second)
      (receiptBeforeFinish operation) valueOutcome
      (statusEnvironment operation first second) (expectedReceipt operation second)
      (finish_value_evaluation_tuples_exact operation first second defined)

private def zeroTestValue (operation : CoreOp) (second : Int) : Pattern :=
  if targetUndefinedAt operation second then trueValue else falseValue

private def zeroSelectedBranch (operation : CoreOp) (second : Int) : Pattern :=
  if targetUndefinedAt operation second then guardThen else nilStatements

private theorem zero_test_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_exact_integer_is_zero_v1"
            [variableExpression "second"],
         initialEnvironment first second, stepReceipt 0 emptyReceipt,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_exact_integer_is_zero_v1"
          [variableExpression "second"],
        initialEnvironment first second, stepReceipt 0 emptyReceipt,
        evaluationValue (zeroTestValue operation second),
        initialEnvironment first second, stepReceipt 0 emptyReceipt]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, zeroTestValue, call,
      targetLinkName, externalName, expressionList, variableExpression,
      constantExpression, valueUnit, trueValue, falseValue,
      externalValueStatus, callProgramCounter, valueProgramCounter,
      receiptAtCall, receiptAfterExternal, receiptBeforeFinish,
      resultEnvironment, statusEnvironment, expectedReceipt,
      initialEnvironment, emptyReceipt, stepReceipt, externalReceipt,
      finishedReceipt, sc, valueInteger, valueSymbol, identifier, token]
      at hPartial ⊢

private theorem zero_branch_tuples_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (output : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCSelectBranch"
        [zeroTestValue operation second, guardThen, nilStatements, output] =
      [[zeroTestValue operation second, guardThen, nilStatements,
        zeroSelectedBranch operation second]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, branchRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, zeroTestValue,
      zeroSelectedBranch, trueValue, falseValue,
      missingReceiptThen_ne_guardThen,
      valueSymbol, identifier, token, sc] at hPartial ⊢

private theorem record_two_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression (valueInteger 2)],
         initialEnvironment first second, stepReceipt 0 emptyReceipt,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression (valueInteger 2)],
        initialEnvironment first second, stepReceipt 0 emptyReceipt,
        evaluationValue valueUnit, initialEnvironment first second,
        receiptAtCall operation]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      expectedReceipt,
      initialEnvironment, emptyReceipt, stepReceipt,
      finishedReceipt, sc, valueInteger, identifier, token]
      at hPartial defined ⊢

private theorem record_one_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_record_step_v1"
            [variableExpression "receipt", constantExpression (valueInteger 1)],
         initialEnvironment first second, stepReceipt 0 emptyReceipt,
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_record_step_v1"
          [variableExpression "receipt", constantExpression (valueInteger 1)],
        initialEnvironment first second, stepReceipt 0 emptyReceipt,
        evaluationValue valueUnit, initialEnvironment first second,
        stepReceipt 1 (stepReceipt 0 emptyReceipt)]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      expectedReceipt, initialEnvironment, emptyReceipt, stepReceipt,
      finishedReceipt, sc, valueInteger, identifier, token]
      at hPartial undefined ⊢

private theorem finish_declined_evaluation_tuples_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second)
    (result outputEnvironment outputReceipt : Pattern) :
    (referenceEnv operation first second).tuples "StructuredCEvaluate"
        [call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression declinedOutcome],
         initialEnvironment first second,
         stepReceipt 1 (stepReceipt 0 emptyReceipt),
         result, outputEnvironment, outputReceipt] =
      [[call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression declinedOutcome],
        initialEnvironment first second,
        stepReceipt 1 (stepReceipt 0 emptyReceipt),
        evaluationValue declinedOutcome, initialEnvironment first second,
        expectedReceipt operation second]] := by
  cases operation <;> by_cases zero : second = 0 <;>
    simp [referenceEnv, selectInputRows, evaluateRows, targetUndefinedAt_iff,
      undefinedAt, CoreOp.isPartial, zero, call, externalName,
      expressionList, variableExpression, constantExpression, valueUnit,
      declinedOutcome,
      expectedReceipt, initialEnvironment, emptyReceipt, stepReceipt,
      finishedReceipt, sc, valueInteger, valueSymbol,
      identifier, token] at hPartial undefined ⊢

theorem zero_guard_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement zeroGuardStatement rest)
          (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) =
      [run (appendStatements (zeroSelectedBranch operation second) rest)
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)] := by
  simpa [zeroGuardStatement, sc, StructuredC.a] using
    ifValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_exact_integer_is_zero_v1"
        [variableExpression "second"])
      guardThen nilStatements rest (initialEnvironment first second)
      (stepReceipt 0 emptyReceipt) (zeroTestValue operation second)
      (initialEnvironment first second) (stepReceipt 0 emptyReceipt)
      (zeroSelectedBranch operation second)
      (zero_test_evaluation_tuples_exact operation first second hPartial)
      (by
        intro output
        exact zero_branch_tuples_exact operation first second hPartial output)

theorem record_two_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement (recordStepStatement 2) rest)
          (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) =
      [run rest (initialEnvironment first second) (receiptAtCall operation)] := by
  simpa [recordStepStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_record_step_v1"
        [variableExpression "receipt", constantExpression (valueInteger 2)])
      rest (initialEnvironment first second) (stepReceipt 0 emptyReceipt)
      valueUnit (initialEnvironment first second) (receiptAtCall operation)
      (record_two_evaluation_tuples_exact operation first second hPartial defined)

theorem record_one_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement (recordStepStatement 1) rest)
          (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) =
      [run rest (initialEnvironment first second)
        (stepReceipt 1 (stepReceipt 0 emptyReceipt))] := by
  simpa [recordStepStatement, effect, sc, StructuredC.a] using
    effectValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_record_step_v1"
        [variableExpression "receipt", constantExpression (valueInteger 1)])
      rest (initialEnvironment first second) (stepReceipt 0 emptyReceipt)
      valueUnit (initialEnvironment first second)
      (stepReceipt 1 (stepReceipt 0 emptyReceipt))
      (record_one_evaluation_tuples_exact operation first second hPartial undefined)

theorem finish_declined_phase_rewrite_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second) (rest : Pattern) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
        language 1
        (run (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression declinedOutcome]))
          rest)
          (initialEnvironment first second)
          (stepReceipt 1 (stepReceipt 0 emptyReceipt))) =
      [halted (sc "structured-c:outcome-return" [declinedOutcome])
        (initialEnvironment first second) (expectedReceipt operation second)] := by
  simpa [returnExpression, sc, StructuredC.a] using
    returnValueTransition_rewriteAt_exact_of_tuples
      (referenceEnv operation first second)
      (call "cetta_external_call_generated_finish_v1"
        [variableExpression "receipt", constantExpression declinedOutcome])
      rest (initialEnvironment first second)
      (stepReceipt 1 (stepReceipt 0 emptyReceipt)) declinedOutcome
      (initialEnvironment first second) (expectedReceipt operation second)
      (finish_declined_evaluation_tuples_exact operation first second hPartial
        undefined)

theorem addition_normalizes_for_all_integers (first second : Int) :
    normalizeFirstUsing (referenceEnv .add first second) language 1 32
      (start .add first second) = done .add first second := by
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt, missing_phase_rewrite_exact]
  simp only [missing_append_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 30
      (run (consStatement beginStatement
        (statements [recordStepStatement 0, invokeStatement .add,
          recordExternalStatement 0, dispatchStatement .add]))
        (initialEnvironment first second) readyReceipt) = _
  simp only [normalizeFirstAt, begin_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 29
      (run (consStatement (recordStepStatement 0)
        (statements [invokeStatement .add, recordExternalStatement 0,
          dispatchStatement .add]))
        (initialEnvironment first second) emptyReceipt) = _
  simp only [normalizeFirstAt, record_zero_phase_rewrite_exact]
  have defined : ¬ targetUndefinedAt CoreOp.add second := by
    simp [targetUndefinedAt_iff, undefinedAt, CoreOp.isPartial]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 28
      (run (consStatement (invokeStatement .add)
        (statements [recordExternalStatement 0, dispatchStatement .add]))
        (initialEnvironment first second) (receiptAtCall .add)) = _
  simp only [normalizeFirstAt, invoke_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 27
      (run (consStatement (recordExternalStatement 0)
        (statements [dispatchStatement .add]))
        (statusEnvironment .add first second) (receiptAtCall .add)) = _
  have recordExternalAdd :
      rewriteAt (engineBasePremises (referenceEnv .add first second))
          language 1
          (run (consStatement (recordExternalStatement 0)
            (statements [dispatchStatement .add]))
            (statusEnvironment .add first second) (receiptAtCall .add)) =
        [run (statements [dispatchStatement .add])
          (statusEnvironment .add first second)
          (receiptAfterExternal .add)] := by
    simpa [callProgramCounter, CoreOp.isPartial] using
      record_external_phase_rewrite_exact CoreOp.add first second defined
        (statements [dispatchStatement .add])
  rw [normalizeFirstAt, recordExternalAdd]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 26
      (run (consStatement (dispatchStatement .add) nilStatements)
        (statusEnvironment .add first second)
        (receiptAfterExternal .add)) = _
  simp only [normalizeFirstAt, dispatch_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 25
      (run (appendStatements
        (consStatement (recordStepStatement (valueProgramCounter .add))
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])]))
        nilStatements)
        (statusEnvironment .add first second)
        (receiptAfterExternal .add)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 24
      (run (consStatement (recordStepStatement (valueProgramCounter .add))
        (appendStatements
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])])
          nilStatements))
        (statusEnvironment .add first second)
        (receiptAfterExternal .add)) = _
  simp only [normalizeFirstAt,
    record_value_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 23
      (run (appendStatements
        (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome]))
          nilStatements)
        nilStatements)
        (statusEnvironment .add first second) (receiptBeforeFinish .add)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv .add first second)) language 1 22
      (run (consStatement
        (returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome]))
        (appendStatements nilStatements nilStatements))
        (statusEnvironment .add first second) (receiptBeforeFinish .add)) = _
  simp only [normalizeFirstAt,
    finish_value_phase_rewrite_exact _ _ _ defined]
  simp only [halted_rewriteAt_empty]
  simp [done, expectedOutcome, finalEnvironment, targetUndefinedAt_iff,
    undefinedAt, CoreOp.isPartial, sc]

private theorem total_after_missing_shape
    (operation : CoreOp) (total : operation.isPartial = false) :
    afterMissing operation =
      statements [beginStatement, recordStepStatement 0,
        invokeStatement operation, recordExternalStatement 0,
        dispatchStatement operation] := by
  cases operation <;> simp [afterMissing, operationStatements,
    callProgramCounter, CoreOp.isPartial] at total ⊢

private theorem total_receipt_at_call
    (operation : CoreOp) (total : operation.isPartial = false) :
    receiptAtCall operation = stepReceipt 0 emptyReceipt := by
  simp [receiptAtCall, total]

private theorem total_call_program_counter
    (operation : CoreOp) (total : operation.isPartial = false) :
    callProgramCounter operation = 0 := by
  simp [callProgramCounter, total]

theorem total_operation_normalizes
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) :
    normalizeFirstUsing (referenceEnv operation first second) language 1 32
      (start operation first second) = done operation first second := by
  have defined : ¬ targetUndefinedAt operation second := by
    rw [targetUndefinedAt_iff]
    simp [undefinedAt, total]
  have receiptAtCallEq := total_receipt_at_call operation total
  have callPcEq := total_call_program_counter operation total
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt, missing_phase_rewrite_exact]
  simp only [missing_append_rewrite_exact]
  rw [total_after_missing_shape operation total]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 30
      (run (consStatement beginStatement
        (statements [recordStepStatement 0, invokeStatement operation,
          recordExternalStatement 0, dispatchStatement operation]))
        (initialEnvironment first second) readyReceipt) = _
  simp only [normalizeFirstAt, begin_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 29
      (run (consStatement (recordStepStatement 0)
        (statements [invokeStatement operation, recordExternalStatement 0,
          dispatchStatement operation]))
        (initialEnvironment first second) emptyReceipt) = _
  simp only [normalizeFirstAt, record_zero_phase_rewrite_exact]
  rw [← receiptAtCallEq]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 28
      (run (consStatement (invokeStatement operation)
        (statements [recordExternalStatement 0, dispatchStatement operation]))
        (initialEnvironment first second) (receiptAtCall operation)) = _
  simp only [normalizeFirstAt, invoke_phase_rewrite_exact _ _ _ defined]
  rw [← callPcEq]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 27
      (run (consStatement
        (recordExternalStatement (callProgramCounter operation))
        (statements [dispatchStatement operation]))
        (statusEnvironment operation first second) (receiptAtCall operation)) = _
  simp only [normalizeFirstAt,
    record_external_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 26
      (run (consStatement (dispatchStatement operation) nilStatements)
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt, dispatch_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 25
      (run (appendStatements
        (consStatement (recordStepStatement (valueProgramCounter operation))
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])]))
        nilStatements)
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 24
      (run (consStatement (recordStepStatement (valueProgramCounter operation))
        (appendStatements
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])])
          nilStatements))
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt,
    record_value_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 23
      (run (appendStatements
        (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome]))
          nilStatements)
        nilStatements)
        (statusEnvironment operation first second)
        (receiptBeforeFinish operation)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 22
      (run (consStatement
        (returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome]))
        (appendStatements nilStatements nilStatements))
        (statusEnvironment operation first second)
        (receiptBeforeFinish operation)) = _
  simp only [normalizeFirstAt,
    finish_value_phase_rewrite_exact _ _ _ defined]
  simp only [halted_rewriteAt_empty]
  simp [done, expectedOutcome, finalEnvironment, defined, sc]

private theorem partial_after_missing_shape
    (operation : CoreOp) (hPartial : operation.isPartial = true) :
    afterMissing operation =
      statements [beginStatement, recordStepStatement 0, zeroGuardStatement,
        recordStepStatement 2, invokeStatement operation,
        recordExternalStatement 2, dispatchStatement operation] := by
  cases operation <;> simp [afterMissing, operationStatements,
    callProgramCounter, CoreOp.isPartial] at hPartial ⊢

private theorem partial_call_program_counter
    (operation : CoreOp) (hPartial : operation.isPartial = true) :
    callProgramCounter operation = 2 := by
  simp [callProgramCounter, hPartial]

theorem undefined_partial_operation_normalizes
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second) :
    normalizeFirstUsing (referenceEnv operation first second) language 1 32
      (start operation first second) = done operation first second := by
  have selectedGuard : zeroSelectedBranch operation second = guardThen := by
    simp [zeroSelectedBranch, undefined]
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt, missing_phase_rewrite_exact]
  simp only [missing_append_rewrite_exact]
  rw [partial_after_missing_shape operation hPartial]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 30
      (run (consStatement beginStatement
        (statements [recordStepStatement 0, zeroGuardStatement,
          recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) readyReceipt) = _
  simp only [normalizeFirstAt, begin_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 29
      (run (consStatement (recordStepStatement 0)
        (statements [zeroGuardStatement, recordStepStatement 2,
          invokeStatement operation, recordExternalStatement 2,
          dispatchStatement operation]))
        (initialEnvironment first second) emptyReceipt) = _
  simp only [normalizeFirstAt, record_zero_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 28
      (run (consStatement zeroGuardStatement
        (statements [recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) = _
  simp only [normalizeFirstAt,
    zero_guard_phase_rewrite_exact _ _ _ hPartial]
  rw [selectedGuard]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 27
      (run (appendStatements
        (consStatement (recordStepStatement 1)
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression
                declinedOutcome])]))
        (statements [recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 26
      (run (consStatement (recordStepStatement 1)
        (appendStatements
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression
                declinedOutcome])])
          (statements [recordStepStatement 2, invokeStatement operation,
            recordExternalStatement 2, dispatchStatement operation])))
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) = _
  simp only [normalizeFirstAt,
    record_one_phase_rewrite_exact _ _ _ hPartial undefined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 25
      (run (appendStatements
        (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression declinedOutcome]))
          nilStatements)
        (statements [recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second)
        (stepReceipt 1 (stepReceipt 0 emptyReceipt))) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 24
      (run (consStatement
        (returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression declinedOutcome]))
        (appendStatements nilStatements
          (statements [recordStepStatement 2, invokeStatement operation,
            recordExternalStatement 2, dispatchStatement operation])))
        (initialEnvironment first second)
        (stepReceipt 1 (stepReceipt 0 emptyReceipt))) = _
  simp only [normalizeFirstAt,
    finish_declined_phase_rewrite_exact _ _ _ hPartial undefined]
  simp only [halted_rewriteAt_empty]
  simp [done, expectedOutcome, finalEnvironment, undefined, sc]

theorem defined_partial_operation_normalizes
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second) :
    normalizeFirstUsing (referenceEnv operation first second) language 1 32
      (start operation first second) = done operation first second := by
  have selectedEmpty : zeroSelectedBranch operation second = nilStatements := by
    simp [zeroSelectedBranch, defined]
  have callPcEq := partial_call_program_counter operation hPartial
  unfold normalizeFirstUsing
  simp only [normalizeFirstAt, missing_phase_rewrite_exact]
  simp only [missing_append_rewrite_exact]
  rw [partial_after_missing_shape operation hPartial]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 30
      (run (consStatement beginStatement
        (statements [recordStepStatement 0, zeroGuardStatement,
          recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) readyReceipt) = _
  simp only [normalizeFirstAt, begin_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 29
      (run (consStatement (recordStepStatement 0)
        (statements [zeroGuardStatement, recordStepStatement 2,
          invokeStatement operation, recordExternalStatement 2,
          dispatchStatement operation]))
        (initialEnvironment first second) emptyReceipt) = _
  simp only [normalizeFirstAt, record_zero_phase_rewrite_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 28
      (run (consStatement zeroGuardStatement
        (statements [recordStepStatement 2, invokeStatement operation,
          recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) = _
  simp only [normalizeFirstAt,
    zero_guard_phase_rewrite_exact _ _ _ hPartial]
  rw [selectedEmpty]
  simp only [appendEmptyTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 26
      (run (consStatement (recordStepStatement 2)
        (statements [invokeStatement operation, recordExternalStatement 2,
          dispatchStatement operation]))
        (initialEnvironment first second) (stepReceipt 0 emptyReceipt)) = _
  simp only [normalizeFirstAt,
    record_two_phase_rewrite_exact _ _ _ hPartial defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 25
      (run (consStatement (invokeStatement operation)
        (statements [recordExternalStatement 2, dispatchStatement operation]))
        (initialEnvironment first second) (receiptAtCall operation)) = _
  simp only [normalizeFirstAt, invoke_phase_rewrite_exact _ _ _ defined]
  rw [← callPcEq]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 24
      (run (consStatement
        (recordExternalStatement (callProgramCounter operation))
        (statements [dispatchStatement operation]))
        (statusEnvironment operation first second) (receiptAtCall operation)) = _
  simp only [normalizeFirstAt,
    record_external_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 23
      (run (consStatement (dispatchStatement operation) nilStatements)
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt, dispatch_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 22
      (run (appendStatements
        (consStatement (recordStepStatement (valueProgramCounter operation))
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])]))
        nilStatements)
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 21
      (run (consStatement (recordStepStatement (valueProgramCounter operation))
        (appendStatements
          (statements [returnExpression
            (call "cetta_external_call_generated_finish_v1"
              [variableExpression "receipt", constantExpression valueOutcome])])
          nilStatements))
        (statusEnvironment operation first second)
        (receiptAfterExternal operation)) = _
  simp only [normalizeFirstAt,
    record_value_phase_rewrite_exact _ _ _ defined]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 20
      (run (appendStatements
        (consStatement
          (returnExpression (call "cetta_external_call_generated_finish_v1"
            [variableExpression "receipt", constantExpression valueOutcome]))
          nilStatements)
        nilStatements)
        (statusEnvironment operation first second)
        (receiptBeforeFinish operation)) = _
  simp only [normalizeFirstAt, appendConsTransition_rewriteAt_exact]
  change normalizeFirstAt
      (engineBasePremises (referenceEnv operation first second)) language 1 19
      (run (consStatement
        (returnExpression (call "cetta_external_call_generated_finish_v1"
          [variableExpression "receipt", constantExpression valueOutcome]))
        (appendStatements nilStatements nilStatements))
        (statusEnvironment operation first second)
        (receiptBeforeFinish operation)) = _
  simp only [normalizeFirstAt,
    finish_value_phase_rewrite_exact _ _ _ defined]
  simp only [halted_rewriteAt_empty]
  simp [done, expectedOutcome, finalEnvironment, defined, sc]

theorem generated_function_normalizes
    (operation : CoreOp) (first second : Int) :
    normalizeFirstUsing (referenceEnv operation first second) language 1 32
      (start operation first second) = done operation first second := by
  by_cases hPartial : operation.isPartial = true
  · by_cases undefined : targetUndefinedAt operation second
    · exact undefined_partial_operation_normalizes operation first second
        hPartial undefined
    · exact defined_partial_operation_normalizes operation first second
        hPartial undefined
  · have total : operation.isPartial = false :=
      Bool.eq_false_of_not_eq_true hPartial
    exact total_operation_normalizes operation first second total

theorem generated_function_outcome_receipt_no_invention
    (operation : CoreOp) (first second : Int)
    (outcome environment receipt : Pattern)
    (execution :
      normalizeFirstUsing (referenceEnv operation first second) language 1 32
          (start operation first second) =
        halted outcome environment receipt) :
    outcome = sc "structured-c:outcome-return"
        [expectedOutcome operation second] ∧
      environment = finalEnvironment operation first second ∧
      receipt = expectedReceipt operation second := by
  rw [generated_function_normalizes] at execution
  simpa [done, halted, sc, StructuredC.a] using execution.symm

theorem generated_function_done_has_no_reducts
    (operation : CoreOp) (first second : Int) :
    rewriteAt (engineBasePremises (referenceEnv operation first second))
      language 1 (done operation first second) = [] := by
  simpa [done, sc, StructuredC.a] using
    halted_rewriteAt_empty (referenceEnv operation first second)
      (sc "structured-c:outcome-return" [expectedOutcome operation second])
      (finalEnvironment operation first second)
      (expectedReceipt operation second)

theorem addition_two_three_executes_exactly :
    normalizeFirstUsing (referenceEnv .add 2 3) language 1 32
      (start .add 2 3) = done .add 2 3 := by
  exact generated_function_normalizes .add 2 3

theorem tquot_seven_zero_executes_exactly :
    normalizeFirstUsing (referenceEnv .tquot 7 0) language 1 32
      (start .tquot 7 0) = done .tquot 7 0 := by
  exact generated_function_normalizes .tquot 7 0

theorem tquot_seven_two_executes_exactly :
    normalizeFirstUsing (referenceEnv .tquot 7 2) language 1 32
      (start .tquot 7 2) = done .tquot 7 2 := by
  exact generated_function_normalizes .tquot 7 2

theorem missing_handler_is_stuck :
    rewriteAt (engineBasePremises RelationEnv.empty) language 1
      (start .add 2 3) = [] := by
  decide +kernel

#print axioms addition_two_three_executes_exactly
#print axioms tquot_seven_zero_executes_exactly
#print axioms tquot_seven_two_executes_exactly
#print axioms missing_handler_is_stuck
#print axioms evaluateRows_input_keys_unique
#print axioms branchRows_input_keys_unique
#print axioms caseRows_input_keys_unique
#print axioms storeRows_input_keys_unique
#print axioms generated_function_normalizes
#print axioms generated_function_outcome_receipt_no_invention
#print axioms generated_function_done_has_no_reducts

end Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredCSemantics
