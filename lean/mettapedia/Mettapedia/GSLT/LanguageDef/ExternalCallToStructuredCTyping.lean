import Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredC
import Std.Data.String.ToInt

/-!
# Intrinsically typed StructuredC lowering

The executable lowering builds ordinary `Pattern` values.  This companion
reconstructs the same target program through typed constructor combinators.
The final equality says that the executable output is exactly that intrinsically
typed program, rather than a lookalike checked by a separate signature table.
-/

namespace Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredCTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall

structure Typed (sort : String) where
  pattern : Pattern
  typing : CarrierWellSorted.HasType StructuredC.language
    WellSorted.FreeTypeContext.empty [] pattern (.base sort)

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def mk0 (label result : String)
    (membership : StructuredC.ctor label result [] ∈ StructuredC.language.terms) :
    Typed result := {
  pattern := a label
  typing := by
    apply CarrierWellSorted.HasType.constructor
      (rule := StructuredC.ctor label result [])
    · exact membership
    · simp [WellSorted.UsesBareCollection, StructuredC.ctor]
    · exact .nil
}

private def mk1 (label result firstName firstSort : String)
    (first : Typed firstSort)
    (membership : StructuredC.ctor label result
      [(firstName, firstSort)] ∈ StructuredC.language.terms) : Typed result := {
  pattern := a label [first.pattern]
  typing := by
    apply CarrierWellSorted.HasType.constructor
      (rule := StructuredC.ctor label result [(firstName, firstSort)])
    · exact membership
    · simp [WellSorted.UsesBareCollection, StructuredC.ctor]
    · exact .cons True.intro rfl first.typing .nil
}

private def mk2 (label result firstName firstSort secondName secondSort : String)
    (first : Typed firstSort) (second : Typed secondSort)
    (membership : StructuredC.ctor label result
      [(firstName, firstSort), (secondName, secondSort)] ∈
        StructuredC.language.terms) : Typed result := {
  pattern := a label [first.pattern, second.pattern]
  typing := by
    apply CarrierWellSorted.HasType.constructor
      (rule := StructuredC.ctor label result
        [(firstName, firstSort), (secondName, secondSort)])
    · exact membership
    · simp [WellSorted.UsesBareCollection, StructuredC.ctor]
    · exact .cons True.intro rfl first.typing
        (.cons True.intro rfl second.typing .nil)
}

private def mk3 (label result firstName firstSort secondName secondSort
    thirdName thirdSort : String)
    (first : Typed firstSort) (second : Typed secondSort)
    (third : Typed thirdSort)
    (membership : StructuredC.ctor label result
      [(firstName, firstSort), (secondName, secondSort),
       (thirdName, thirdSort)] ∈ StructuredC.language.terms) : Typed result := {
  pattern := a label [first.pattern, second.pattern, third.pattern]
  typing := by
    apply CarrierWellSorted.HasType.constructor
      (rule := StructuredC.ctor label result
        [(firstName, firstSort), (secondName, secondSort),
         (thirdName, thirdSort)])
    · exact membership
    · simp [WellSorted.UsesBareCollection, StructuredC.ctor]
    · exact .cons True.intro rfl first.typing
        (.cons True.intro rfl second.typing
          (.cons True.intro rfl third.typing .nil))
}

private def mk4 (label result firstName firstSort secondName secondSort
    thirdName thirdSort fourthName fourthSort : String)
    (first : Typed firstSort) (second : Typed secondSort)
    (third : Typed thirdSort) (fourth : Typed fourthSort)
    (membership : StructuredC.ctor label result
      [(firstName, firstSort), (secondName, secondSort),
       (thirdName, thirdSort), (fourthName, fourthSort)] ∈
        StructuredC.language.terms) : Typed result := {
  pattern := a label [first.pattern, second.pattern, third.pattern, fourth.pattern]
  typing := by
    apply CarrierWellSorted.HasType.constructor
      (rule := StructuredC.ctor label result
        [(firstName, firstSort), (secondName, secondSort),
         (thirdName, thirdSort), (fourthName, fourthSort)])
    · exact membership
    · simp [WellSorted.UsesBareCollection, StructuredC.ctor]
    · exact .cons True.intro rfl first.typing
        (.cons True.intro rfl second.typing
          (.cons True.intro rfl third.typing
            (.cons True.intro rfl fourth.typing .nil)))
}

private def stringAtom (value : String) : Typed "String" := {
  pattern := a value
  typing := .builtinAtom ⟨StructuredC.language.types[1],
    List.getElem_mem _, rfl, rfl⟩
}

private theorem natAtomAccepted (value : Nat) :
    CarrierWellSorted.carrierAcceptsAtom .builtinInt (toString value) = true := by
  simp [CarrierWellSorted.carrierAcceptsAtom, Nat.toInt?_repr]

private def integerAtom (value : Nat) : Typed "Integer" := {
  pattern := a (toString value)
  typing := .builtinAtom ⟨StructuredC.language.types[0],
    List.getElem_mem _, rfl, natAtomAccepted value⟩
}

private def identifier (name : String) : Typed "Identifier" :=
  mk1 "structured-c:identifier" "Identifier" "name" "String"
    (stringAtom name) (by simp [StructuredC.language, StructuredC.terms])

private def functionName (name : String) : Typed "FunctionName" :=
  mk1 "structured-c:function-name" "FunctionName" "name" "String"
    (stringAtom name) (by simp [StructuredC.language, StructuredC.terms])

private def externalName (name : String) : Typed "ExternalName" :=
  mk1 "structured-c:external-name" "ExternalName" "name" "String"
    (stringAtom name) (by simp [StructuredC.language, StructuredC.terms])

private def namedType (name : String) : Typed "CType" :=
  mk1 "structured-c:type-named" "CType" "name" "Identifier"
    (identifier name) (by simp [StructuredC.language, StructuredC.terms])

private def constType (target : Typed "CType") : Typed "CType" :=
  mk1 "structured-c:type-const" "CType" "target" "CType" target
    (by simp [StructuredC.language, StructuredC.terms])

private def pointerType (name : String) (isConst : Bool) : Typed "CType" :=
  let target := if isConst then constType (namedType name) else namedType name
  mk1 "structured-c:type-pointer" "CType" "target" "CType" target
    (by simp [StructuredC.language, StructuredC.terms])

private def valueInteger (value : Nat) : Typed "Value" :=
  mk1 "structured-c:value-integer" "Value" "value" "Integer"
    (integerAtom value) (by simp [StructuredC.language, StructuredC.terms])

private def valueSymbol (name : String) : Typed "Value" :=
  mk1 "structured-c:value-symbol" "Value" "name" "Identifier"
    (identifier name) (by simp [StructuredC.language, StructuredC.terms])

private def variableExpression (name : String) : Typed "Expression" :=
  mk1 "structured-c:expression-variable" "Expression" "name" "Identifier"
    (identifier name) (by simp [StructuredC.language, StructuredC.terms])

private def constantExpression (value : Typed "Value") : Typed "Expression" :=
  mk1 "structured-c:expression-constant" "Expression" "value" "Value" value
    (by simp [StructuredC.language, StructuredC.terms])

private def expressionList : List (Typed "Expression") → Typed "Expressions"
  | [] => mk0 "structured-c:expressions-nil" "Expressions"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest =>
      mk2 "structured-c:expressions-cons" "Expressions"
        "expression" "Expression" "rest" "Expressions" item
        (expressionList rest) (by simp [StructuredC.language, StructuredC.terms])

private def call (name : String)
    (arguments : List (Typed "Expression")) : Typed "Expression" :=
  mk2 "structured-c:expression-call" "Expression"
    "function" "ExternalName" "arguments" "Expressions"
    (externalName name) (expressionList arguments)
    (by simp [StructuredC.language, StructuredC.terms])

private def statements : List (Typed "Statement") → Typed "Statements"
  | [] => mk0 "structured-c:statements-nil" "Statements"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest =>
      mk2 "structured-c:statements-cons" "Statements"
        "statement" "Statement" "rest" "Statements" item
        (statements rest) (by simp [StructuredC.language, StructuredC.terms])

private def effect (expression : Typed "Expression") : Typed "Statement" :=
  mk1 "structured-c:effect" "Statement" "expression" "Expression" expression
    (by simp [StructuredC.language, StructuredC.terms])

private def returnExpression
    (expression : Typed "Expression") : Typed "Statement" :=
  mk1 "structured-c:return" "Statement" "expression" "Expression" expression
    (by simp [StructuredC.language, StructuredC.terms])

private def ifStatement (condition : Typed "Expression")
    (thenBranch elseBranch : Typed "Statements") : Typed "Statement" :=
  mk3 "structured-c:if" "Statement" "condition" "Expression"
    "thenBranch" "Statements" "elseBranch" "Statements"
    condition thenBranch elseBranch
    (by simp [StructuredC.language, StructuredC.terms])

private def switchStatement (scrutinee : Typed "Expression")
    (cases : Typed "Cases") (defaultBranch : Typed "Statements") :
    Typed "Statement" :=
  mk3 "structured-c:switch" "Statement" "scrutinee" "Expression"
    "cases" "Cases" "defaultBranch" "Statements"
    scrutinee cases defaultBranch
    (by simp [StructuredC.language, StructuredC.terms])

private def declaration (name : String) (type : Typed "CType")
    (expression : Typed "Expression") : Typed "Statement" :=
  mk3 "structured-c:declare" "Statement" "variable" "Identifier"
    "type" "CType" "expression" "Expression"
    (identifier name) type expression
    (by simp [StructuredC.language, StructuredC.terms])

private def caseStatement (value : Typed "Value")
    (body : Typed "Statements") : Typed "Case" :=
  mk2 "structured-c:case" "Case" "value" "Value" "body" "Statements"
    value body (by simp [StructuredC.language, StructuredC.terms])

private def cases : List (Typed "Case") → Typed "Cases"
  | [] => mk0 "structured-c:cases-nil" "Cases"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest => mk2 "structured-c:cases-cons" "Cases"
      "case" "Case" "rest" "Cases" item (cases rest)
      (by simp [StructuredC.language, StructuredC.terms])

private def parameter (name typeName : String)
    (pointer isConst : Bool) : Typed "Parameter" :=
  let type := if pointer then pointerType typeName isConst else namedType typeName
  mk2 "structured-c:parameter" "Parameter" "name" "Identifier"
    "type" "CType" (identifier name) type
    (by simp [StructuredC.language, StructuredC.terms])

private def parameters : List (Typed "Parameter") → Typed "Parameters"
  | [] => mk0 "structured-c:parameters-nil" "Parameters"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest => mk2 "structured-c:parameters-cons" "Parameters"
      "parameter" "Parameter" "rest" "Parameters" item (parameters rest)
      (by simp [StructuredC.language, StructuredC.terms])

private def function (name returnType : String)
    (params : Typed "Parameters") (body : Typed "Statements") :
    Typed "Function" :=
  mk4 "structured-c:function" "Function" "name" "FunctionName"
    "returnType" "CType" "parameters" "Parameters" "body" "Statements"
    (functionName name) (namedType returnType) params body
    (by simp [StructuredC.language, StructuredC.terms])

private def externalFunction (name returnType : String)
    (params : Typed "Parameters") : Typed "ExternalFunction" :=
  mk3 "structured-c:external-function" "ExternalFunction"
    "name" "ExternalName" "returnType" "CType" "parameters" "Parameters"
    (externalName name) (namedType returnType) params
    (by simp [StructuredC.language, StructuredC.terms])

private def externalFunctions :
    List (Typed "ExternalFunction") → Typed "ExternalFunctions"
  | [] => mk0 "structured-c:external-functions-nil" "ExternalFunctions"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest => mk2 "structured-c:external-functions-cons"
      "ExternalFunctions" "function" "ExternalFunction"
      "rest" "ExternalFunctions" item (externalFunctions rest)
      (by simp [StructuredC.language, StructuredC.terms])

private def functions : List (Typed "Function") → Typed "Functions"
  | [] => mk0 "structured-c:functions-nil" "Functions"
      (by simp [StructuredC.language, StructuredC.terms])
  | item :: rest => mk2 "structured-c:functions-cons" "Functions"
      "function" "Function" "rest" "Functions" item (functions rest)
      (by simp [StructuredC.language, StructuredC.terms])

private def program (externals : Typed "ExternalFunctions")
    (body : Typed "Functions") : Typed "Program" :=
  mk2 "structured-c:program" "Program" "externals" "ExternalFunctions"
    "functions" "Functions" externals body
    (by simp [StructuredC.language, StructuredC.terms])

private def recordStep (programCounter : Nat) : Typed "Statement" :=
  effect (call "cetta_external_call_generated_record_step_v1"
    [variableExpression "receipt", constantExpression (valueInteger programCounter)])

private def recordExternal (programCounter : Nat) : Typed "Statement" :=
  effect (call "cetta_external_call_generated_record_external_v1"
    [variableExpression "receipt", constantExpression (valueInteger programCounter),
     constantExpression (valueInteger 0), variableExpression "external_status"])

private def finish (outcome : String) : Typed "Expression" :=
  call "cetta_external_call_generated_finish_v1"
    [variableExpression "receipt", constantExpression (valueSymbol outcome)]

private def outcomeCases (valueProgramCounter : Nat) : Typed "Cases" :=
  cases [
    caseStatement (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_VALUE_V1")
      (statements [recordStep valueProgramCounter,
        returnExpression (finish "CETTA_EXTERNAL_CALL_GENERATED_VALUE_V1")]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_LANGUAGE_FAULT_V1")
      (statements [recordStep (valueProgramCounter + 1),
        returnExpression (finish
          "CETTA_EXTERNAL_CALL_GENERATED_LANGUAGE_FAULT_V1")]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_ENGINE_FAULT_V1")
      (statements [recordStep (valueProgramCounter + 2),
        returnExpression (finish
          "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")]),
    caseStatement
      (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_EXTERNAL_RESOURCE_FAULT_V1")
      (statements [recordStep (valueProgramCounter + 3),
        returnExpression (finish
          "CETTA_EXTERNAL_CALL_GENERATED_RESOURCE_FAULT_V1")])]

private def generatedParameters : Typed "Parameters" := parameters [
  parameter "first" "CettaExternalCallExactIntegerV1" true true,
  parameter "second" "CettaExternalCallExactIntegerV1" true true,
  parameter "output" "CettaExternalCallExactIntegerV1" true false,
  parameter "receipt" "CettaExternalCallGeneratedReceiptV1" true false]

private def externalParameters : Typed "Parameters" := parameters [
  parameter "first" "CettaExternalCallExactIntegerV1" true true,
  parameter "second" "CettaExternalCallExactIntegerV1" true true,
  parameter "output" "CettaExternalCallExactIntegerV1" true false]

private def functionBody (operation : CoreOp) : Typed "Statements" :=
  let guarded := operation.isPartial
  let callPc := if guarded then 2 else 0
  let valuePc := if guarded then 3 else 1
  let missingReceipt := ifStatement
    (call "cetta_external_call_generated_receipt_missing_v1"
      [variableExpression "receipt"])
    (statements [returnExpression
      (constantExpression
        (valueSymbol "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1"))])
    (statements [])
  let beginReceipt := effect
    (call "cetta_external_call_generated_begin_v1"
      [variableExpression "receipt"])
  let guardedPrefix := [
    recordStep 0,
    ifStatement
      (call "cetta_external_call_exact_integer_is_zero_v1"
        [variableExpression "second"])
      (statements [recordStep 1,
        returnExpression (finish
          "CETTA_EXTERNAL_CALL_GENERATED_DECLINED_V1")])
      (statements [])]
  let invoke := declaration "external_status"
    (namedType "CettaExternalCallGeneratedExternalV1")
    (call (targetLinkName operation)
      [variableExpression "first", variableExpression "second",
       variableExpression "output"])
  let dispatch := switchStatement (variableExpression "external_status")
    (outcomeCases valuePc)
    (statements [
      effect (call "cetta_external_call_generated_mark_incomplete_v1"
        [variableExpression "receipt"]),
      returnExpression (finish
        "CETTA_EXTERNAL_CALL_GENERATED_ENGINE_FAULT_V1")])
  statements ([missingReceipt, beginReceipt] ++
    (if guarded then guardedPrefix else []) ++
    [recordStep callPc, invoke, recordExternal callPc, dispatch])

private def lowerCoreOperation (operation : CoreOp) : Typed "Function" :=
  function (ExternalCallToStructuredC.generatedFunctionName operation)
    "CettaExternalCallGeneratedOutcomeV1" generatedParameters
    (functionBody operation)

private def externalDeclaration (operation : CoreOp) : Typed "ExternalFunction" :=
  externalFunction (targetLinkName operation)
    "CettaExternalCallGeneratedExternalV1" externalParameters

private def arithmeticProgram : Typed "Program" :=
  program
    (externalFunctions (ExternalCallToStructuredC.operations.map externalDeclaration))
    (functions (ExternalCallToStructuredC.operations.map lowerCoreOperation))

private theorem lowerCoreOperation_pattern (operation : CoreOp) :
    (lowerCoreOperation operation).pattern = ExternalCallToStructuredC.lowerCoreOperation operation := by
  cases operation <;> rfl

private theorem functionBody_pattern (operation : CoreOp) :
    (functionBody operation).pattern =
      ExternalCallToStructuredC.lowerCoreOperationBody operation := by
  cases operation <;> rfl

theorem arithmeticProgram_pattern :
    arithmeticProgram.pattern = ExternalCallToStructuredC.arithmeticProgram := by
  rfl

theorem arithmeticProgram_target_typing :
    CarrierWellSorted.HasType StructuredC.language WellSorted.FreeTypeContext.empty []
      ExternalCallToStructuredC.arithmeticProgram (.base "Program") := by
  rw [← arithmeticProgram_pattern]
  exact arithmeticProgram.typing

#print axioms arithmeticProgram_target_typing

end Mettapedia.GSLT.LanguageDef.ExternalCallToStructuredCTyping
