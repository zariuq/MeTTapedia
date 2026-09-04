import Mettapedia.GSLT.LanguageDef.StructuredC
import Mettapedia.GSLT.LanguageDef.StructuredCBuilder

/-!
# Structural runtime relations for the flat StructuredC expression fragment

`StructuredC` exposes evaluation, storage, branch selection, and case
selection as relations.  This module supplies one structural implementation of
those relations.  It interprets constants and environment variables directly,
evaluates a flat list of constant/variable call operands from left to right,
and delegates only the named external primitive itself to an explicit handler.

The evaluator is deliberately partial.  Nested calls and malformed runtime
carriers fail closed instead of receiving an invented meaning.  Lowerings that
use this runtime must separately prove that their generated expressions stay
inside the admitted flat fragment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder

inductive EvaluationResult where
  | value (value : Pattern)
  | fault (fault : Pattern)
deriving DecidableEq, Repr

/-- The complete observable result of one expression evaluation. -/
structure EvaluationStep where
  result : EvaluationResult
  environment : Pattern
  receipt : Pattern
deriving DecidableEq, Repr

/-- External primitives receive already evaluated operands and return all
observable state changes explicitly. -/
abbrev ExternalHandler :=
  String → List Pattern → Pattern → Pattern → Option EvaluationStep

def identifierName? : Pattern → Option String
  | .apply "structured-c:identifier" [.apply name []] => some name
  | _ => none

def externalName? : Pattern → Option String
  | .apply "structured-c:external-name" [.apply name []] => some name
  | _ => none

def expressionList? : Pattern → Option (List Pattern)
  | .apply "structured-c:expressions-nil" [] => some []
  | .apply "structured-c:expressions-cons" [expression, rest] => do
      let expressions ← expressionList? rest
      pure (expression :: expressions)
  | _ => none

/-- The printable StructuredC expression-list builder is decoded exactly by
the structural runtime. -/
theorem expressionList?_expressions_exact (items : List Pattern) :
    expressionList? (expressions items) = some items := by
  induction items with
  | nil => simp [expressions, expressionList?, node]
  | cons item rest inductionHypothesis =>
      simp [expressions, expressionList?, node, inductionHypothesis]

def environmentEmpty : Pattern :=
  node "structured-c:environment-empty"

def environmentBind (identifier value rest : Pattern) : Pattern :=
  node "structured-c:environment-bind" [identifier, value, rest]

def bindName (name : String) (value rest : Pattern) : Pattern :=
  environmentBind (identifier name) value rest

/-- Lookup respects the usual newest-binding-wins environment discipline. -/
def lookup? (environment wanted : Pattern) : Option Pattern :=
  match environment with
  | .apply "structured-c:environment-empty" [] => none
  | .apply "structured-c:environment-bind" [found, value, rest] =>
      if found = wanted then some value else lookup? rest wanted
  | _ => none

/-- A freshly bound name shadows every older binding of the same name. -/
theorem lookup_bindName_same
    (name : String) (value environment : Pattern) :
    lookup? (bindName name value environment) (identifier name) = some value := by
  simp [lookup?, bindName, environmentBind, identifier, node, token]

/-- Looking up a distinct name passes through one persistent binding. -/
theorem lookup_bindName_of_ne
    (bound wanted : String) (value environment : Pattern)
    (different : bound ≠ wanted) :
    lookup? (bindName bound value environment) (identifier wanted) =
      lookup? environment (identifier wanted) := by
  simp [lookup?, bindName, environmentBind, identifier, node, token,
    different]

/-- Storage is persistent shadowing.  A malformed identifier is rejected. -/
def store? (environment slot value : Pattern) : Option Pattern := do
  let _ ← identifierName? slot
  pure (environmentBind slot value environment)

/-- Constants and variables are the admissible call operands. -/
def evaluateLeaf? (expression environment receipt : Pattern) :
    Option EvaluationStep :=
  match expression with
  | .apply "structured-c:expression-constant" [value] =>
      some ⟨.value value, environment, receipt⟩
  | .apply "structured-c:expression-variable" [slot] => do
      let _ ← identifierName? slot
      let value ← lookup? environment slot
      pure ⟨.value value, environment, receipt⟩
  | _ => none

/-- Evaluate a flat argument row from left to right.  Leaves are pure, but the
state threading remains explicit so the ordering contract is visible. -/
def evaluateLeaves? : List Pattern → Pattern → Pattern →
    Option (List Pattern × Pattern × Pattern)
  | [], environment, receipt => some ([], environment, receipt)
  | expression :: rest, environment, receipt => do
      let head ← evaluateLeaf? expression environment receipt
      match head.result with
      | .fault _ => none
      | .value value =>
          let tail ← evaluateLeaves? rest head.environment head.receipt
          pure (value :: tail.1, tail.2.1, tail.2.2)

/-- Structural evaluator for the admitted flat expression fragment. -/
def evaluate? (handler : ExternalHandler)
    (expression environment receipt : Pattern) : Option EvaluationStep :=
  match evaluateLeaf? expression environment receipt with
  | some result => some result
  | none =>
      match expression with
      | .apply "structured-c:expression-call" [external, arguments] => do
          let name ← externalName? external
          let argumentExpressions ← expressionList? arguments
          let evaluated ←
            evaluateLeaves? argumentExpressions environment receipt
          handler name evaluated.1 evaluated.2.1 evaluated.2.2
      | _ => none

def trueValue : Pattern := valueSymbol "true"
def falseValue : Pattern := valueSymbol "false"

def selectBranch? (value thenBranch elseBranch : Pattern) : Option Pattern :=
  if value = trueValue then some thenBranch
  else if value = falseValue then some elseBranch
  else none

/-- Select the first matching authored case, or the default after a
well-formed exhausted case list.  Malformed case syntax is rejected. -/
def selectCase? (value defaultBranch : Pattern) : Pattern → Option Pattern
  | .apply "structured-c:cases-nil" [] => some defaultBranch
  | .apply "structured-c:cases-cons"
      [.apply "structured-c:case" [candidate, body], rest] =>
      if candidate = value then some body
      else selectCase? value defaultBranch rest
  | _ => none

private def evaluationRows (handler : ExternalHandler) :
    List Pattern → List (List Pattern)
  | expression :: environment :: receipt :: _ =>
      match evaluate? handler expression environment receipt with
      | some step =>
          let encodedResult := match step.result with
            | .value value => evaluationValue value
            | .fault fault => evaluationFault fault
          [[expression, environment, receipt, encodedResult,
            step.environment, step.receipt]]
      | none => []
  | _ => []

private def storageRows : List Pattern → List (List Pattern)
  | environment :: slot :: value :: _ =>
      match store? environment slot value with
      | some next => [[environment, slot, value, next]]
      | none => []
  | _ => []

private def branchRows : List Pattern → List (List Pattern)
  | value :: thenBranch :: elseBranch :: _ =>
      match selectBranch? value thenBranch elseBranch with
      | some selected => [[value, thenBranch, elseBranch, selected]]
      | none => []
  | _ => []

private def caseRows : List Pattern → List (List Pattern)
  | authoredCases :: defaultBranch :: value :: _ =>
      match selectCase? value defaultBranch authoredCases with
      | some selected =>
          [[authoredCases, defaultBranch, value, selected]]
      | none => []
  | _ => []

/-- A computed relation environment for the actual StructuredC transition
rules.  No row catalog or expected execution trace is supplied. -/
def relationEnv (handler : ExternalHandler) : RelationEnv where
  tuples relation arguments :=
    if relation = "StructuredCEvaluate" then
      evaluationRows handler arguments
    else if relation = "StructuredCStore" then
      storageRows arguments
    else if relation = "StructuredCSelectBranch" then
      branchRows arguments
    else if relation = "StructuredCSelectCase" then
      caseRows arguments
    else
      []

/-! ## Exact relation projections -/

/-- The evaluation relation is exactly the graph of the structural evaluator.
This theorem exposes the computed row without requiring clients to unfold the
private relation-row implementation. -/
theorem relationEnv_evaluate_tuples
    (handler : ExternalHandler) (expression environment receipt
      result outputEnvironment outputReceipt : Pattern) :
    (relationEnv handler).tuples "StructuredCEvaluate"
      [expression, environment, receipt, result, outputEnvironment,
        outputReceipt] =
      match evaluate? handler expression environment receipt with
      | some step =>
          let encodedResult := match step.result with
            | .value value => evaluationValue value
            | .fault fault => evaluationFault fault
          [[expression, environment, receipt, encodedResult,
            step.environment, step.receipt]]
      | none => [] := by
  rfl

/-- The storage relation is exactly persistent shadowing on a well-formed
identifier. -/
theorem relationEnv_store_tuples
    (handler : ExternalHandler) (environment slot value output : Pattern) :
    (relationEnv handler).tuples "StructuredCStore"
      [environment, slot, value, output] =
      match store? environment slot value with
      | some next => [[environment, slot, value, next]]
      | none => [] := by
  rfl

/-- The branch relation is exactly structural Boolean selection. -/
theorem relationEnv_branch_tuples
    (handler : ExternalHandler)
    (value thenBranch elseBranch output : Pattern) :
    (relationEnv handler).tuples "StructuredCSelectBranch"
      [value, thenBranch, elseBranch, output] =
      match selectBranch? value thenBranch elseBranch with
      | some selected => [[value, thenBranch, elseBranch, selected]]
      | none => [] := by
  rfl

/-- The case relation is exactly first-match selection with an explicit
default branch. -/
theorem relationEnv_case_tuples
    (handler : ExternalHandler)
    (cases defaultBranch value output : Pattern) :
    (relationEnv handler).tuples "StructuredCSelectCase"
      [cases, defaultBranch, value, output] =
      match selectCase? value defaultBranch cases with
      | some selected => [[cases, defaultBranch, value, selected]]
      | none => [] := by
  rfl

/-- A flat one-variable external call evaluates exactly when lookup and the
external handler do.  This is the common admission shape for generated field
projections. -/
theorem evaluate_single_variable_call_exact
    (handler : ExternalHandler) (name slotName : String)
    (value environment receipt : Pattern) (step : EvaluationStep)
    (stored : lookup? environment (identifier slotName) = some value)
    (handled : handler name [value] environment receipt = some step) :
    evaluate? handler (call name [variableExpression slotName])
      environment receipt = some step := by
  have storedExpanded :
      lookup? environment
          (Pattern.apply "structured-c:identifier"
            [Pattern.apply slotName []]) = some value := by
    simpa [identifier, node, token] using stored
  simp [evaluate?, evaluateLeaf?, evaluateLeaves?, identifierName?,
    expressionList?, externalName?, call, externalName, expressions,
    variableExpression, identifier, node, token, storedExpanded, handled]

/-- A row of variable operands evaluates to the corresponding row of stored
values without changing the environment or receipt.  The `Forall₂` witness
retains the authored operand order and multiplicity. -/
theorem evaluateLeaves_variableExpressions_exact
    (names : List String) (values : List Pattern)
    (environment receipt : Pattern)
    (stored : List.Forall₂
      (fun name value =>
        lookup? environment (identifier name) = some value)
      names values) :
    evaluateLeaves? (names.map variableExpression) environment receipt =
      some (values, environment, receipt) := by
  induction stored with
  | nil =>
      simp [evaluateLeaves?]
  | @cons name value names values storedHead _ inductionHypothesis =>
      have storedExpanded :
          lookup? environment
              (Pattern.apply "structured-c:identifier"
                [Pattern.apply name []]) = some value := by
        simpa [identifier, node, token] using storedHead
      simp [evaluateLeaves?, evaluateLeaf?, identifierName?,
        variableExpression, identifier, node, token, storedExpanded,
        inductionHypothesis]

/-- Pointwise form of `evaluateLeaves_variableExpressions_exact`.  It is
useful when an authored operand row interleaves variables with other pure
leaves and therefore cannot be split into one variable prefix and one
constant suffix. -/
theorem evaluateLeaf_variableExpressions_exact
    (names : List String) (values : List Pattern)
    (environment receipt : Pattern)
    (stored : List.Forall₂
      (fun name value =>
        lookup? environment (identifier name) = some value)
      names values) :
    List.Forall₂
      (fun expression value =>
        evaluateLeaf? expression environment receipt =
          some ⟨.value value, environment, receipt⟩)
      (names.map variableExpression) values := by
  induction stored with
  | nil => simp
  | @cons name value names values storedHead _ inductionHypothesis =>
      have storedExpanded :
          lookup? environment
              (Pattern.apply "structured-c:identifier"
                [Pattern.apply name []]) = some value := by
        simpa [identifier, node, token] using storedHead
      constructor
      · simp [evaluateLeaf?, identifierName?, variableExpression, identifier,
          node, token, storedExpanded]
      · exact inductionHypothesis

/-- A row of constant operands evaluates to its authored values without
changing the environment or receipt. -/
theorem evaluateLeaves_constants_exact
    (values : List Pattern) (environment receipt : Pattern) :
    evaluateLeaves? (values.map constant) environment receipt =
      some (values, environment, receipt) := by
  induction values with
  | nil => simp [evaluateLeaves?]
  | cons value rest inductionHypothesis =>
      simp [evaluateLeaves?, evaluateLeaf?, constant, node,
        inductionHypothesis]

/-- A generated operand row may consist of an ordered variable prefix and an
ordered constant suffix.  Evaluation preserves both segments and their exact
multiplicity. -/
theorem evaluateLeaves_variableExpressions_append_constants_exact
    (names : List String) (values constants : List Pattern)
    (environment receipt : Pattern)
    (stored : List.Forall₂
      (fun name value =>
        lookup? environment (identifier name) = some value)
      names values) :
    evaluateLeaves?
        (names.map variableExpression ++ constants.map constant)
        environment receipt =
      some (values ++ constants, environment, receipt) := by
  induction stored with
  | nil =>
      simpa using evaluateLeaves_constants_exact constants environment receipt
  | @cons name value names values storedHead _ inductionHypothesis =>
      have storedExpanded :
          lookup? environment
              (Pattern.apply "structured-c:identifier"
                [Pattern.apply name []]) = some value := by
        simpa [identifier, node, token] using storedHead
      simp [evaluateLeaves?, evaluateLeaf?, identifierName?,
        variableExpression, identifier, node, token, storedExpanded,
        inductionHypothesis]

/-- Any flat operand row whose leaves are individually pure evaluates in the
same authored order.  This covers arbitrary mixtures of variables and
constants without introducing a second expression evaluator. -/
theorem evaluateLeaves_pure_exact
    (operandExpressions operandValues : List Pattern)
    (environment receipt : Pattern)
    (evaluated : List.Forall₂
      (fun expression value =>
        evaluateLeaf? expression environment receipt =
          some ⟨.value value, environment, receipt⟩)
      operandExpressions operandValues) :
    evaluateLeaves? operandExpressions environment receipt =
      some (operandValues, environment, receipt) := by
  induction evaluated with
  | nil => simp [evaluateLeaves?]
  | cons evaluatedHead _ inductionHypothesis =>
      simp [evaluateLeaves?, evaluatedHead, inductionHypothesis]

/-- A flat external call whose operands are authored variables evaluates
exactly when every lookup and the external handler do. -/
theorem evaluate_variable_call_exact
    (handler : ExternalHandler) (name : String)
    (names : List String) (values : List Pattern)
    (environment receipt : Pattern) (step : EvaluationStep)
    (stored : List.Forall₂
      (fun slot value =>
        lookup? environment (identifier slot) = some value)
      names values)
    (handled : handler name values environment receipt = some step) :
    evaluate? handler (call name (names.map variableExpression))
      environment receipt = some step := by
  have parsed := expressionList?_expressions_exact
    (names.map variableExpression)
  have evaluated := evaluateLeaves_variableExpressions_exact names values
    environment receipt stored
  simp [evaluate?, evaluateLeaf?, externalName?, call, externalName,
    node, token, parsed, evaluated, handled]

/-- A flat external call with a variable prefix and constant suffix evaluates
exactly when its lookups and external handler do. -/
theorem evaluate_variable_constant_call_exact
    (handler : ExternalHandler) (name : String)
    (names : List String) (values constants : List Pattern)
    (environment receipt : Pattern) (step : EvaluationStep)
    (stored : List.Forall₂
      (fun slot value =>
        lookup? environment (identifier slot) = some value)
      names values)
    (handled : handler name (values ++ constants) environment receipt =
      some step) :
    evaluate? handler
        (call name
          (names.map variableExpression ++ constants.map constant))
        environment receipt = some step := by
  have parsed := expressionList?_expressions_exact
    (names.map variableExpression ++ constants.map constant)
  have evaluated :=
    evaluateLeaves_variableExpressions_append_constants_exact names values
      constants environment receipt stored
  simp [evaluate?, evaluateLeaf?, externalName?, call, externalName,
    node, token, parsed, evaluated, handled]

/-- A flat call with an arbitrary pure variable/constant mixture evaluates
exactly when the leaf row and the named external handler agree. -/
theorem evaluate_pure_call_exact
    (handler : ExternalHandler) (name : String)
    (operandExpressions operandValues : List Pattern)
    (environment receipt : Pattern) (step : EvaluationStep)
    (evaluated : List.Forall₂
      (fun expression value =>
        evaluateLeaf? expression environment receipt =
          some ⟨.value value, environment, receipt⟩)
      operandExpressions operandValues)
    (handled : handler name operandValues environment receipt = some step) :
    evaluate? handler (call name operandExpressions) environment receipt =
      some step := by
  have parsed := expressionList?_expressions_exact operandExpressions
  have valuesExact := evaluateLeaves_pure_exact operandExpressions
    operandValues environment receipt evaluated
  simp [evaluate?, evaluateLeaf?, externalName?, call, externalName,
    node, token, parsed, valuesExact, handled]

/-- Constant expressions are pure structural evaluations, independently of
the external handler. -/
theorem evaluate_constant_exact
    (handler : ExternalHandler) (value environment receipt : Pattern) :
    evaluate? handler (constant value) environment receipt =
      some ⟨.value value, environment, receipt⟩ := by
  simp [evaluate?, evaluateLeaf?, constant, node]

/-- A printable symbolic constant evaluates to its exact symbolic value. -/
theorem evaluate_symbol_exact
    (handler : ExternalHandler) (name : String)
    (environment receipt : Pattern) :
    evaluate? handler (symbol name) environment receipt =
      some ⟨.value (valueSymbol name), environment, receipt⟩ := by
  simpa [symbol] using
    evaluate_constant_exact handler (valueSymbol name) environment receipt

namespace Canary

def echoHandler : ExternalHandler
  | "echo", [value], environment, receipt =>
      some ⟨.value value, environment, receipt⟩
  | _, _, _, _ => none

def sampleEnvironment : Pattern :=
  bindName "x" (valueSymbol "sample") environmentEmpty

theorem variable_lookup_positive :
    evaluate? echoHandler (variableExpression "x") sampleEnvironment
        (node "structured-c:receipt-ready") =
      some ⟨.value (valueSymbol "sample"), sampleEnvironment,
        node "structured-c:receipt-ready"⟩ := by
  decide +kernel

theorem missing_variable_negative :
    evaluate? echoHandler (variableExpression "missing") sampleEnvironment
        (node "structured-c:receipt-ready") = none := by
  decide +kernel

/-- Nested calls are outside the admitted fragment and fail closed. -/
theorem nested_call_operand_negative :
    evaluate? echoHandler
        (call "echo" [call "echo" [symbol "sample"]])
        sampleEnvironment (node "structured-c:receipt-ready") = none := by
  decide +kernel

end Canary

#print axioms Canary.variable_lookup_positive
#print axioms Canary.missing_variable_negative
#print axioms Canary.nested_call_operand_negative
#print axioms relationEnv_evaluate_tuples
#print axioms lookup_bindName_same
#print axioms lookup_bindName_of_ne
#print axioms relationEnv_store_tuples
#print axioms relationEnv_branch_tuples
#print axioms relationEnv_case_tuples
#print axioms expressionList?_expressions_exact
#print axioms evaluate_single_variable_call_exact
#print axioms evaluateLeaves_variableExpressions_exact
#print axioms evaluateLeaves_constants_exact
#print axioms evaluateLeaves_variableExpressions_append_constants_exact
#print axioms evaluateLeaves_pure_exact
#print axioms evaluate_variable_call_exact
#print axioms evaluate_variable_constant_call_exact
#print axioms evaluate_pure_call_exact
#print axioms evaluate_constant_exact
#print axioms evaluate_symbol_exact

end Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
