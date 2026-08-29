import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# A total-or-faulting structured C presentation

`StructuredC` is a small target language for generated C, not a claim to model
all of ISO C.  Programs contain explicit expressions, assignments, conditionals,
switches, statement lists, and returns.  Primitive evaluation is exposed through
relations whose result carrier contains only a value or an explicit fault; no
undefined-behavior result exists in the language.

The final rendering into compiler-accepted C is a separate realization.  Its
adequacy obligation is therefore visible rather than hidden inside this
presentation.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def v (name : String) : Pattern := .fvar name
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments
def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

def run (statements environment receipt : Pattern) : Pattern :=
  a "structured-c:run" [statements, environment, receipt]

def halted (outcome environment receipt : Pattern) : Pattern :=
  a "structured-c:halted" [outcome, environment, receipt]

def nilStatements : Pattern := a "structured-c:statements-nil"

def consStatement (statement statements : Pattern) : Pattern :=
  a "structured-c:statements-cons" [statement, statements]

def appendStatements (first second : Pattern) : Pattern :=
  a "structured-c:statements-append" [first, second]

def evaluationValue (value : Pattern) : Pattern :=
  a "structured-c:evaluation-value" [value]

def evaluationFault (fault : Pattern) : Pattern :=
  a "structured-c:evaluation-fault" [fault]

def commonContext : List (String × TypeExpr) := typed [
  ("environment", "Environment"), ("receipt", "Receipt"),
  ("rest", "Statements")]

def emptyTransition : RewriteRule := {
  name := "structured-c:finish"
  typeContext := typed [
    ("environment", "Environment"), ("receipt", "Receipt")]
  premises := []
  left := run nilStatements (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fallthrough")
    (v "environment") (v "receipt")
}

def appendEmptyTransition : RewriteRule := {
  name := "structured-c:append-empty"
  typeContext := typed [
    ("continuation", "Statements"), ("environment", "Environment"),
    ("receipt", "Receipt")]
  premises := []
  left := run (appendStatements nilStatements (v "continuation"))
    (v "environment") (v "receipt")
  right := run (v "continuation") (v "environment") (v "receipt")
}

def appendConsTransition : RewriteRule := {
  name := "structured-c:append-cons"
  typeContext := typed [
    ("statement", "Statement"), ("tail", "Statements"),
    ("continuation", "Statements"), ("environment", "Environment"),
    ("receipt", "Receipt")]
  premises := []
  left := run
    (appendStatements (consStatement (v "statement") (v "tail"))
      (v "continuation")) (v "environment") (v "receipt")
  right := run
    (consStatement (v "statement")
      (appendStatements (v "tail") (v "continuation")))
    (v "environment") (v "receipt")
}

def assignValueTransition : RewriteRule := {
  name := "structured-c:assign-value"
  typeContext := commonContext ++ typed [
    ("variable", "Identifier"), ("expression", "Expression"),
    ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt"),
    ("nextEnvironment", "Environment")]
  premises := [
    query "StructuredCEvaluate"
      [v "expression", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"],
    query "StructuredCStore"
      [v "evaluatedEnvironment", v "variable", v "value",
       v "nextEnvironment"]]
  left := run
    (consStatement
      (a "structured-c:assign" [v "variable", v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := run (v "rest") (v "nextEnvironment") (v "evaluatedReceipt")
}

def assignFaultTransition : RewriteRule := {
  name := "structured-c:assign-fault"
  typeContext := commonContext ++ typed [
    ("variable", "Identifier"), ("expression", "Expression"),
    ("fault", "Fault"), ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement
      (a "structured-c:assign" [v "variable", v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def declareValueTransition : RewriteRule := {
  name := "structured-c:declare-value"
  typeContext := commonContext ++ typed [
    ("variable", "Identifier"), ("type", "CType"),
    ("expression", "Expression"), ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt"),
    ("nextEnvironment", "Environment")]
  premises := [
    query "StructuredCEvaluate"
      [v "expression", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"],
    query "StructuredCStore"
      [v "evaluatedEnvironment", v "variable", v "value",
       v "nextEnvironment"]]
  left := run
    (consStatement
      (a "structured-c:declare" [v "variable", v "type", v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := run (v "rest") (v "nextEnvironment") (v "evaluatedReceipt")
}

def declareFaultTransition : RewriteRule := {
  name := "structured-c:declare-fault"
  typeContext := commonContext ++ typed [
    ("variable", "Identifier"), ("type", "CType"),
    ("expression", "Expression"), ("fault", "Fault"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement
      (a "structured-c:declare" [v "variable", v "type", v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def effectValueTransition : RewriteRule := {
  name := "structured-c:effect-value"
  typeContext := commonContext ++ typed [
    ("expression", "Expression"), ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationValue (v "value"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement (a "structured-c:effect" [v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := run (v "rest") (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def effectFaultTransition : RewriteRule := {
  name := "structured-c:effect-fault"
  typeContext := commonContext ++ typed [
    ("expression", "Expression"), ("fault", "Fault"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement (a "structured-c:effect" [v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def ifValueTransition : RewriteRule := {
  name := "structured-c:if-value"
  typeContext := commonContext ++ typed [
    ("condition", "Expression"), ("thenBranch", "Statements"),
    ("elseBranch", "Statements"), ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt"), ("selected", "Statements")]
  premises := [
    query "StructuredCEvaluate"
      [v "condition", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"],
    query "StructuredCSelectBranch"
      [v "value", v "thenBranch", v "elseBranch", v "selected"]]
  left := run
    (consStatement
      (a "structured-c:if"
        [v "condition", v "thenBranch", v "elseBranch"])
      (v "rest")) (v "environment") (v "receipt")
  right := run (appendStatements (v "selected") (v "rest"))
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def ifFaultTransition : RewriteRule := {
  name := "structured-c:if-fault"
  typeContext := commonContext ++ typed [
    ("condition", "Expression"), ("thenBranch", "Statements"),
    ("elseBranch", "Statements"), ("fault", "Fault"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "condition", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement
      (a "structured-c:if"
        [v "condition", v "thenBranch", v "elseBranch"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

/-- `while` is structural control, not a primitive oracle.  One step exposes
one conditional iteration while retaining the loop as target syntax in the
true branch.  Expression evaluation and explicit faults remain governed by
the same `StructuredCEvaluate` relation used by `if`. -/
def whileExpandTransition : RewriteRule := {
  name := "structured-c:while-expand"
  typeContext := commonContext ++ typed [
    ("condition", "Expression"), ("body", "Statements")]
  premises := []
  left := run
    (consStatement
      (a "structured-c:while" [v "condition", v "body"])
      (v "rest")) (v "environment") (v "receipt")
  right := run
    (consStatement
      (a "structured-c:if" [v "condition",
        appendStatements (v "body")
          (consStatement
            (a "structured-c:while" [v "condition", v "body"])
            nilStatements),
        nilStatements])
      (v "rest")) (v "environment") (v "receipt")
}

def switchValueTransition : RewriteRule := {
  name := "structured-c:switch-value"
  typeContext := commonContext ++ typed [
    ("scrutinee", "Expression"), ("cases", "Cases"),
    ("defaultBranch", "Statements"), ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt"), ("selected", "Statements")]
  premises := [
    query "StructuredCEvaluate"
      [v "scrutinee", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"],
    query "StructuredCSelectCase"
      [v "cases", v "defaultBranch", v "value", v "selected"]]
  left := run
    (consStatement
      (a "structured-c:switch"
        [v "scrutinee", v "cases", v "defaultBranch"])
      (v "rest")) (v "environment") (v "receipt")
  right := run (appendStatements (v "selected") (v "rest"))
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def switchFaultTransition : RewriteRule := {
  name := "structured-c:switch-fault"
  typeContext := commonContext ++ typed [
    ("scrutinee", "Expression"), ("cases", "Cases"),
    ("defaultBranch", "Statements"), ("fault", "Fault"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "scrutinee", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement
      (a "structured-c:switch"
        [v "scrutinee", v "cases", v "defaultBranch"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def returnValueTransition : RewriteRule := {
  name := "structured-c:return-value"
  typeContext := commonContext ++ typed [
    ("expression", "Expression"), ("value", "Value"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationValue (v "value"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement (a "structured-c:return" [v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-return" [v "value"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def returnFaultTransition : RewriteRule := {
  name := "structured-c:return-fault"
  typeContext := commonContext ++ typed [
    ("expression", "Expression"), ("fault", "Fault"),
    ("evaluatedEnvironment", "Environment"),
    ("evaluatedReceipt", "Receipt")]
  premises := [query "StructuredCEvaluate"
    [v "expression", v "environment", v "receipt",
     evaluationFault (v "fault"), v "evaluatedEnvironment",
     v "evaluatedReceipt"]]
  left := run
    (consStatement (a "structured-c:return" [v "expression"])
      (v "rest")) (v "environment") (v "receipt")
  right := halted (a "structured-c:outcome-fault" [v "fault"])
    (v "evaluatedEnvironment") (v "evaluatedReceipt")
}

def transitions : List RewriteRule := [
  emptyTransition,
  appendEmptyTransition,
  appendConsTransition,
  assignValueTransition,
  assignFaultTransition,
  declareValueTransition,
  declareFaultTransition,
  effectValueTransition,
  effectFaultTransition,
  ifValueTransition,
  ifFaultTransition,
  whileExpandTransition,
  switchValueTransition,
  switchFaultTransition,
  returnValueTransition,
  returnFaultTransition
]

def terms : List GrammarRule := [
  ctor "structured-c:identifier" "Identifier" [("name", "String")],
  ctor "structured-c:function-name" "FunctionName" [("name", "String")],
  ctor "structured-c:external-name" "ExternalName" [("name", "String")],
  ctor "structured-c:type-named" "CType" [("name", "Identifier")],
  ctor "structured-c:type-pointer" "CType" [("target", "CType")],
  ctor "structured-c:type-const" "CType" [("target", "CType")],
  ctor "structured-c:value-integer" "Value" [("value", "Integer")],
  ctor "structured-c:value-symbol" "Value" [("name", "Identifier")],
  ctor "structured-c:value-unit" "Value" [],
  ctor "structured-c:expression-variable" "Expression" [("name", "Identifier")],
  ctor "structured-c:expression-constant" "Expression" [("value", "Value")],
  ctor "structured-c:expression-call" "Expression" [
    ("function", "ExternalName"), ("arguments", "Expressions")],
  ctor "structured-c:expressions-nil" "Expressions" [],
  ctor "structured-c:expressions-cons" "Expressions" [
    ("expression", "Expression"), ("rest", "Expressions")],
  ctor "structured-c:assign" "Statement" [
    ("variable", "Identifier"), ("expression", "Expression")],
  ctor "structured-c:declare" "Statement" [
    ("variable", "Identifier"), ("type", "CType"),
    ("expression", "Expression")],
  ctor "structured-c:effect" "Statement" [("expression", "Expression")],
  ctor "structured-c:if" "Statement" [
    ("condition", "Expression"), ("thenBranch", "Statements"),
    ("elseBranch", "Statements")],
  ctor "structured-c:while" "Statement" [
    ("condition", "Expression"), ("body", "Statements")],
  ctor "structured-c:switch" "Statement" [
    ("scrutinee", "Expression"), ("cases", "Cases"),
    ("defaultBranch", "Statements")],
  ctor "structured-c:return" "Statement" [("expression", "Expression")],
  ctor "structured-c:statements-nil" "Statements" [],
  ctor "structured-c:statements-cons" "Statements" [
    ("statement", "Statement"), ("rest", "Statements")],
  ctor "structured-c:statements-append" "Statements" [
    ("first", "Statements"), ("second", "Statements")],
  ctor "structured-c:case" "Case" [
    ("value", "Value"), ("body", "Statements")],
  ctor "structured-c:cases-nil" "Cases" [],
  ctor "structured-c:cases-cons" "Cases" [
    ("case", "Case"), ("rest", "Cases")],
  ctor "structured-c:parameter" "Parameter" [
    ("name", "Identifier"), ("type", "CType")],
  ctor "structured-c:parameters-nil" "Parameters" [],
  ctor "structured-c:parameters-cons" "Parameters" [
    ("parameter", "Parameter"), ("rest", "Parameters")],
  ctor "structured-c:function" "Function" [
    ("name", "FunctionName"), ("returnType", "CType"),
    ("parameters", "Parameters"), ("body", "Statements")],
  ctor "structured-c:external-function" "ExternalFunction" [
    ("name", "ExternalName"), ("returnType", "CType"),
    ("parameters", "Parameters")],
  ctor "structured-c:external-functions-nil" "ExternalFunctions" [],
  ctor "structured-c:external-functions-cons" "ExternalFunctions" [
    ("function", "ExternalFunction"), ("rest", "ExternalFunctions")],
  ctor "structured-c:functions-nil" "Functions" [],
  ctor "structured-c:functions-cons" "Functions" [
    ("function", "Function"), ("rest", "Functions")],
  ctor "structured-c:program" "Program" [
    ("externals", "ExternalFunctions"), ("functions", "Functions")],
  ctor "structured-c:evaluation-value" "EvaluationResult" [("value", "Value")],
  ctor "structured-c:evaluation-fault" "EvaluationResult" [("fault", "Fault")],
  ctor "structured-c:fault-language" "Fault" [("message", "String")],
  ctor "structured-c:fault-engine" "Fault" [("message", "String")],
  ctor "structured-c:fault-resource" "Fault" [("message", "String")],
  ctor "structured-c:outcome-return" "Outcome" [("value", "Value")],
  ctor "structured-c:outcome-fallthrough" "Outcome" [],
  ctor "structured-c:outcome-fault" "Outcome" [("fault", "Fault")],
  ctor "structured-c:environment-empty" "Environment" [],
  ctor "structured-c:environment-bind" "Environment" [
    ("variable", "Identifier"), ("value", "Value"), ("rest", "Environment")],
  ctor "structured-c:receipt-ready" "Receipt" [],
  ctor "structured-c:receipt-empty" "Receipt" [],
  ctor "structured-c:receipt-step" "Receipt" [
    ("at", "Value"), ("prior", "Receipt")],
  ctor "structured-c:receipt-external" "Receipt" [
    ("at", "Value"), ("external", "Value"), ("outcome", "Value"),
    ("prior", "Receipt")],
  ctor "structured-c:receipt-finished" "Receipt" [
    ("outcome", "Value"), ("prior", "Receipt")],
  ctor "structured-c:receipt-incomplete" "Receipt" [
    ("prior", "Receipt")],
  ctor "structured-c:run" "Config" [
    ("statements", "Statements"), ("environment", "Environment"),
    ("receipt", "Receipt")] (some .rewrite),
  ctor "structured-c:halted" "Config" [
    ("outcome", "Outcome"), ("environment", "Environment"),
    ("receipt", "Receipt")]
]

/-- The first StructuredC slice.  Its syntax is closed; environment access,
external calls, and case selection remain explicit relational interfaces. -/
def language : LanguageDef := {
  name := "StructuredC"
  types := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Identifier", "FunctionName", "ExternalName", "CType", "Value", "Expression",
    "Expressions", "Statement", "Statements", "Case", "Cases", "Parameter",
    "Parameters", "Function", "Functions", "ExternalFunction",
    "ExternalFunctions", "Program", "Environment", "Receipt", "Fault",
    "EvaluationResult", "Outcome", "Config"]
  terms := terms
  equations := []
  rewrites := transitions
}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ transitions at membership
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 1000000 })
      [LanguageDef.validateRewrite, language, terms, ctor, typed, v, a,
      query, run, halted, nilStatements, consStatement, appendStatements,
      evaluationValue, evaluationFault, commonContext,
      emptyTransition, appendEmptyTransition, appendConsTransition,
      assignValueTransition, assignFaultTransition, effectValueTransition,
      declareValueTransition, declareFaultTransition,
      effectFaultTransition, ifValueTransition, ifFaultTransition,
      whileExpandTransition,
      switchValueTransition, switchFaultTransition, returnValueTransition,
      returnFaultTransition,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain,
      TypeExpr.baseNames]

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide
  exact rewrites_validate

def validated : ValidatedLanguageDef where
  language := language
  valid := language_validate

theorem transition_count : transitions.length = 16 := by decide

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire != "" := by decide +kernel

#print axioms language_validate

end Mettapedia.GSLT.LanguageDef.StructuredC
