import Mettapedia.Languages.Chaitin.GSLT.Configurations
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Authored rewrite rules for the historical Lisp evaluator's pure core

The thirteen schemas expose expression dispatch, function evaluation,
quotation, conditional choice, argument sequencing, application and dynamic
binding. The explicit premise boundary supplies only data operations. It
never receives a continuation, evaluates a guest expression, or interprets a
Turing table. Recursion proceeds through ordinary authored evaluator steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def dataBindings (operation : String) (inputs : List Pattern) : Option Bindings :=
  match operation, inputs with
  | "atomLookup", [expression, environment] => do
      let value ← decode expression
      let bindings ← decodeEnvironment environment
      if value.atom then pure [("a", encode (lookup bindings value))] else none
  | "quotation", [function, operands] => do
      let value ← decode function
      let expressions ← decodeValues operands
      if value = .symbol "'" then pure [("a", encode (expressions.headD SExpr.nil))] else none
  | "conditionalOperands", [function, operands] => do
      let value ← decode function
      let expressions ← decodeValues operands
      if value = .symbol "if" then pure [
        ("a", encode (expressions.headD SExpr.nil)),
        ("b", encode (expressions.tail.headD SExpr.nil)),
        ("c", encode (expressions.tail.tail.headD SExpr.nil))] else none
  | "ordinary", [function] => do
      let value ← decode function
      if value ≠ .symbol "'" ∧ value ≠ .symbol "if" then pure [] else none
  | "truthy", [expression] => do
      let value ← decode expression
      if value.truth then pure [] else none
  | "falsey", [expression] => do
      let value ← decode expression
      if value.truth then none else pure []
  | "reverseCons", [expression, reversed] => do
      let value ← decode expression
      let values ← decodeValues reversed
      pure [("a", encodeValues (value :: values).reverse)]
  | "primitive", [function, arguments] => do
      let value ← decode function
      let values ← decodeValues arguments
      let result ← purePrimitive value values
      pure [("a", encode result)]
  | "cleanEval", [function, arguments] => do
      let value ← decode function
      let values ← decodeValues arguments
      if value = .symbol "eval" then pure [("a", encode (values.headD SExpr.nil)),
        ("b", encodeEnvironment cleanEnvironment)] else none
  | "lambdaBody", [function, arguments, environment] => do
      let value ← decode function
      let values ← decodeValues arguments
      let bindings ← decodeEnvironment environment
      if value ≠ .symbol "read-bit" ∧ value ≠ .symbol "read-exp" ∧
          value ≠ .symbol "display" ∧ value ≠ .symbol "debug" ∧
          value ≠ .symbol "eval" ∧ value ≠ .symbol "try" ∧
          purePrimitive value values = none then
        pure [("a", encode value.caddr),
          ("b", encodeEnvironment (bind value.cadr (.list values) bindings))]
      else none
  | _, _ => none

def inputCount : String → Nat
  | "atomLookup" | "quotation" | "conditionalOperands" | "reverseCons" |
    "primitive" | "cleanEval" => 2
  | "ordinary" | "truthy" | "falsey" => 1
  | "lambdaBody" => 3
  | _ => 0

def outputNames : String → List String
  | "atomLookup" | "quotation" | "reverseCons" | "primitive" => ["a"]
  | "conditionalOperands" => ["a", "b", "c"]
  | "lambdaBody" | "cleanEval" => ["a", "b"]
  | _ => []

/-- An explicit, total data-premise realization. Output names `a`, `b`, and
`c` are reserved by the authored schemas; all their inputs are already bound.
Unknown operations and malformed encoded inputs produce no premise evidence. -/
def dataPremises : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery operation arguments =>
      if arguments.drop (inputCount operation) = (outputNames operation).map Pattern.fvar then
        match dataBindings operation ((arguments.take (inputCount operation)).map (applyBindings bindings)) with
        | none => []
        | some outputs => [outputs ++ bindings]
      else []
  | _ => []

def metavariable (name : String) : Pattern := .fvar name
def node (name : String) (arguments : List Pattern) : Pattern := .apply name arguments
def nilData : Pattern := node "Nil" []

def ruleContext : List (String × TypeExpr) :=
  [("x", .base "Data"), ("y", .base "Data"), ("z", .base "Data"),
    ("e", .base "Data"), ("k", .base "Continuation"),
    ("a", .base "Data"), ("b", .base "Data"), ("c", .base "Data")]

def schema (name : String) (left right : Pattern) (premises : List Premise := []) : RewriteRule :=
  { name, typeContext := ruleContext, premises, left, right }

def query (operation : String) (inputs : List String) : List Premise :=
  [.relationQuery operation ((inputs ++ outputNames operation).map metavariable)]

def atomRule : RewriteRule := schema "atom"
  (node "Eval" [metavariable "x", metavariable "y", metavariable "k"])
  (node "Returned" [metavariable "a", metavariable "k"]) (query "atomLookup" ["x", "y"])

def callRule : RewriteRule := schema "call"
  (node "Eval" [node "List" [node "Cons" [metavariable "x", metavariable "z"]],
    metavariable "y", metavariable "k"])
  (node "Eval" [metavariable "x", metavariable "y", node "Function" [metavariable "z", metavariable "y", metavariable "k"]])

def quoteRule : RewriteRule := schema "quote"
  (node "Returned" [metavariable "x", node "Function" [metavariable "y", metavariable "z", metavariable "k"]])
  (node "Returned" [metavariable "a", metavariable "k"]) (query "quotation" ["x", "y"])

def conditionalRule : RewriteRule := schema "conditional"
  (node "Returned" [metavariable "x", node "Function" [metavariable "y", metavariable "z", metavariable "k"]])
  (node "Eval" [metavariable "a", metavariable "z",
    node "Conditional" [metavariable "b", metavariable "c", metavariable "z", metavariable "k"]])
  (query "conditionalOperands" ["x", "y"])

def functionNilRule : RewriteRule := schema "function-nil"
  (node "Returned" [metavariable "x", node "Function" [nilData, metavariable "y", metavariable "k"]])
  (node "Apply" [metavariable "x", nilData, metavariable "y", metavariable "k"]) (query "ordinary" ["x"])

def functionConsRule : RewriteRule := schema "function-cons"
  (node "Returned" [metavariable "x", node "Function" [node "Cons" [metavariable "y", metavariable "z"],
    metavariable "e", metavariable "k"]])
  (node "Eval" [metavariable "y", metavariable "e",
    node "Argument" [metavariable "x", nilData, metavariable "z", metavariable "e", metavariable "k"]])
  (query "ordinary" ["x"])

def positiveRule : RewriteRule := schema "positive"
  (node "Returned" [metavariable "x", node "Conditional" [metavariable "y", metavariable "z", metavariable "e", metavariable "k"]])
  (node "Eval" [metavariable "y", metavariable "e", metavariable "k"]) (query "truthy" ["x"])

def negativeRule : RewriteRule := schema "negative"
  (node "Returned" [metavariable "x", node "Conditional" [metavariable "y", metavariable "z", metavariable "e", metavariable "k"]])
  (node "Eval" [metavariable "z", metavariable "e", metavariable "k"]) (query "falsey" ["x"])

def argumentNilRule : RewriteRule := schema "argument-nil"
  (node "Returned" [metavariable "x", node "Argument" [metavariable "y", metavariable "z", nilData,
    metavariable "e", metavariable "k"]])
  (node "Apply" [metavariable "y", metavariable "a", metavariable "e", metavariable "k"])
  (query "reverseCons" ["x", "z"])

def argumentConsRule : RewriteRule := schema "argument-cons"
  (node "Returned" [metavariable "x", node "Argument" [metavariable "y", metavariable "z",
    node "Cons" [metavariable "a", metavariable "b"], metavariable "e", metavariable "k"]])
  (node "Eval" [metavariable "a", metavariable "e", node "Argument" [metavariable "y",
    node "Cons" [metavariable "x", metavariable "z"], metavariable "b", metavariable "e", metavariable "k"]])

def primitiveRule : RewriteRule := schema "primitive"
  (node "Apply" [metavariable "x", metavariable "y", metavariable "z", metavariable "k"])
  (node "Returned" [metavariable "a", metavariable "k"]) (query "primitive" ["x", "y"])

def evalRule : RewriteRule := schema "clean-eval"
  (node "Apply" [metavariable "x", metavariable "y", metavariable "z", metavariable "k"])
  (node "Eval" [metavariable "a", metavariable "b", metavariable "k"])
  (query "cleanEval" ["x", "y"])

def lambdaRule : RewriteRule := schema "lambda"
  (node "Apply" [metavariable "x", metavariable "y", metavariable "z", metavariable "k"])
  (node "Eval" [metavariable "a", metavariable "b", metavariable "k"]) (query "lambdaBody" ["x", "y", "z"])

def grammar (label category : String) (parameters : List (String × String)) : GrammarRule :=
  { label, category,
    params := parameters.map fun (name, sort) => .simple name (.base sort),
    syntaxPattern := parameters.map fun (name, _) => .nonTerminal name }

def language : LanguageDef :=
  { name := "ChaitinPureEvaluator"
    types := ["Data", "Continuation", "Configuration"]
    terms := [
      grammar "Zero" "Data" [], grammar "One" "Data" [],
      grammar "Bit0" "Data" [("digit", "Data")],
      grammar "Bit1" "Data" [("digit", "Data")],
      grammar "Positive" "Data" [("digits", "Data")],
      grammar "Nil" "Data" [], grammar "Cons" "Data" [("head", "Data"), ("tail", "Data")],
      grammar "Word" "Data" [("characters", "Data")],
      grammar "Number" "Data" [("value", "Data")],
      grammar "List" "Data" [("values", "Data")],
      grammar "Binding" "Data" [("name", "Data"), ("value", "Data")],
      grammar "Done" "Continuation" [],
      grammar "Function" "Continuation" [("operands", "Data"), ("environment", "Data"), ("rest", "Continuation")],
      grammar "Conditional" "Continuation" [("yes", "Data"), ("no", "Data"), ("environment", "Data"), ("rest", "Continuation")],
      grammar "Argument" "Continuation" [("function", "Data"), ("reversed", "Data"), ("remaining", "Data"),
        ("environment", "Data"), ("rest", "Continuation")],
      grammar "Eval" "Configuration" [("expression", "Data"), ("environment", "Data"), ("continuation", "Continuation")],
      grammar "Apply" "Configuration" [("function", "Data"), ("arguments", "Data"),
        ("environment", "Data"), ("continuation", "Continuation")],
      grammar "Returned" "Configuration" [("value", "Data"), ("continuation", "Continuation")]]
    equations := []
    rewrites := [atomRule, callRule, quoteRule, conditionalRule, functionNilRule,
      functionConsRule, positiveRule, negativeRule, argumentNilRule, argumentConsRule,
      primitiveRule, evalRule, lambdaRule] }

theorem equationFree : language.isEquationFree = true := by decide

local macro "validate_core_rule" : tactic =>
  `(tactic| simp [LanguageDef.validateRewrite, LanguageDef.typeNames, TypeDecl.plain,
      atomRule, callRule, quoteRule, conditionalRule, functionNilRule, functionConsRule,
      positiveRule, negativeRule, argumentNilRule, argumentConsRule, primitiveRule, evalRule, lambdaRule,
      schema, node, metavariable, nilData, query, outputNames, ruleContext, language, grammar,
      LanguageDef.validatePatternConstructors,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premiseStepTypeExprs,
      LanguageDef.premisePatterns, LanguageDef.premiseLocallyScoped,
      LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams]
    <;> (repeat' apply And.intro)
    <;> apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    <;> decide)

theorem atomRule_validates : LanguageDef.validateRewrite language atomRule = [] := by
  validate_core_rule

theorem callRule_validates : LanguageDef.validateRewrite language callRule = [] := by
  validate_core_rule

theorem quoteRule_validates : LanguageDef.validateRewrite language quoteRule = [] := by
  validate_core_rule

theorem conditionalRule_validates : LanguageDef.validateRewrite language conditionalRule = [] := by
  validate_core_rule

theorem functionNilRule_validates : LanguageDef.validateRewrite language functionNilRule = [] := by
  validate_core_rule

theorem functionConsRule_validates : LanguageDef.validateRewrite language functionConsRule = [] := by
  validate_core_rule

theorem positiveRule_validates : LanguageDef.validateRewrite language positiveRule = [] := by
  validate_core_rule

theorem negativeRule_validates : LanguageDef.validateRewrite language negativeRule = [] := by
  validate_core_rule

theorem argumentNilRule_validates : LanguageDef.validateRewrite language argumentNilRule = [] := by
  validate_core_rule

theorem argumentConsRule_validates : LanguageDef.validateRewrite language argumentConsRule = [] := by
  validate_core_rule

theorem primitiveRule_validates : LanguageDef.validateRewrite language primitiveRule = [] := by
  validate_core_rule

theorem evalRule_validates : LanguageDef.validateRewrite language evalRule = [] := by
  validate_core_rule

theorem lambdaRule_validates : LanguageDef.validateRewrite language lambdaRule = [] := by
  validate_core_rule

theorem language_validates : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rule member
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact atomRule_validates
    · exact callRule_validates
    · exact quoteRule_validates
    · exact conditionalRule_validates
    · exact functionNilRule_validates
    · exact functionConsRule_validates
    · exact positiveRule_validates
    · exact negativeRule_validates
    · exact argumentNilRule_validates
    · exact argumentConsRule_validates
    · exact primitiveRule_validates
    · exact evalRule_validates
    · exact lambdaRule_validates

def theory : Mettapedia.GSLT.GSLT := gsltModuloEquations dataPremises language

theorem theory_equiv_iff_eq (source target : Pattern) :
    theory.Equiv source target ↔ source = target :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators equationFree source target

theorem theory_step_iff (source target : Pattern) :
    theory.Step source target ↔ Step dataPremises language source target :=
  stepModuloEquations_iff_step_of_no_generators equationFree source target

end Mettapedia.Languages.Chaitin.GSLT
