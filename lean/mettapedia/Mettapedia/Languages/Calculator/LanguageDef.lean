import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# A calculator as a language definition

Closed arithmetic expressions over unary numerals, with addition and
multiplication.  The laws of arithmetic are authored as equations: an
expression and its value are the same thing written two ways, and the
language has no rewrite at all.  It is a theory of terms and equations in
which nothing meets anything.

The same four laws read as directed rules give a different presentation,
`calculatorRewriting`, in which evaluation is reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Calculator

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- Numerals, sums and products. -/
def terms : List GrammarRule := [
    { label := "Zero", category := "Num", params := [], syntaxPattern := [] },
    { label := "Succ", category := "Num",
      params := [.simple "n" (.base "Num")],
      syntaxPattern := [.nonTerminal "n"] },
    { label := "Add", category := "Num",
      params := [.simple "m" (.base "Num"), .simple "n" (.base "Num")],
      syntaxPattern := [.nonTerminal "m", .nonTerminal "n"] },
    { label := "Mul", category := "Num",
      params := [.simple "m" (.base "Num"), .simple "n" (.base "Num")],
      syntaxPattern := [.nonTerminal "m", .nonTerminal "n"] }
  ]

/-- `0 + n = n`. -/
def addZero : Equation where
  name := "AddZero"
  typeContext := [("n", .base "Num")]
  premises := []
  left := .apply "Add" [.apply "Zero" [], .fvar "n"]
  right := .fvar "n"

/-- `S m + n = S (m + n)`. -/
def addSucc : Equation where
  name := "AddSucc"
  typeContext := [("m", .base "Num"), ("n", .base "Num")]
  premises := []
  left := .apply "Add" [.apply "Succ" [.fvar "m"], .fvar "n"]
  right := .apply "Succ" [.apply "Add" [.fvar "m", .fvar "n"]]

/-- `0 · n = 0`. -/
def mulZero : Equation where
  name := "MulZero"
  typeContext := [("n", .base "Num")]
  premises := []
  left := .apply "Mul" [.apply "Zero" [], .fvar "n"]
  right := .apply "Zero" []

/-- `S m · n = n + m · n`. -/
def mulSucc : Equation where
  name := "MulSucc"
  typeContext := [("m", .base "Num"), ("n", .base "Num")]
  premises := []
  left := .apply "Mul" [.apply "Succ" [.fvar "m"], .fvar "n"]
  right := .apply "Add" [.fvar "n", .apply "Mul" [.fvar "m", .fvar "n"]]

/-- The laws of arithmetic. -/
def laws : List Equation := [addZero, addSucc, mulZero, mulSucc]

/-- The calculator: arithmetic as an equational theory, with no rewrite. -/
def calculator : LanguageDef :=
  { name := "Calculator"
    types := ["Num"]
    terms := terms
    equations := laws
    rewrites := [] }

/-- One law read from left to right as a rule. -/
def directed (equation : Equation) : RewriteRule where
  name := equation.name
  typeContext := equation.typeContext
  premises := equation.premises
  left := equation.left
  right := equation.right

/-- The same signature with the laws read as directed rules. -/
def calculatorRewriting : LanguageDef :=
  { name := "CalculatorRewriting"
    types := ["Num"]
    terms := terms
    equations := []
    rewrites := laws.map directed }

/-! ## Validation -/

/-- The constructors with their arities. -/
def signatureReferences : List (String × Nat) :=
  [("Zero", 0), ("Succ", 1), ("Add", 2), ("Mul", 2)]

theorem signatureReferences_declared :
    ∀ reference ∈ signatureReferences,
      LanguageDef.referenceDeclared terms reference = true := by
  decide

/-- Each law validates as an equation. -/
theorem laws_validate :
    ∀ equation ∈ laws, LanguageDef.validateEquation calculator equation = [] := by
  intro equation membership
  simp only [laws, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | (intro context
         simp [addZero, addSucc, mulZero, mulSucc, calculator, terms,
           LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
           Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
           LanguageDef.patternBinderNames])

/-- The calculator passes the declaration gate. -/
theorem calculator_validate_eq_nil : calculator.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · exact laws_validate
  · intro rewrite membership
    cases membership

/-- Each law validates as a directed rule. -/
theorem directedLaws_validate :
    ∀ rewrite ∈ laws.map directed,
      LanguageDef.validateRewrite calculatorRewriting rewrite = [] := by
  intro rewrite membership
  simp only [laws, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    at membership
  rcases membership with rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | (intro context
         simp [directed, addZero, addSucc, mulZero, mulSucc, calculatorRewriting, terms,
           LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
           Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
           LanguageDef.patternBinderNames])

/-- The rewriting calculator passes the declaration gate. -/
theorem calculatorRewriting_validate_eq_nil : calculatorRewriting.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · exact directedLaws_validate

/-! ## What the two presentations do -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The numeral of a natural number. -/
def numeral (value : Nat) : Pattern := Pattern.unary "Zero" "Succ" value

/-- `1 + 1`. -/
def onePlusOne : Pattern := .apply "Add" [numeral 1, numeral 1]

/-- `S (0 + 1)`: the first law applied once. -/
def onePlusOneUnfolded : Pattern :=
  .apply "Succ" [.apply "Add" [numeral 0, numeral 1]]

/-- The equational calculator never takes a step: it has no rule to fire. -/
theorem calculator_no_step (source target : Pattern) :
    ¬ Step base calculator source target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  cases membership

/-- Its laws are nevertheless real: `1 + 1` and `S (0 + 1)` are equal by an
instance of the successor law. -/
theorem onePlusOne_equation :
    EquationEquiv base calculator onePlusOne onePlusOneUnfolded := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern addSucc.left onePlusOne,
        applyBindings bindings addSucc.right = onePlusOneUnfolded := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.forward (equation := addSucc)
    (List.Mem.tail _ (List.Mem.head _)) matched (PremisesAt.nil bindings) applied⟩

/-- In the rewriting presentation the same law is a step. -/
theorem onePlusOne_rewrites :
    Step base calculatorRewriting onePlusOne onePlusOneUnfolded :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

end Mettapedia.Languages.Calculator
