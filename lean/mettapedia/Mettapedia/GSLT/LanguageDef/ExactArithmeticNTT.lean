import Mettapedia.GSLT.LanguageDef.ArithmeticExtension
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# Exact-integer arithmetic OSLF and native-type diagnostics

This operational source presentation is distinct from C0.  It exposes the
seven exact-integer operations, value and decline outcomes, and an explicit
typed relation boundary for mathematical arithmetic.  The existing
`ExactInteger.coreSem` remains the mathematical authority for that boundary.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

/-- Canonical free-variable pattern used by the authored arithmetic rules. -/
def v (name : String) : Pattern := .fvar name
/-- Canonical application pattern used by the authored arithmetic rules. -/
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-- One named exact-arithmetic evaluation rule.  Exposing the constructor lets
compiler proofs select and invert the authored source edge without unfolding
the whole executable rule engine. -/
def evaluateRule (operation relation : String) : RewriteRule := {
  name := s!"arith:evaluate:{operation}"
  typeContext := [
    ("first", .base "Integer"), ("second", .base "Integer"),
    ("outcome", .base "Outcome")]
  premises := [
    .relationQuery relation [v "first", v "second", v "outcome"]]
  left := a "arith:eval" [a operation, v "first", v "second"]
  right := a "arith:halted" [v "outcome"]
}

/-- The operational exact-integer source language used by the first
GSLT-to-GSLT compiler theorem. -/
def exactArithmetic : LanguageDef := {
  name := "ExactArithmetic"
  types := [
    { name := "Integer", carrier := .builtinInt },
    "Operation", "Outcome", "Config"]
  terms := [
    ctor "arith:add" "Operation" [],
    ctor "arith:sub" "Operation" [],
    ctor "arith:mul" "Operation" [],
    ctor "arith:tquot" "Operation" [],
    ctor "arith:fquot" "Operation" [],
    ctor "arith:trem" "Operation" [],
    ctor "arith:frem" "Operation" [],
    ctor "arith:outcome-value" "Outcome" [("value", "Integer")],
    ctor "arith:outcome-declined" "Outcome" [],
    ctor "arith:eval" "Config"
      [("operation", "Operation"), ("first", "Integer"),
       ("second", "Integer")] (some .rewrite),
    ctor "arith:halted" "Config" [("outcome", "Outcome")]
  ]
  equations := []
  rewrites := [
    evaluateRule "arith:add" "ExactIntegerAdd",
    evaluateRule "arith:sub" "ExactIntegerSub",
    evaluateRule "arith:mul" "ExactIntegerMul",
    evaluateRule "arith:tquot" "ExactIntegerTQuot",
    evaluateRule "arith:fquot" "ExactIntegerFQuot",
    evaluateRule "arith:trem" "ExactIntegerTRem",
    evaluateRule "arith:frem" "ExactIntegerFRem"]
}

/-- Exact proof-relevant binding fibre for one authored arithmetic evaluation
rule.  The operation constructor is fixed by the rule, while the two operands
remain explicit bindings in source order. -/
theorem match_evaluateRule
    (operation relation : String) (first second : Pattern) :
    matchPatternForRule exactArithmetic (evaluateRule operation relation)
        (a "arith:eval" [a operation, first, second]) =
      [[("first", first), ("second", second)]] := by
  simp [evaluateRule, matchPatternForRule_eq_syntactic, matchPattern,
    matchArgs, mergeBindings, a, v]

/-! ## Mandatory NTT gate -/

theorem exactArithmetic_inventory :
    exactArithmetic.types.length = 4 ∧
    exactArithmetic.terms.length = 11 ∧
    exactArithmetic.rewrites.length = 7 := by
  decide

theorem integer_outcome_crossing :
    ("arith:outcome-value", "Integer", "Outcome") ∈
      unaryCrossings exactArithmetic := by
  decide

theorem outcome_config_crossing :
    ("arith:halted", "Outcome", "Config") ∈
      unaryCrossings exactArithmetic := by
  decide

/-- Operations cannot become outcomes without passing through evaluation. -/
theorem no_operation_outcome_crossing :
    ("arith:invented-operation-outcome", "Operation", "Outcome") ∉
      unaryCrossings exactArithmetic := by
  decide

private def integerZero : Pattern := a "integer:0"
private def integerTwo : Pattern := a "integer:2"
private def integerThree : Pattern := a "integer:3"
private def integerFive : Pattern := a "integer:5"
private def value (integer : Pattern) : Pattern :=
  a "arith:outcome-value" [integer]
private def declined : Pattern := a "arith:outcome-declined"

/-- Finite executable facts used only for positive and negative OSLF
diagnostics.  Universal arithmetic authority remains `coreSem`. -/
def arithmeticDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ExactIntegerAdd" then
      [[integerTwo, integerThree, value integerFive]]
    else if relation == "ExactIntegerTQuot" then
      [[integerThree, integerZero, declined]]
    else
      []

def exactArithmeticOSLF :=
  langOSLFUsing arithmeticDemoRelationEnv exactArithmetic "Config"

theorem exactArithmetic_galois :
    GaloisConnection
      (langDiamondUsing arithmeticDemoRelationEnv exactArithmetic)
      (langBoxUsing arithmeticDemoRelationEnv exactArithmetic) :=
  langGaloisUsing arithmeticDemoRelationEnv exactArithmetic

/-- The positive demo fact agrees with the mathematical exact-integer
semantics. -/
theorem add_demo_coreSem : coreSem .add 2 3 = .val 5 := by
  decide

/-- Zero-divisor decline is a source-language outcome, not a C or GMP fault. -/
theorem tquot_zero_demo_coreSem : coreSem .tquot 3 0 = .declined := by
  simp [coreSem, undefinedAt, CoreOp.isPartial]

theorem add_step_exact :
    rewriteAt (engineBasePremises arithmeticDemoRelationEnv)
        exactArithmetic 1
        (a "arith:eval" [a "arith:add", integerTwo, integerThree]) =
      [a "arith:halted" [value integerFive]] := by
  decide +kernel

theorem tquot_zero_step_exact :
    rewriteAt (engineBasePremises arithmeticDemoRelationEnv)
        exactArithmetic 1
        (a "arith:eval" [a "arith:tquot", integerThree, integerZero]) =
      [a "arith:halted" [declined]] := by
  decide +kernel

/-- An unlicensed arithmetic tuple cannot invent a result. -/
theorem unsupported_add_is_stuck :
    rewriteAt (engineBasePremises arithmeticDemoRelationEnv)
        exactArithmetic 1
        (a "arith:eval" [a "arith:add", integerThree, integerThree]) = [] := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT
