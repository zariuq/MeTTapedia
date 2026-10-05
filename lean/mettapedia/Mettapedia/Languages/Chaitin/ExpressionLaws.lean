import Mettapedia.Languages.Chaitin.Expressions
import Mettapedia.Languages.Chaitin.EvaluationLaws

/-!
# Derivation rules for historical expression constructors

Each rule combines semantic derivations of its operands. Primitive names
remain subject to dynamic lookup, and conditionals evaluate only the selected
branch.
-/

namespace Mettapedia.Languages.Chaitin.PureEvaluation

open Expressions

theorem eval_word {environment : Environment} {name : String} {value : SExpr}
    (found : lookup environment (.symbol name) = value) :
    PureEval environment (.symbol name) value := by
  simpa only [found] using PureEval.atom environment (.symbol name) rfl

theorem eval_primitive_call {environment : Environment} {name : String}
    {expressions values : List SExpr} {value : SExpr}
    (unshadowed : lookup environment (.symbol name) = .symbol name)
    (notQuote : name ≠ "'") (notIf : name ≠ "if")
    (arguments : PureArguments environment expressions values)
    (returned : purePrimitive (.symbol name) values = some value) :
    PureEval environment (call name expressions) value := by
  exact PureEval.application (eval_word unshadowed)
    (fun same => notQuote (SExpr.symbol.inj same))
    (fun same => notIf (SExpr.symbol.inj same))
    arguments (PureApply.primitive returned)

theorem eval_car {environment : Environment} {expression value : SExpr}
    (unshadowed : lookup environment (.symbol "car") = .symbol "car")
    (argument : PureEval environment expression value) :
    PureEval environment (call "car" [expression]) value.car := by
  exact eval_primitive_call unshadowed (by decide) (by decide)
    (.cons argument (.nil environment)) rfl

theorem eval_cdr {environment : Environment} {expression value : SExpr}
    (unshadowed : lookup environment (.symbol "cdr") = .symbol "cdr")
    (argument : PureEval environment expression value) :
    PureEval environment (call "cdr" [expression]) value.cdr := by
  exact eval_primitive_call unshadowed (by decide) (by decide)
    (.cons argument (.nil environment)) rfl

theorem eval_cons {environment : Environment} {head tail first rest : SExpr}
    (unshadowed : lookup environment (.symbol "cons") = .symbol "cons")
    (headRun : PureEval environment head first)
    (tailRun : PureEval environment tail rest) :
    PureEval environment (consExpr head tail) (SExpr.cons first rest) := by
  exact eval_primitive_call unshadowed (by decide) (by decide)
    (.cons headRun (.cons tailRun (.nil environment))) rfl

theorem eval_equal {environment : Environment} {left right first second : SExpr}
    (unshadowed : lookup environment (.symbol "=") = .symbol "=")
    (leftRun : PureEval environment left first)
    (rightRun : PureEval environment right second) :
    PureEval environment (equalExpr left right)
      (SExpr.boolean (decide (first = second))) := by
  exact eval_primitive_call unshadowed (by decide) (by decide)
    (.cons leftRun (.cons rightRun (.nil environment))) rfl

theorem eval_if {environment : Environment} {condition yes no test value : SExpr}
    (unshadowed : lookup environment (.symbol "if") = .symbol "if")
    (conditionRun : PureEval environment condition test)
    (branchRun : PureEval environment (if test.truth then yes else no) value) :
    PureEval environment (ifExpr condition yes no) value := by
  exact PureEval.conditional (eval_word unshadowed) conditionRun branchRun

theorem eval_letValue {environment : Environment} {name : String}
    {expression body argument value : SExpr}
    (unshadowed : lookup environment (.symbol "'") = .symbol "'")
    (argumentRun : PureEval environment expression argument)
    (bodyRun : PureEval (bind (.list [.symbol name]) (.list [argument]) environment)
      body value) :
    PureEval environment (letValue name expression body) value := by
  exact PureEval.application (eval_quote unshadowed (lambda [name] body))
    (by intro same; cases same) (by intro same; cases same)
    (.cons argumentRun (.nil environment)) (PureEvaluation.apply_lambda _ _ _ bodyRun)

theorem eval_listExpr {environment : Environment}
    (consUnshadowed : lookup environment (.symbol "cons") = .symbol "cons")
    (nilValue : lookup environment (.symbol "nil") = SExpr.nil)
    {expressions values : List SExpr}
    (arguments : PureArguments environment expressions values) :
    PureEval environment (listExpr expressions) (.list values) := by
  induction expressions generalizing values with
  | nil =>
      cases arguments
      exact eval_word nilValue
  | cons expression expressions recurse =>
      cases arguments with
      | cons head tail => exact eval_cons consUnshadowed head (recurse tail)

theorem eval_field {environment : Environment}
    (carUnshadowed : lookup environment (.symbol "car") = .symbol "car")
    (cdrUnshadowed : lookup environment (.symbol "cdr") = .symbol "cdr")
    (index : Nat) {expression value : SExpr}
    (argumentRun : PureEval environment expression value) :
    PureEval environment (fieldExpr index expression) (SExpr.field index value) := by
  induction index generalizing expression value with
  | zero => exact eval_car carUnshadowed argumentRun
  | succ index recurse => exact recurse (eval_cdr cdrUnshadowed argumentRun)

theorem eval_if_equal_branches {environment : Environment}
    {left right first second yes no yesValue noValue : SExpr}
    (conditional : lookup environment (.symbol "if") = .symbol "if")
    (equal : lookup environment (.symbol "=") = .symbol "=")
    (leftRun : PureEval environment left first)
    (rightRun : PureEval environment right second)
    (yesRun : PureEval environment yes yesValue)
    (noRun : PureEval environment no noValue) :
    PureEval environment (ifExpr (equalExpr left right) yes no)
      (if first = second then yesValue else noValue) := by
  apply eval_if conditional (eval_equal equal leftRun rightRun)
  by_cases same : first = second
  · simpa [SExpr.truth_boolean, same] using yesRun
  · simpa [SExpr.truth_boolean, same] using noRun

/-- The unused branch may request input; a pure conditional still preserves
that input when its selected branch is pure. -/
theorem unused_read_is_not_executed (input : List Bool) :
    Evaluates (ifExpr (.number 1) (.number 7) (call "read-bit" [])) input
      ⟨.success (.number 7), [], []⟩ input := by
  have derivation := eval_if (environment := cleanEnvironment) (no := call "read-bit" [])
    (by decide) (eval_number cleanEnvironment 1) (eval_number cleanEnvironment 7)
  exact derivation.evaluates input

/-- Dynamic rebinding of the quote word changes its behavior. -/
theorem quote_name_can_be_rebound :
    PureEval [(.symbol "'", .symbol "car"),
      (.symbol "payload", .list [.number 7, .number 8])]
      (quote (.symbol "payload")) (.number 7) := by
  exact PureEval.application (function := .symbol "car")
    (values := [.list [.number 7, .number 8]]) (eval_word (by decide))
    (by decide) (by decide)
    (.cons (eval_word (by decide)) (.nil _)) (.primitive rfl)

/-- A function's free word is resolved in its caller's dynamic environment. -/
theorem lambda_free_word (environment : Environment) (name : String) :
    PureApply environment (lambda [] (.symbol name)) []
      (lookup environment (.symbol name)) :=
  apply_lambda _ _ _ (eval_symbol environment name)

end Mettapedia.Languages.Chaitin.PureEvaluation
