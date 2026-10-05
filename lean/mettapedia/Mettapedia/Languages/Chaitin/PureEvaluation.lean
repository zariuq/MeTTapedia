import Mettapedia.Languages.Chaitin.Evaluator
import Mathlib.Logic.Relation

/-!
# Pure natural semantics for historical Chaitin Lisp

These derivations describe unbounded evaluations that perform no input or
output effects. Function positions are evaluated, bindings are dynamic, and
`eval` starts in the clean environment. Operand lists retain their order.
-/

namespace Mettapedia.Languages.Chaitin.PureEvaluation

open Mettapedia.Computability.StreamingInput

/-- The evaluator's permissive lambda branch, excluding its primitive and
effectful dispatch branches. No well-formed lambda syntax is required. -/
structure LambdaDispatch (function : SExpr) (arguments : List SExpr) : Prop where
  not_readBit : function ≠ .symbol "read-bit"
  not_readExp : function ≠ .symbol "read-exp"
  not_display : function ≠ .symbol "display"
  not_debug : function ≠ .symbol "debug"
  not_eval : function ≠ .symbol "eval"
  not_try : function ≠ .symbol "try"
  no_primitive : purePrimitive function arguments = none

mutual
  /-- Unbounded effect-free evaluation in a dynamic environment. -/
  inductive PureEval : Environment → SExpr → SExpr → Prop where
    | atom (environment expression) (atomic : expression.atom = true) :
        PureEval environment expression (lookup environment expression)
    | quote {environment head operands}
        (function : PureEval environment head (.symbol "'")) :
        PureEval environment (.list (head :: operands)) (operands.headD SExpr.nil)
    | conditional {environment head operands condition value}
        (function : PureEval environment head (.symbol "if"))
        (test : PureEval environment (operands.headD SExpr.nil) condition)
        (branch : PureEval environment
          (if condition.truth then operands.tail.headD SExpr.nil
            else operands.tail.tail.headD SExpr.nil) value) :
        PureEval environment (.list (head :: operands)) value
    | application {environment head operands function values value}
        (functionRun : PureEval environment head function)
        (not_quote : function ≠ .symbol "'")
        (not_if : function ≠ .symbol "if")
        (arguments : PureArguments environment operands values)
        (body : PureApply environment function values value) :
        PureEval environment (.list (head :: operands)) value

  /-- Operands evaluated from left to right without changing the environment. -/
  inductive PureArguments : Environment → List SExpr → List SExpr → Prop where
    | nil (environment) : PureArguments environment [] []
    | cons {environment expression expressions value values}
        (head : PureEval environment expression value)
        (tail : PureArguments environment expressions values) :
        PureArguments environment (expression :: expressions) (value :: values)

  /-- Apply an already evaluated function to its already evaluated operands. -/
  inductive PureApply : Environment → SExpr → List SExpr → SExpr → Prop where
    | primitive {environment function arguments value}
        (returned : purePrimitive function arguments = some value) :
        PureApply environment function arguments value
    | eval {environment arguments value}
        (body : PureEval cleanEnvironment (arguments.headD SExpr.nil) value) :
        PureApply environment (.symbol "eval") arguments value
    | lambda {environment function arguments value}
        (dispatch : LambdaDispatch function arguments)
        (body : PureEval (bind function.cadr (.list arguments) environment)
          function.caddr value) :
        PureApply environment function arguments value
end

/-- A finite sequence of internal evaluator actions, without reads or returns
through the caller's continuation. -/
def InternalSteps : State → State → Prop :=
  Relation.ReflTransGen (fun state next => observe state = .step next)

theorem InternalSteps.single {state next}
    (step : observe state = .step next) : InternalSteps state next :=
  Relation.ReflTransGen.single step

theorem InternalSteps.trans {state middle next}
    (first : InternalSteps state middle) (second : InternalSteps middle next) :
    InternalSteps state next := Relation.ReflTransGen.trans first second

def EvalSound (environment : Environment) (expression value : SExpr) : Prop :=
  ∀ context : State,
    InternalSteps { context with control := .eval expression environment .unlimited }
      { context with control := .returned value }

def ArgumentsSound (environment : Environment) (expressions values : List SExpr) : Prop :=
  ∀ (context : State) (function : SExpr) (reversed : List SExpr),
    InternalSteps (evaluateArguments context function reversed expressions environment .unlimited)
      { context with control := (.apply function (reversed.reverse ++ values)
          environment .unlimited) }

def ApplySound (environment : Environment) (function : SExpr)
    (arguments : List SExpr) (value : SExpr) : Prop :=
  ∀ context : State,
    InternalSteps { context with control := .apply function arguments environment .unlimited }
      { context with control := .returned value }

private theorem atom_sound {environment expression}
    (atomic : expression.atom = true) :
    EvalSound environment expression (lookup environment expression) := by
  intro context
  apply InternalSteps.single
  cases expression with
  | symbol name => rfl
  | number value => rfl
  | list values =>
      cases values with
      | nil => rfl
      | cons first rest => simp [SExpr.atom] at atomic

private theorem quote_sound {environment head operands}
    (function : EvalSound environment head (.symbol "'")) :
    EvalSound environment (.list (head :: operands)) (operands.headD SExpr.nil) := by
  intro context
  exact (InternalSteps.single rfl).trans
    ((function { context with
        frames := .function operands environment .unlimited :: context.frames }).trans
      (InternalSteps.single (by simp [observe])))

private theorem conditional_sound {environment head operands condition value}
    (function : EvalSound environment head (.symbol "if"))
    (test : EvalSound environment (operands.headD SExpr.nil) condition)
    (branch : EvalSound environment
      (if condition.truth then operands.tail.headD SExpr.nil
        else operands.tail.tail.headD SExpr.nil) value) :
    EvalSound environment (.list (head :: operands)) value := by
  intro context
  exact (InternalSteps.single rfl).trans
    ((function { context with
        frames := .function operands environment .unlimited :: context.frames }).trans
      ((InternalSteps.single (by simp [observe])).trans
        ((test { context with frames := (Frame.conditional (operands.tail.headD SExpr.nil)
              (operands.tail.tail.headD SExpr.nil) environment .unlimited :: context.frames) }).trans
          ((InternalSteps.single rfl).trans (branch context)))))

private theorem evaluateArguments_control (context : State) (control : Control)
    (function : SExpr) (reversed remaining : List SExpr) (environment : Environment) :
    evaluateArguments { context with control := control } function reversed remaining
        environment .unlimited =
      evaluateArguments context function reversed remaining environment .unlimited := by
  cases remaining <;> rfl

private theorem application_sound {environment head operands function values value}
    (functionRun : EvalSound environment head function)
    (not_quote : function ≠ .symbol "'")
    (not_if : function ≠ .symbol "if")
    (arguments : ArgumentsSound environment operands values)
    (body : ApplySound environment function values value) :
    EvalSound environment (.list (head :: operands)) value := by
  intro context
  exact (InternalSteps.single rfl).trans
    ((functionRun { context with
        frames := .function operands environment .unlimited :: context.frames }).trans
      ((InternalSteps.single (by simp [observe, not_quote, not_if, evaluateArguments_control])).trans
        ((arguments context function []).trans (body context))))

private theorem nil_sound (environment : Environment) :
    ArgumentsSound environment [] [] := by
  intro context function reversed
  simp only [evaluateArguments, List.append_nil]
  exact .refl

private theorem cons_sound {environment expression expressions value values}
    (head : EvalSound environment expression value)
    (tail : ArgumentsSound environment expressions values) :
    ArgumentsSound environment (expression :: expressions) (value :: values) := by
  intro context function reversed
  simpa only [evaluateArguments, List.reverse_cons, List.append_assoc, List.singleton_append] using
    (head { context with frames := (Frame.argument function reversed expressions
        environment .unlimited :: context.frames) }).trans
      ((InternalSteps.single rfl).trans (tail context function (value :: reversed)))

private theorem primitive_sound {environment function arguments value}
    (returned : purePrimitive function arguments = some value) :
    ApplySound environment function arguments value := by
  intro context
  apply InternalSteps.single
  cases function with
  | number number => simp [purePrimitive] at returned
  | list values => simp [purePrimitive] at returned
  | symbol name =>
      by_cases readBit : name = "read-bit"
      · subst name; simp [purePrimitive] at returned
      by_cases readExp : name = "read-exp"
      · subst name; simp [purePrimitive] at returned
      by_cases display : name = "display"
      · subst name; simp [purePrimitive] at returned
      by_cases debug : name = "debug"
      · subst name; simp [purePrimitive] at returned
      simp [observe, readBit, readExp, display, debug, returned]

private theorem eval_sound {environment arguments value}
    (body : EvalSound cleanEnvironment (arguments.headD SExpr.nil) value) :
    ApplySound environment (.symbol "eval") arguments value := by
  intro context
  exact (InternalSteps.single (by simp [observe, purePrimitive, Depth.decrease])).trans (body context)

private theorem lambda_sound {environment function arguments value}
    (dispatch : LambdaDispatch function arguments)
    (body : EvalSound (bind function.cadr (.list arguments) environment)
      function.caddr value) :
    ApplySound environment function arguments value := by
  intro context
  apply InternalSteps.trans (InternalSteps.single ?_) (body context)
  rcases dispatch with ⟨readBit, readExp, display, debug, notEval, notTry, primitive⟩
  cases function with
  | number number => simp [observe, primitive, Depth.decrease]
  | list values => simp [observe, primitive, Depth.decrease]
  | symbol name =>
      simp [observe, notEval, notTry, primitive, Depth.decrease]

theorem PureEval.steps {environment expression value}
    (derivation : PureEval environment expression value) :
    EvalSound environment expression value := by
  induction derivation using PureEval.rec
      (motive_2 := fun environment expressions values _ =>
        ArgumentsSound environment expressions values)
      (motive_3 := fun environment function arguments value _ =>
        ApplySound environment function arguments value) with
  | atom environment expression atomic => exact atom_sound atomic
  | quote function ih => exact quote_sound ih
  | conditional function test branch ihFunction ihTest ihBranch =>
      exact conditional_sound ihFunction ihTest ihBranch
  | application functionRun notQuote notIf arguments body ihFunction ihArguments ihBody =>
      exact application_sound ihFunction notQuote notIf ihArguments ihBody
  | nil environment => exact nil_sound environment
  | cons head tail ihHead ihTail => exact cons_sound ihHead ihTail
  | primitive returned => exact primitive_sound returned
  | eval body ih => exact eval_sound ih
  | lambda dispatch body ih => exact lambda_sound dispatch ih

/-- Applying a pure function is sound in any caller continuation. -/
theorem PureApply.steps {environment function arguments value}
    (derivation : PureApply environment function arguments value) :
    ApplySound environment function arguments value := by
  induction derivation using PureApply.rec
      (motive_1 := fun environment expression value _ =>
        EvalSound environment expression value)
      (motive_2 := fun environment expressions values _ =>
        ArgumentsSound environment expressions values) with
  | atom environment expression atomic => exact atom_sound atomic
  | quote function ih => exact quote_sound ih
  | conditional function test branch ihFunction ihTest ihBranch =>
      exact conditional_sound ihFunction ihTest ihBranch
  | application functionRun notQuote notIf arguments body ihFunction ihArguments ihBody =>
      exact application_sound ihFunction notQuote notIf ihArguments ihBody
  | nil environment => exact nil_sound environment
  | cons head tail ihHead ihTail => exact cons_sound ihHead ihTail
  | primitive returned => exact primitive_sound returned
  | eval body ih => exact eval_sound ih
  | lambda dispatch body ih => exact lambda_sound dispatch ih

end Mettapedia.Languages.Chaitin.PureEvaluation
