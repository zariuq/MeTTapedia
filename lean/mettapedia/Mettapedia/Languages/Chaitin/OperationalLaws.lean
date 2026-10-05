import Mettapedia.Languages.Chaitin.ExpressionLaws

/-!
# Compositional prefixes of historical Lisp execution

These laws stop at a call or a selected body, before its result is known.
They retain the caller's continuation and all streaming observations. A
positive internal prefix strictly decreases any successful execution budget;
this supplies the well-founded measure for backward interpreter proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.PureEvaluation

open Mettapedia.Computability.StreamingInput Expressions

theorem PureArguments.steps {environment expressions values}
    (arguments : PureArguments environment expressions values) :
    ArgumentsSound environment expressions values := by
  induction expressions generalizing values with
  | nil =>
      cases arguments
      intro context function reversed
      simp only [evaluateArguments, List.append_nil]
      exact .refl
  | cons expression expressions recurse =>
      cases arguments with
      | cons head tail =>
        have ih := recurse tail
        intro context function reversed
        simpa only [evaluateArguments, List.reverse_cons, List.append_assoc,
          List.singleton_append] using
          (head.steps { context with frames := (
            Frame.argument function reversed expressions environment .unlimited :: context.frames) }).trans
            ((InternalSteps.single rfl).trans (ih context function (_ :: reversed)))

theorem application_prefix {environment : Environment} {head function : SExpr}
    {operands values : List SExpr}
    (functionRun : PureEval environment head function)
    (notQuote : function ≠ .symbol "'") (notIf : function ≠ .symbol "if")
    (arguments : PureArguments environment operands values) (context : State) :
    InternalSteps
      { context with control := .eval (.list (head :: operands)) environment .unlimited }
      { context with control := .apply function values environment .unlimited } := by
  have resume : observe
      { context with
        control := .returned function
        frames := .function operands environment .unlimited :: context.frames } =
      .step (evaluateArguments context function [] operands environment .unlimited) := by
    cases operands <;> simp [observe, notQuote, notIf, evaluateArguments]
  exact (InternalSteps.single rfl).trans
    ((functionRun.steps { context with frames := (
      Frame.function operands environment .unlimited :: context.frames) }).trans
      ((InternalSteps.single resume).trans (arguments.steps context function [])))

theorem lambda_prefix (parameters body : SExpr) (arguments : List SExpr)
    (environment : Environment) (context : State) :
    InternalSteps
      { context with control := (
        Control.apply (.list [.symbol "lambda", parameters, body]) arguments environment .unlimited) }
      { context with control := (
        Control.eval body (bind parameters (.list arguments) environment) .unlimited) } :=
  InternalSteps.single rfl

theorem let_prefix {environment : Environment} {name : String}
    {expression body argument : SExpr}
    (quoteName : lookup environment (.symbol "'") = .symbol "'")
    (computed : PureEval environment expression argument) (context : State) :
    InternalSteps
      { context with control := .eval (letValue name expression body) environment .unlimited }
      { context with control := (.eval body
        (bind (.list [.symbol name]) (.list [argument]) environment) .unlimited) } :=
  (application_prefix (eval_quote quoteName (lambda [name] body))
    (by intro same; cases same) (by intro same; cases same)
    (.cons computed (.nil environment)) context).trans
    (lambda_prefix _ _ _ _ context)

theorem conditional_prefix {environment : Environment}
    {condition yes no test : SExpr}
    (ifName : lookup environment (.symbol "if") = .symbol "if")
    (computed : PureEval environment condition test) (context : State) :
    InternalSteps
      { context with control := .eval (ifExpr condition yes no) environment .unlimited }
      { context with control := (.eval (if test.truth then yes else no)
        environment .unlimited) } := by
  exact (InternalSteps.single rfl).trans
    (((eval_word ifName).steps { context with frames := (
      Frame.function [condition, yes, no] environment .unlimited :: context.frames) }).trans
      ((InternalSteps.single (by simp [observe])).trans
        ((computed.steps { context with frames := (
          Frame.conditional yes no environment .unlimited :: context.frames) }).trans
          (InternalSteps.single rfl))))

/-- An internal prefix can only remove work from a successful execution. -/
theorem InternalSteps.fuel_le {state next : State} (steps : InternalSteps state next)
    {fuel : Nat} {input rest : List Bool} {observation : Observation}
    (computed : runFuel machine fuel state input = some (observation, rest)) :
    ∃ remaining ≤ fuel, runFuel machine remaining next input = some (observation, rest) := by
  induction steps generalizing fuel with
  | refl => exact ⟨fuel, le_rfl, computed⟩
  | @tail next following steps observed ih =>
      obtain ⟨remaining, bounded, computed⟩ := ih computed
      cases remaining with
      | zero => simp [runFuel] at computed
      | succ remaining =>
          refine ⟨remaining, by omega, ?_⟩
          simpa only [runFuel, machine, observed] using computed

/-- Every genuine first step makes the successful execution budget smaller. -/
theorem internal_prefix_fuel_lt {state first next : State}
    (firstStep : observe state = .step first) (steps : InternalSteps first next)
    {fuel : Nat} {input rest : List Bool} {observation : Observation}
    (computed : runFuel machine fuel state input = some (observation, rest)) :
    ∃ remaining < fuel, runFuel machine remaining next input = some (observation, rest) := by
  cases fuel with
  | zero => simp [runFuel] at computed
  | succ fuel =>
      have later : runFuel machine fuel first input = some (observation, rest) := by
        simpa only [runFuel, machine, firstStep] using computed
      obtain ⟨remaining, bounded, computed⟩ := steps.fuel_le later
      exact ⟨remaining, by omega, computed⟩

end Mettapedia.Languages.Chaitin.PureEvaluation
