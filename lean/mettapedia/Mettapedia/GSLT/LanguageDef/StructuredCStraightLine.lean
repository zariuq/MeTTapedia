import Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
import Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime

/-!
# Straight-line execution of the generated StructuredC fragment

Generated call-guard bodies use five statement forms: a declaration bound
to an evaluated expression, an effect, a two-way branch, a switch, and a
return.  Under a relation environment supplied by an external handler, each
authored StructuredC rule for these forms has exactly one value reduct.  This
module packages that fact as a small-step function `step?` on configurations,
proved sound against `rewriteAt`, and iterates it to a halted configuration.

The payoff is that the first-reduct normalization of a generated body from a
loaded state is the evaluation of `runSteps?`, a direct function of the
handler.  A row simulation is then a computation, not a hand-written chain of
rewrite equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuredCStraightLine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

/-- A halted configuration. -/
def isHalted : Pattern → Bool
  | .apply "structured-c:halted" [_, _, _] => true
  | _ => false

/-- The value path of one expression evaluation. -/
def evaluateValue? (handler : ExternalHandler) (expression environment receipt : Pattern) :
    Option (Pattern × Pattern × Pattern) :=
  match evaluate? handler expression environment receipt with
  | some ⟨.value value, environment', receipt'⟩ => some (value, environment', receipt')
  | _ => none

theorem evaluate?_of_evaluateValue? {handler : ExternalHandler}
    {expression environment receipt value environment' receipt' : Pattern}
    (evaluated : evaluateValue? handler expression environment receipt =
      some (value, environment', receipt')) :
    evaluate? handler expression environment receipt = some ⟨.value value, environment', receipt'⟩ := by
  unfold evaluateValue? at evaluated
  split at evaluated
  · rename_i step value' environment'' receipt'' found
    cases evaluated
    exact found
  · cases evaluated

/-- The evaluation tuples of a handler-backed relation environment at a
value evaluation. -/
theorem evaluate_tuples_of_value {handler : ExternalHandler}
    {expression environment receipt value environment' receipt' : Pattern}
    (evaluated : evaluate? handler expression environment receipt =
      some ⟨.value value, environment', receipt'⟩) :
    ∀ result outputEnvironment outputReceipt,
      (relationEnv handler).tuples "StructuredCEvaluate"
          [expression, environment, receipt, result, outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value, environment', receipt']] := by
  intro result outputEnvironment outputReceipt
  rw [relationEnv_evaluate_tuples, evaluated]

/-- One statement of the generated fragment, at the head of a running
configuration. -/
def statementStep? (handler : ExternalHandler) (statement rest environment receipt : Pattern) :
    Option Pattern :=
  match statement with
  | .apply "structured-c:declare" [slot, _, expression] => do
      let (value, environment', receipt') ←
        evaluateValue? handler expression environment receipt
      let next ← store? environment' slot value
      pure (run rest next receipt')
  | .apply "structured-c:effect" [expression] => do
      let (_, environment', receipt') ← evaluateValue? handler expression environment receipt
      pure (run rest environment' receipt')
  | .apply "structured-c:if" [condition, thenBranch, elseBranch] => do
      let (value, environment', receipt') ←
        evaluateValue? handler condition environment receipt
      let selected ← selectBranch? value thenBranch elseBranch
      pure (run (appendStatements selected rest) environment' receipt')
  | .apply "structured-c:switch" [scrutinee, cases, defaultBranch] => do
      let (value, environment', receipt') ←
        evaluateValue? handler scrutinee environment receipt
      let selected ← selectCase? value defaultBranch cases
      pure (run (appendStatements selected rest) environment' receipt')
  | .apply "structured-c:return" [expression] => do
      let (value, environment', receipt') ←
        evaluateValue? handler expression environment receipt
      pure (halted (a "structured-c:outcome-return" [value]) environment' receipt')
  | _ => none

/-- One small step of a configuration in the generated fragment. -/
def step? (handler : ExternalHandler) : Pattern → Option Pattern
  | .apply "structured-c:run"
      [.apply "structured-c:statements-cons" [statement, rest], environment, receipt] =>
      statementStep? handler statement rest environment receipt
  | .apply "structured-c:run"
      [.apply "structured-c:statements-append"
        [.apply "structured-c:statements-nil" [], continuation], environment, receipt] =>
      some (run continuation environment receipt)
  | .apply "structured-c:run"
      [.apply "structured-c:statements-append"
        [.apply "structured-c:statements-cons" [statement, tail], continuation],
        environment, receipt] =>
      some (run (consStatement statement (appendStatements tail continuation)) environment
        receipt)
  | .apply "structured-c:run" [.apply "structured-c:statements-nil" [], environment, receipt] =>
      some (halted (a "structured-c:outcome-fallthrough") environment receipt)
  | _ => none

/-- Running out of statements halts with the fallthrough outcome. -/
theorem emptyTransition_rewriteAt_exact (relationEnv : RelationEnv)
    (environment receipt : Pattern) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run nilStatements environment receipt) =
      [halted (a "structured-c:outcome-fallthrough") environment receipt] := by
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run nilStatements environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

/-- A statement step is the unique value reduct of the authored rules. -/
theorem statementStep?_sound (handler : ExternalHandler)
    {statement rest environment receipt next : Pattern}
    (stepped : statementStep? handler statement rest environment receipt = some next) :
    rewriteAt (engineBasePremises (relationEnv handler)) language 1
        (run (consStatement statement rest) environment receipt) = [next] := by
  unfold statementStep? at stepped
  split at stepped
  · rename_i slot type expression
    cases evaluated : evaluateValue? handler expression environment receipt with
    | none => simp [evaluated] at stepped
    | some triple =>
        obtain ⟨value, environment', receipt'⟩ := triple
        cases stored : store? environment' slot value with
        | none => simp [evaluated, stored] at stepped
        | some nextEnvironment =>
            simp [evaluated, stored, Option.bind] at stepped
            subst stepped
            exact declareValueTransition_rewriteAt_exact_of_tuples (relationEnv handler)
              slot type expression rest environment receipt value environment' receipt'
              nextEnvironment (evaluate_tuples_of_value (evaluate?_of_evaluateValue? evaluated))
              (fun _ => by rw [relationEnv_store_tuples, stored])
  · rename_i expression
    cases evaluated : evaluateValue? handler expression environment receipt with
    | none => simp [evaluated] at stepped
    | some triple =>
        obtain ⟨value, environment', receipt'⟩ := triple
        simp [evaluated, Option.bind] at stepped
        subst stepped
        exact effectValueTransition_rewriteAt_exact_of_tuples (relationEnv handler) expression
          rest environment receipt value environment' receipt'
          (evaluate_tuples_of_value (evaluate?_of_evaluateValue? evaluated))
  · rename_i condition thenBranch elseBranch
    cases evaluated : evaluateValue? handler condition environment receipt with
    | none => simp [evaluated] at stepped
    | some triple =>
        obtain ⟨value, environment', receipt'⟩ := triple
        cases selected : selectBranch? value thenBranch elseBranch with
        | none => simp [evaluated, selected] at stepped
        | some branch =>
            simp [evaluated, selected, Option.bind] at stepped
            subst stepped
            exact ifValueTransition_rewriteAt_exact_of_tuples (relationEnv handler) condition
              thenBranch elseBranch rest environment receipt value environment' receipt' branch
              (evaluate_tuples_of_value (evaluate?_of_evaluateValue? evaluated))
              (fun _ => by rw [relationEnv_branch_tuples, selected])
  · rename_i scrutinee cases defaultBranch
    cases evaluated : evaluateValue? handler scrutinee environment receipt with
    | none => simp [evaluated] at stepped
    | some triple =>
        obtain ⟨value, environment', receipt'⟩ := triple
        cases selected : selectCase? value defaultBranch cases with
        | none => simp [evaluated, selected] at stepped
        | some branch =>
            simp [evaluated, selected, Option.bind] at stepped
            subst stepped
            exact switchValueTransition_rewriteAt_exact_of_tuples (relationEnv handler)
              scrutinee cases defaultBranch rest environment receipt value environment' receipt'
              branch (evaluate_tuples_of_value (evaluate?_of_evaluateValue? evaluated))
              (fun _ => by rw [relationEnv_case_tuples, selected])
  · rename_i expression
    cases evaluated : evaluateValue? handler expression environment receipt with
    | none => simp [evaluated] at stepped
    | some triple =>
        obtain ⟨value, environment', receipt'⟩ := triple
        simp [evaluated, Option.bind] at stepped
        subst stepped
        exact returnValueTransition_rewriteAt_exact_of_tuples (relationEnv handler) expression
          rest environment receipt value environment' receipt'
          (evaluate_tuples_of_value (evaluate?_of_evaluateValue? evaluated))
  · cases stepped

/-- A step of the fragment is the unique reduct of the authored rules. -/
theorem step?_sound (handler : ExternalHandler) {config next : Pattern}
    (stepped : step? handler config = some next) :
    rewriteAt (engineBasePremises (relationEnv handler)) language 1 config = [next] := by
  unfold step? at stepped
  split at stepped
  · rename_i statement rest environment receipt
    exact statementStep?_sound handler stepped
  · rename_i continuation environment receipt
    cases stepped
    exact appendEmptyTransition_rewriteAt_exact (relationEnv handler) continuation environment
      receipt
  · rename_i statement tail continuation environment receipt
    cases stepped
    exact appendConsTransition_rewriteAt_exact (relationEnv handler) statement tail continuation
      environment receipt
  · rename_i environment receipt
    cases stepped
    exact emptyTransition_rewriteAt_exact (relationEnv handler) environment receipt
  · cases stepped

theorem rewriteAt_halted (relationEnv : RelationEnv) {config : Pattern}
    (halted : isHalted config = true) :
    rewriteAt (engineBasePremises relationEnv) language 1 config = [] := by
  unfold isHalted at halted
  split at halted
  · rename_i outcome environment receipt
    exact halted_rewriteAt_empty relationEnv outcome environment receipt
  · cases halted

/-- Iterate the fragment's step until a halted configuration, within a step
budget. -/
def runSteps? (handler : ExternalHandler) : Nat → Pattern → Option Pattern
  | 0, config => if isHalted config then some config else none
  | fuel + 1, config =>
      if isHalted config then some config
      else
        match step? handler config with
        | some next => runSteps? handler fuel next
        | none => none

theorem isHalted_of_runSteps? (handler : ExternalHandler) :
    ∀ {fuel : Nat} {config final : Pattern}, runSteps? handler fuel config = some final →
      isHalted final = true
  | 0, config, final, ran => by
      unfold runSteps? at ran
      split at ran
      · rename_i halted
        cases ran
        exact halted
      · cases ran
  | fuel + 1, config, final, ran => by
      unfold runSteps? at ran
      split at ran
      · rename_i halted
        cases ran
        exact halted
      · split at ran
        · exact isHalted_of_runSteps? handler ran
        · cases ran

/-- The first-reduct normalization of the fragment is the iterated step. -/
theorem normalizeFirst_of_runSteps? (handler : ExternalHandler) :
    ∀ {fuel : Nat} {config final : Pattern}, runSteps? handler fuel config = some final →
      normalizeFirstUsing (relationEnv handler) language 1 fuel config = final
  | 0, config, final, ran => by
      unfold runSteps? at ran
      split at ran
      · cases ran
        rfl
      · cases ran
  | fuel + 1, config, final, ran => by
      unfold runSteps? at ran
      split at ran
      · rename_i halted
        cases ran
        unfold normalizeFirstUsing normalizeFirstAt
        rw [rewriteAt_halted (relationEnv handler) halted]
      · rename_i notHalted
        split at ran
        · rename_i next stepped
          unfold normalizeFirstUsing normalizeFirstAt
          rw [step?_sound handler stepped]
          exact normalizeFirst_of_runSteps? handler ran
        · cases ran

end Mettapedia.GSLT.LanguageDef.StructuredCStraightLine
