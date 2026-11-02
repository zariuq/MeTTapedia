import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnStructural

/-! Boolean return rows preserve short-circuiting and the source Boolean
result check. The row indices remain attached to the authored module.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem base_instance_of_fields {index : Nat} {left right : Pattern}
    (computed : (baseLanguage.rewrites[index]?).map (fun row => (row.left, row.right, row.premises)) =
      some (left, right, [])) (assignment : Bindings) :
    BaseRuleInstance index (applyBindings assignment left) (applyBindings assignment right) := by
  constructor
  intro row authored
  rw [authored] at computed
  have fields := Option.some.inj computed
  have lhs := congrArg (fun fields => fields.1) fields
  have rhs := congrArg (fun fields => fields.2.1) fields
  have premises := congrArg (fun fields => fields.2.2) fields
  dsimp only at lhs rhs premises
  exact ⟨premises, assignment, congrArg (applyBindings assignment) lhs, congrArg (applyBindings assignment) rhs⟩

theorem return_and_instance (choice : Bool) (right captured rest : Pattern) :
    BaseRuleInstance (if choice then 7 else 6)
      (node "MlReturn" [literal (.boolean choice), node "MlKAnd" [right, captured, rest]])
      (if choice then node "MlEvaluate" [right, captured, node "MlKBoolean" [rest]]
        else node "MlReturn" [literal (.boolean false), rest]) := by
  let assignment : Bindings := [("right", right), ("environment", captured), ("rest", rest)]
  cases choice with
  | false =>
      have fields : (baseLanguage.rewrites[6]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlFalse", node "MlKAnd" [.fvar "right", .fvar "environment", .fvar "rest"]],
            node "MlReturn" [node "MlFalse", .fvar "rest"], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment
  | true =>
      have fields : (baseLanguage.rewrites[7]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlTrue", node "MlKAnd" [.fvar "right", .fvar "environment", .fvar "rest"]],
            node "MlEvaluate" [.fvar "right", .fvar "environment", node "MlKBoolean" [.fvar "rest"]], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment

theorem return_or_instance (choice : Bool) (right captured rest : Pattern) :
    BaseRuleInstance (if choice then 8 else 9)
      (node "MlReturn" [literal (.boolean choice), node "MlKOr" [right, captured, rest]])
      (if choice then node "MlReturn" [literal (.boolean true), rest]
        else node "MlEvaluate" [right, captured, node "MlKBoolean" [rest]]) := by
  let assignment : Bindings := [("right", right), ("environment", captured), ("rest", rest)]
  cases choice with
  | false =>
      have fields : (baseLanguage.rewrites[9]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlFalse", node "MlKOr" [.fvar "right", .fvar "environment", .fvar "rest"]],
            node "MlEvaluate" [.fvar "right", .fvar "environment", node "MlKBoolean" [.fvar "rest"]], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment
  | true =>
      have fields : (baseLanguage.rewrites[8]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlTrue", node "MlKOr" [.fvar "right", .fvar "environment", .fvar "rest"]],
            node "MlReturn" [node "MlTrue", .fvar "rest"], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment

theorem return_boolean_instance (choice : Bool) (rest : Pattern) :
    BaseRuleInstance (if choice then 10 else 11)
      (node "MlReturn" [literal (.boolean choice), node "MlKBoolean" [rest]])
      (node "MlReturn" [literal (.boolean choice), rest]) := by
  let assignment : Bindings := [("rest", rest)]
  cases choice with
  | false =>
      have fields : (baseLanguage.rewrites[11]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlFalse", node "MlKBoolean" [.fvar "rest"]],
            node "MlReturn" [node "MlFalse", .fvar "rest"], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment
  | true =>
      have fields : (baseLanguage.rewrites[10]?).map (fun row => (row.left, row.right, row.premises)) =
          some (node "MlReturn" [node "MlTrue", node "MlKBoolean" [.fvar "rest"]],
            node "MlReturn" [node "MlTrue", .fvar "rest"], []) := by decide +kernel
      simpa [assignment, apply_node, applyBindings, literal] using base_instance_of_fields fields assignment

theorem return_and_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {choice : Bool} {right : OCaml.Code}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if choice then 7 else 6]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node "MlKAnd" [code right, environment capturedEnvironment, encodedRest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned (.literal (.boolean choice)) (.andThen right capturedEnvironment :: rest)) =
        .ok (some next) ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (return_and_instance choice (code right) (environment capturedEnvironment) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  cases choice with
  | false =>
      refine ⟨.returned (.literal (.boolean false)) rest, rfl, ?_⟩
      rw [output]
      simp only [Bool.false_eq_true, if_false, state?, value, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | true =>
      refine ⟨.evaluate right capturedEnvironment (.booleanResult :: rest), rfl, ?_⟩
      rw [output]
      simp only [if_true, state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem return_or_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {choice : Bool} {right : OCaml.Code}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if choice then 8 else 9]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node "MlKOr" [code right, environment capturedEnvironment, encodedRest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned (.literal (.boolean choice)) (.orElse right capturedEnvironment :: rest)) =
        .ok (some next) ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (return_or_instance choice (code right) (environment capturedEnvironment) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  cases choice with
  | false =>
      refine ⟨.evaluate right capturedEnvironment (.booleanResult :: rest), rfl, ?_⟩
      rw [output]
      simp only [Bool.false_eq_true, if_false, state?, continuation?, frame?, resolved,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  | true =>
      refine ⟨.returned (.literal (.boolean true)) rest, rfl, ?_⟩
      rw [output]
      simp only [if_true, state?, value, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem return_boolean_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {choice : Bool} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if choice then 10 else 11]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node "MlKBoolean" [encodedRest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned (.literal (.boolean choice)) (.booleanResult :: rest)) =
        .ok (some next) ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (return_boolean_instance choice encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .returned (.literal (.boolean choice)) rest, rfl, ?_⟩
  rw [output]
  simp only [state?, value, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms return_and_source_step
#print axioms return_or_source_step
#print axioms return_boolean_source_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
