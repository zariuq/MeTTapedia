import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBoolean
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternSource

/-! Returning a match scrutinee and advancing the clause cursor retain the
authored clause order. The empty cursor represents source match failure.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_match_instance (actual clauses captured rest : Pattern) :
    BaseRuleInstance 22 (node "MlReturn" [actual, node "MlKMatch" [clauses, captured, rest]])
      (node "MlSelect" [clauses, actual, captured, rest]) := by
  have fields : (baseLanguage.rewrites[22]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [.fvar "value", node "MlKMatch" [.fvar "clauses", .fvar "environment", .fvar "rest"]],
       node "MlSelect" [.fvar "clauses", .fvar "value", .fvar "environment", .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("value", actual), ("clauses", clauses), ("environment", captured), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem select_empty_instance (actual captured rest : Pattern) :
    BaseRuleInstance 23 (node "MlSelect" [node "MlClauseNil", actual, captured, rest])
      (node "MlFault" [node "MlMatchFailure"]) := by
  have fields : (baseLanguage.rewrites[23]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlSelect" [node "MlClauseNil", .fvar "value", .fvar "environment", .fvar "rest"],
       node "MlFault" [node "MlMatchFailure"], []) := by decide +kernel
  let assignment : Bindings := [("value", actual), ("environment", captured), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem select_clause_instance (parameter body later actual captured rest : Pattern) :
    BaseRuleInstance 24 (node "MlSelect" [node "MlClauseCons" [parameter, body, later], actual, captured, rest])
      (node "MlTryClause" [parameter, actual, body, later, captured, rest]) := by
  have fields : (baseLanguage.rewrites[24]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlSelect" [node "MlClauseCons" [.fvar "pattern", .fvar "body", .fvar "later"],
        .fvar "value", .fvar "environment", .fvar "rest"],
       node "MlTryClause" [.fvar "pattern", .fvar "value", .fvar "body", .fvar "later", .fvar "environment", .fvar "rest"], []) :=
    by decide +kernel
  let assignment : Bindings := [("pattern", parameter), ("body", body), ("later", later),
    ("value", actual), ("environment", captured), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem return_match_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {actual clauses capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[22]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [actual, node "MlKMatch" [clauses, capturedEnvironment, rest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlSelect" [clauses, actual, capturedEnvironment, rest] :=
  base_instance_firing position authored zero (return_match_instance actual clauses capturedEnvironment rest) firing

theorem select_empty_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {actual : OCaml.Value} {capturedEnvironment : OCaml.Environment}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[23]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseNil", value actual, environment capturedEnvironment, encodedRest])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned actual (.matchValue [] capturedEnvironment :: rest)) = .ok (some next) ∧
      state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (select_empty_instance (value actual) (environment capturedEnvironment) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .halted (.error .matchFailure), rfl, ?_⟩
  rw [output]
  rfl

theorem select_clause_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {parameter body later actual capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[24]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseCons" [parameter, body, later], actual, capturedEnvironment, rest])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      target = node "MlTryClause" [parameter, actual, body, later, capturedEnvironment, rest] :=
  base_instance_firing position authored zero (select_clause_instance parameter body later actual capturedEnvironment rest) firing

#print axioms return_match_firing
#print axioms select_empty_source_step
#print axioms select_clause_firing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
