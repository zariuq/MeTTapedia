import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnReadout

/-! Actual Boolean branch receipts preserve the chosen source arm, caller
environment and full continuation. Both authored branch rows are covered by
one theorem about the independent source-machine transition.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem branch_return_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {bound : List TypeExpr}
    (choice : Bool) {yes no capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if choice then 4 else 5]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node "MlKBranch" [yes, no, capturedEnvironment, rest]]) ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlEvaluate" [if choice then yes else no, capturedEnvironment, rest] := by
  have fields : (row.authored.left, row.authored.right, row.authored.premises) =
      (node "MlReturn" [literal (.boolean choice), node "MlKBranch"
        [.fvar "yes", .fvar "no", .fvar "environment", .fvar "rest"]],
       node "MlEvaluate" [.fvar (if choice then "yes" else "no"), .fvar "environment", .fvar "rest"], []) := by
    cases choice with
    | false =>
      change baseLanguage.rewrites[5]? = some row.authored at authored
      have computed : (baseLanguage.rewrites[5]?).map (fun row => (row.left, row.right, row.premises)) =
        some (node "MlReturn" [literal (.boolean false), node "MlKBranch"
          [.fvar "yes", .fvar "no", .fvar "environment", .fvar "rest"]],
         node "MlEvaluate" [.fvar "no", .fvar "environment", .fvar "rest"], []) := by decide +kernel
      rw [authored] at computed
      exact Option.some.inj computed
    | true =>
      change baseLanguage.rewrites[4]? = some row.authored at authored
      have computed : (baseLanguage.rewrites[4]?).map (fun row => (row.left, row.right, row.premises)) =
        some (node "MlReturn" [literal (.boolean true), node "MlKBranch"
          [.fvar "yes", .fvar "no", .fvar "environment", .fvar "rest"]],
         node "MlEvaluate" [.fvar "yes", .fvar "environment", .fvar "rest"], []) := by decide +kernel
      rw [authored] at computed
      exact Option.some.inj computed
  have left := congrArg (fun fields => fields.1) fields
  have right := congrArg (fun fields => fields.2.1) fields
  have premiseFree := congrArg (fun fields => fields.2.2) fields
  dsimp only at left right premiseFree
  let bindings : Bindings := [("yes", yes), ("no", no), ("environment", capturedEnvironment), ("rest", rest)]
  have instantiated : applyBindings bindings row.authored.left =
      node "MlReturn" [literal (.boolean choice), node "MlKBranch" [yes, no, capturedEnvironment, rest]] := by
    rw [left]
    simp only [apply_node, List.map_cons, List.map_nil, apply_literal]
    simp [bindings, applyBindings]
  obtain ⟨sameCaptures, emptyHistory, output⟩ := pure_base_root_target position authored zero premiseFree instantiated firing
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  rw [right] at output
  cases choice <;> simpa [bindings, apply_node, applyBindings] using output

theorem branch_return_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {choice : Bool} {yes no : OCaml.Code}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[if choice then 4 else 5]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [literal (.boolean choice), node "MlKBranch"
        [code yes, code no, environment capturedEnvironment, encodedRest]]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      ∃ next,
        OCaml.machineStep program (.returned (.literal (.boolean choice)) (.branch yes no capturedEnvironment :: rest)) =
          .ok (some next) ∧ state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, actualTarget⟩ := branch_return_firing choice position authored zero firing
  refine ⟨sameCaptures, emptyHistory, .evaluate (if choice then yes else no) capturedEnvironment rest, rfl, ?_⟩
  rw [actualTarget]
  cases choice <;> simp only [Bool.false_eq_true, if_false, if_true, state?, resolved,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms branch_return_firing
#print axioms branch_return_source_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
