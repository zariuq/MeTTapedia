import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnBoolean

/-! Gather continuations retain the unevaluated code suffix and the values
already collected. The last return emits a build request rather than
pretending that construction and primitive evaluation are one rewrite.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_build_more_instance (actual kind next later captured suffix rest : Pattern) :
    BaseRuleInstance 14
      (node "MlReturn" [actual, node "MlKBuild" [kind, node "MlCodeCons" [next, later], captured, suffix, rest]])
      (node "MlEvaluate" [next, captured, node "MlKBuild" [kind, later, captured, node "MlValueCons" [actual, suffix], rest]]) := by
  have fields : (baseLanguage.rewrites[14]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [.fvar "value", node "MlKBuild" [.fvar "kind", node "MlCodeCons" [.fvar "next", .fvar "later"],
        .fvar "environment", .fvar "suffix", .fvar "rest"]],
       node "MlEvaluate" [.fvar "next", .fvar "environment", node "MlKBuild" [.fvar "kind", .fvar "later", .fvar "environment",
        node "MlValueCons" [.fvar "value", .fvar "suffix"], .fvar "rest"]], []) := by decide +kernel
  let assignment : Bindings := [("value", actual), ("kind", kind), ("next", next), ("later", later),
    ("environment", captured), ("suffix", suffix), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem return_build_last_instance (actual kind captured suffix rest : Pattern) :
    BaseRuleInstance 15
      (node "MlReturn" [actual, node "MlKBuild" [kind, node "MlCodeNil", captured, suffix, rest]])
      (node "MlBuildConfig" [kind, node "MlValueCons" [actual, suffix], rest]) := by
  have fields : (baseLanguage.rewrites[15]?).map (fun row => (row.left, row.right, row.premises)) = some
      (node "MlReturn" [.fvar "value", node "MlKBuild" [.fvar "kind", node "MlCodeNil", .fvar "environment", .fvar "suffix", .fvar "rest"]],
       node "MlBuildConfig" [.fvar "kind", node "MlValueCons" [.fvar "value", .fvar "suffix"], .fvar "rest"], []) := by decide +kernel
  let assignment : Bindings := [("value", actual), ("kind", kind), ("environment", captured), ("suffix", suffix), ("rest", rest)]
  simpa [assignment, apply_node, applyBindings] using base_instance_of_fields fields assignment

theorem return_build_more_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {actual : OCaml.Value} {kind : OCaml.Build} {next : OCaml.Code}
    {later : List OCaml.Code} {capturedEnvironment : OCaml.Environment} {suffix : List OCaml.Value}
    {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[14]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value actual, node "MlKBuild" [build kind, codes ((next :: later).map code),
        environment capturedEnvironment, valueList suffix, encodedRest]]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ nextState,
      OCaml.machineStep program (.returned actual (.gather kind (next :: later) capturedEnvironment suffix :: rest)) =
        .ok (some nextState) ∧ state? pool nextState = some target := by
  have realization := return_build_more_instance (value actual) (build kind) (code next) (codes (later.map code))
    (environment capturedEnvironment) (valueList suffix) encodedRest
  have encodedSource : codes ((next :: later).map code) = node "MlCodeCons" [code next, codes (later.map code)] := rfl
  rw [encodedSource] at firing
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero realization firing
  refine ⟨sameCaptures, emptyHistory, .evaluate next capturedEnvironment (.gather kind later capturedEnvironment (actual :: suffix) :: rest),
    rfl, ?_⟩
  rw [output]
  simp only [state?, continuation?, frame?, resolved, valueList, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem return_build_last_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {actual kind capturedEnvironment suffix rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[15]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [actual, node "MlKBuild" [kind, node "MlCodeNil", capturedEnvironment, suffix, rest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlBuildConfig" [kind, node "MlValueCons" [actual, suffix], rest] :=
  base_instance_firing position authored zero (return_build_last_instance actual kind capturedEnvironment suffix rest) firing

#print axioms return_build_more_source_step
#print axioms return_build_last_firing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
