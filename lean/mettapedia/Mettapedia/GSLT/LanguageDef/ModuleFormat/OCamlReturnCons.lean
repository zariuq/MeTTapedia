import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnStructural

/-! Actual list-continuation firings preserve the source evaluation order
and the complete continuation. Both list return frames are covered.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_cons_tail_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {tail : OCaml.Value} {head : OCaml.Code}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[12]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value tail, node "MlKConsTail" [code head, environment capturedEnvironment, encodedRest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned tail (.consTail head capturedEnvironment :: rest)) = .ok (some next) ∧
      state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (return_cons_tail_instance (value tail) (code head) (environment capturedEnvironment) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .evaluate head capturedEnvironment (.consHead tail :: rest), rfl, ?_⟩
  rw [output]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem return_cons_head_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {head tail : OCaml.Value} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[13]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value head, node "MlKConsHead" [value tail, encodedRest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ next,
      OCaml.machineStep program (.returned head (.consHead tail :: rest)) = .ok (some next) ∧
      state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, output⟩ := base_instance_firing position authored zero
    (return_cons_head_instance (value head) (value tail) encodedRest) firing
  refine ⟨sameCaptures, emptyHistory, .returned (.cons head tail) rest, rfl, ?_⟩
  rw [output]
  simp only [state?, resolved, value, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms return_cons_tail_source_step
#print axioms return_cons_head_source_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
