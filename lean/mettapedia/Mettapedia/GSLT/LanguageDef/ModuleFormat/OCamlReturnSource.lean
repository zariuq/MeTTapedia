import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnReadout

/-! A shared return firing reflects to the independent source machine.
The source program, environment, returned value and entire continuation are
preserved. No additional evaluation step is invented by the target receipt.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_argument_source_step {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {program : OCaml.Program}
    {pool : List OCaml.MatchPattern} {argument : OCaml.Value} {function : OCaml.Code}
    {capturedEnvironment : OCaml.Environment} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[1]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value argument, node "MlKArgument"
        [code function, environment capturedEnvironment, encodedRest]]) ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      ∃ next,
        OCaml.machineStep program (.returned argument (.argument function capturedEnvironment :: rest)) = .ok (some next) ∧
        state? pool next = some target := by
  obtain ⟨sameCaptures, emptyHistory, actualTarget⟩ := return_argument_firing position authored zero firing
  refine ⟨sameCaptures, emptyHistory,
    .evaluate function capturedEnvironment (.function argument :: rest), rfl, ?_⟩
  rw [actualTarget]
  simp only [state?, continuation?, resolved, frame?, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

#print axioms return_argument_source_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
