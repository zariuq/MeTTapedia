import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnStructural
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRecursiveInstantiation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternSource

/-! The authored return dispatch and generated function/pattern rows join
at the same intermediate configuration. Source calls may take several
compiled steps while retaining the full caller continuation.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem return_function_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {function argument rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[2]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [function, node "MlKFunction" [argument, rest]]) ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlApply" [function, argument, rest] :=
  base_instance_firing position authored zero (return_function_instance function argument rest) firing

theorem return_let_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {actual parameter body capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[3]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [actual, node "MlKLet" [parameter, body, capturedEnvironment, rest]])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = node "MlMatchOne" [parameter, actual, body, capturedEnvironment, rest] :=
  base_instance_firing position authored zero (return_let_instance actual parameter body capturedEnvironment rest) firing

theorem let_pattern_lowering (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (parameter : OCaml.MatchPattern) (index body : OCaml.Code) (actual : OCaml.Value)
    (captured : OCaml.Environment) (bindings : List OCaml.Value) (continuation : OCaml.Continuation)
    (encodedContinuation : Pattern)
    (parameterResolved : patternReference? pool parameter = some (patternId index))
    (continuationResolved : continuation? pool continuation = some encodedContinuation)
    (matched : OCaml.matchPattern parameter actual = some bindings) :
    OCaml.machineStep program (.returned actual (.letValue parameter body captured :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend captured bindings) continuation)) ∧
    ∃ request assignment,
      state? pool (.returned actual (.letValue parameter body captured :: continuation)) =
        some (node "MlReturn" [value actual, node "MlKLet" [patternId index, code body, environment captured, encodedContinuation]]) ∧
      BaseRuleInstance 3
        (node "MlReturn" [value actual, node "MlKLet" [patternId index, code body, environment captured, encodedContinuation]]) request ∧
      applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).left = request ∧
      state? pool (.evaluate body (OCaml.extend captured bindings) continuation) =
        some (applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).right) := by
  refine ⟨let_source_success program parameter actual body captured bindings continuation matched, ?_⟩
  obtain ⟨assignment, input, output⟩ := match_one_rule_complete parameter index actual bindings body captured encodedContinuation matched
  refine ⟨node "MlMatchOne" [patternId index, value actual, code body, environment captured, encodedContinuation],
    assignment, ?_, return_let_instance _ _ _ _ _, input, ?_⟩
  · simp only [state?, continuation?, frame?, parameterResolved, continuationResolved,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · rw [output]
    simpa only [OCaml.enterBody, matched] using enter_body_encoding body captured continuation continuationResolved matched

#print axioms return_function_firing
#print axioms return_let_firing
#print axioms let_pattern_lowering

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
