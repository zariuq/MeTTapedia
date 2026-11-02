import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBaseCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlReturnCons

/-! Source transition contracts construct actual shared root firings, with
typing and defined captures derived from encoded source/successor states.
The reverse direction is the previously proved receipt readback.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem base_instance_encoded_coverage {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pool : List OCaml.MatchPattern}
    {sourceState targetState : OCaml.MachineState} {source target : Pattern}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (sourceEncoded : state? pool sourceState = some source)
    (targetEncoded : state? pool targetState = some target)
    (realization : BaseRuleInstance index source target) :
    ∃ trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      source ordinal trace captured captured [] target := by
  obtain ⟨premiseFree, assignment, input, output⟩ := realization.realize row.authored authored
  exact base_encoded_firing_construct position terms authored compiled premiseFree sourceEncoded targetEncoded input output

theorem cons_head_root_coverage {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {pool : List OCaml.MatchPattern}
    {head tail : OCaml.Value} {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[13]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (resolved : continuation? pool rest = some encodedRest) :
    ∃ trace captured, GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlReturn" [value head, node "MlKConsHead" [value tail, encodedRest]]) ordinal trace captured captured []
      (node "MlReturn" [value (.cons head tail), encodedRest]) := by
  apply base_instance_encoded_coverage (pool := pool) (sourceState := .returned head (.consHead tail :: rest))
    (targetState := .returned (.cons head tail) rest) position terms authored compiled
  · simp only [state?, continuation?, frame?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · exact return_cons_head_instance (value head) (value tail) encodedRest

theorem cons_head_root_iff {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {pool : List OCaml.MatchPattern}
    {head tail : OCaml.Value} {rest : OCaml.Continuation} {encodedRest target : Pattern}
    (position : plan.rules[ordinal]? = some row)
    (terms : plan.snapshot.language.terms = baseLanguage.terms)
    (authored : baseLanguage.rewrites[13]? = some row.authored)
    (compiled : GeneralRuleBindingInference.compile? baseLanguage row.authored = some row.binding)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (resolved : continuation? pool rest = some encodedRest) :
    (∃ trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
        (node "MlReturn" [value head, node "MlKConsHead" [value tail, encodedRest]]) ordinal trace captured completed history target) ↔
      target = node "MlReturn" [value (.cons head tail), encodedRest] := by
  constructor
  · rintro ⟨trace, captured, completed, history, firing⟩
    exact (base_instance_firing position authored zero (return_cons_head_instance (value head) (value tail) encodedRest) firing).2.2
  · rintro rfl
    obtain ⟨trace, captured, firing⟩ := cons_head_root_coverage position terms authored compiled resolved
    exact ⟨trace, captured, captured, [], firing⟩

#print axioms base_instance_encoded_coverage
#print axioms cons_head_root_coverage
#print axioms cons_head_root_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
