import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativePreservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointControls

/-! Regression controls for actual-row classification and source-preserving
administration. A wrong constructor, result variant or pattern identity
cannot be hidden by choosing a different prepared declaration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.AdministrativeControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open ServiceControls

theorem primitive_step_preserves_value (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare primitiveProgram = .ok prepared)
    (invariant : SourceProviderInvariant (patterns primitiveProgram) table)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlPrimitiveRequest" [primitive .add, valueList [number 40, number 2], encodedRest])
      ordinal trace captured completed history target) :
    ∃ rank, ControlPoint primitiveProgram (.returned (number 42) rest) target rank ∧ rank < 2 :=
  administrative_firing_preserves_source primitiveProgram prepared table built invariant
    ControlPointControls.value_across_three_phases.1 (by decide +kernel) position firing

theorem build_cannot_use_primitive_query (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (items rest : Pattern) (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (wrong : baseLanguage.rewrites[19]? = some row.authored) :
    ¬ ∃ target trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
        (node "MlBuildConfig" [node "MlBuildTuple", items, rest]) ordinal trace captured completed history target := by
  rintro ⟨target, trace, captured, completed, history, firing⟩
  have correct := enabled_build_tuple program prepared table built position items rest firing
  have different : baseLanguage.rewrites[16]? ≠ baseLanguage.rewrites[19]? := by decide +kernel
  exact different (correct.trans wrong.symm)

theorem primitive_fault_cannot_use_value_row (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (rest : Pattern) (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (wrong : baseLanguage.rewrites[20]? = some row.authored) :
    ¬ ∃ target trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
        (node "MlPrimitiveReturned" [primitiveResult (.error .divisionByZero), rest])
        ordinal trace captured completed history target := by
  rintro ⟨target, trace, captured, completed, history, firing⟩
  have correct := enabled_answer_fault program prepared table built position .divisionByZero rest firing
  have different : baseLanguage.rewrites[21]? ≠ baseLanguage.rewrites[20]? := by decide +kernel
  exact different (correct.trans wrong.symm)

theorem pattern_zero_cannot_read_row_one {plan : GeneralExecutionAdmission.Plan}
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan} (parameter : OCaml.MatchPattern)
    (rest : List Pattern) (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules 1 parameter)[0]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true) :
    ¬ ∃ target trace captured completed history,
      GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
        (node "MlMatchOne" (patternId 0 :: rest)) ordinal trace captured completed history target := by
  rintro ⟨target, trace, captured, completed, history, firing⟩
  have impossible := match_one_row_index position authored zero firing
  omega

#print axioms primitive_step_preserves_value
#print axioms build_cannot_use_primitive_query
#print axioms primitive_fault_cannot_use_value_row
#print axioms pattern_zero_cannot_read_row_one

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.AdministrativeControls
