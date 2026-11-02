import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledFamilies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateEncoding
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveReturn
import Mettapedia.OSLF.MeTTaIL.GeneralRootFirstConstructor

/-! An actual request's first constructor selects its kernel declaration.
Wrong construction, clause-list and primitive-result variants cannot fire.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

private theorem base_first_head {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat}
    {label schemaLabel inputLabel : String} {schemas inputs restSchemas restInputs : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (shape : (baseLanguage.rewrites[index]?.map RewriteRule.left) = some (node label (node schemaLabel schemas :: restSchemas)))
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node label (node inputLabel inputs :: restInputs)) ordinal trace captured completed history target) :
    schemaLabel = inputLabel := by
  rw [authored] at shape
  have same := Option.some.inj shape
  exact GeneralRuleMatchingHeads.rootFiring_first_constructor_eq
    (GeneralPlanEnvironment.selected_rule plan position) same firing

theorem enabled_build_tuple (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (items rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlBuildConfig" [node "MlBuildTuple", items, rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[16]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_build_family program prepared table _ built position firing
  rcases alternatives with same | same | same
  · subst index
    exact authored
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildVariant") (schemas := [.fvar "tag"])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildPrimitive") (schemas := [.fvar "operator"])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible

#print axioms enabled_build_tuple

theorem enabled_build_variant (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (typeId constructor : Nat) (items rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlBuildConfig" [node "MlBuildVariant" [tag typeId constructor], items, rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[17]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_build_family program prepared table _ built position firing
  rcases alternatives with same | same | same
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildTuple") (schemas := [])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    exact authored
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildPrimitive") (schemas := [.fvar "operator"])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible

#print axioms enabled_build_variant

theorem enabled_build_primitive (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (operator : OCaml.Primitive) (items rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlBuildConfig" [node "MlBuildPrimitive" [primitive operator], items, rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[18]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_build_family program prepared table _ built position firing
  rcases alternatives with same | same | same
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildTuple") (schemas := [])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    have impossible := base_first_head (schemaLabel := "MlBuildVariant") (schemas := [.fvar "tag"])
      (restSchemas := [.fvar "values", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    exact authored

#print axioms enabled_build_primitive

theorem enabled_select_empty (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (argument environment rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseNil", argument, environment, rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[23]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_select_family program prepared table _ built position firing
  rcases alternatives with same | same
  · subst index
    exact authored
  · subst index
    have impossible := base_first_head (schemaLabel := "MlClauseCons") (schemas := [.fvar "pattern", .fvar "body", .fvar "later"])
      (restSchemas := [.fvar "value", .fvar "environment", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible

#print axioms enabled_select_empty

theorem enabled_select_clause (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (clauseArguments : List Pattern) (argument environment rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlSelect" [node "MlClauseCons" clauseArguments, argument, environment, rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[24]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_select_family program prepared table _ built position firing
  rcases alternatives with same | same
  · subst index
    have impossible := base_first_head (schemaLabel := "MlClauseNil") (schemas := [])
      (restSchemas := [.fvar "value", .fvar "environment", .fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    exact authored

#print axioms enabled_select_clause

theorem enabled_answer_value (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (actual : OCaml.Value) (rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlPrimitiveReturned" [node "MlPrimitiveValue" [value actual], rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[20]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_answer_family program prepared table _ built position firing
  rcases alternatives with same | same
  · subst index
    exact authored
  · subst index
    have impossible := base_first_head (schemaLabel := "MlPrimitiveFault") (schemas := [.fvar "fault"])
      (restSchemas := [.fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible

#print axioms enabled_answer_value

theorem enabled_answer_fault (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    {target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (built : prepare program = .ok prepared) (position : (epochPlan prepared table).rules[ordinal]? = some row)
 (error : OCaml.Fault) (rest : Pattern)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlPrimitiveReturned" [node "MlPrimitiveFault" [fault error], rest]) ordinal trace captured completed history target) :
    baseLanguage.rewrites[21]? = some row.authored := by
  obtain ⟨index, authored, alternatives⟩ := enabled_answer_family program prepared table _ built position firing
  rcases alternatives with same | same
  · subst index
    have impossible := base_first_head (schemaLabel := "MlPrimitiveValue") (schemas := [.fvar "value"])
      (restSchemas := [.fvar "rest"]) position authored (by decide +kernel) firing
    simp at impossible
  · subst index
    exact authored

#print axioms enabled_answer_fault

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
