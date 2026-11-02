import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEnabledRowOrigin

/-! Constructor-specific inverses for every prepared administrative family.
These classify actual root firings; no rule-selection oracle is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem enabled_evaluate_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlEvaluate" inputs) ordinal trace captured completed history target) :
    ∃ reference instruction, program.instruction? reference = some instruction ∧
      compileInstruction? (patterns program) reference instruction = some row.authored := by
  rcases enabled_prepared_row_origin program prepared table "MlEvaluate" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlEvaluate" = ([] : List Nat) := by decide +kernel
    rw [candidates] at compatible
    cases compatible
  · exact instruction.2
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms enabled_evaluate_family

theorem enabled_apply_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlApply" inputs) ordinal trace captured completed history target) :
    ∃ reference instruction rows, program.instruction? reference = some instruction ∧
      functionRules? program (patterns program) reference instruction = some rows ∧ row.authored ∈ rows := by
  rcases enabled_prepared_row_origin program prepared table "MlApply" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlApply" = ([] : List Nat) := by decide +kernel
    rw [candidates] at compatible
    cases compatible
  · simp at instruction
  · exact function.2
  · simp at pattern
  · simp at clause

#print axioms enabled_apply_family

theorem enabled_match_one_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlMatchOne" inputs) ordinal trace captured completed history target) :
    baseLanguage.rewrites[25]? = some row.authored ∨
    ∃ index parameter, (patterns program)[index]? = some parameter ∧
      row.authored = (patternRules index parameter)[0]'(by simp [patternRules]) := by
  rcases enabled_prepared_row_origin program prepared table "MlMatchOne" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlMatchOne" = [25] := by decide +kernel
    rw [candidates] at compatible
    have same : index = 25 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible
    subst index
    exact .inl authored
  · simp at instruction
  · simp at function
  · exact .inr pattern.2
  · simp at clause

#print axioms enabled_match_one_family

theorem enabled_clause_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlTryClause" inputs) ordinal trace captured completed history target) :
    baseLanguage.rewrites[26]? = some row.authored ∨
    ∃ index parameter, (patterns program)[index]? = some parameter ∧
      row.authored = (patternRules index parameter)[1]'(by simp [patternRules]) := by
  rcases enabled_prepared_row_origin program prepared table "MlTryClause" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlTryClause" = [26] := by decide +kernel
    rw [candidates] at compatible
    have same : index = 26 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible
    subst index
    exact .inl authored
  · simp at instruction
  · simp at function
  · simp at pattern
  · exact .inr clause.2

#print axioms enabled_clause_family

theorem enabled_select_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlSelect" inputs) ordinal trace captured completed history target) :
    ∃ index, baseLanguage.rewrites[index]? = some row.authored ∧ (index = 23 ∨ index = 24) := by
  rcases enabled_prepared_row_origin program prepared table "MlSelect" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlSelect" = [23, 24] := by decide +kernel
    rw [candidates] at compatible
    exact ⟨index, authored, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible⟩
  · simp at instruction
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms enabled_select_family

theorem enabled_build_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlBuildConfig" inputs) ordinal trace captured completed history target) :
    ∃ index, baseLanguage.rewrites[index]? = some row.authored ∧ (index = 16 ∨ index = 17 ∨ index = 18) := by
  rcases enabled_prepared_row_origin program prepared table "MlBuildConfig" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlBuildConfig" = [16, 17, 18] := by decide +kernel
    rw [candidates] at compatible
    exact ⟨index, authored, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible⟩
  · simp at instruction
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms enabled_build_family

theorem enabled_primitive_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlPrimitiveRequest" inputs) ordinal trace captured completed history target) :
    baseLanguage.rewrites[19]? = some row.authored := by
  rcases enabled_prepared_row_origin program prepared table "MlPrimitiveRequest" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlPrimitiveRequest" = [19] := by decide +kernel
    rw [candidates] at compatible
    have same : index = 19 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible
    subst index
    exact authored
  · simp at instruction
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms enabled_primitive_family

theorem enabled_answer_family (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node "MlPrimitiveReturned" inputs) ordinal trace captured completed history target) :
    ∃ index, baseLanguage.rewrites[index]? = some row.authored ∧ (index = 20 ∨ index = 21) := by
  rcases enabled_prepared_row_origin program prepared table "MlPrimitiveReturned" inputs built position firing with
    kernel | instruction | function | pattern | clause
  · obtain ⟨index, authored, compatible⟩ := kernel
    have candidates : kernelCandidates "MlPrimitiveReturned" = [20, 21] := by decide +kernel
    rw [candidates] at compatible
    exact ⟨index, authored, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using compatible⟩
  · simp at instruction
  · simp at function
  · simp at pattern
  · simp at clause

#print axioms enabled_answer_family

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
