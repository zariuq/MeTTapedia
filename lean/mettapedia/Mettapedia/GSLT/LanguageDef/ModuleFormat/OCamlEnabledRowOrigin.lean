import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowOrigin
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRuleConstructors
import Mettapedia.OSLF.MeTTaIL.GeneralRootConstructor

/-! Every actual enabled prepared row has a compatible authored source
origin. Constructor matching excludes unrelated generated families, and
kernel candidates retain their actual declaration positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem selected_prepared_authored_member (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (position : (epochPlan prepared table).rules[ordinal]? = some row) : row.authored ∈ prepared.compiled.rewrites := by
  obtain ⟨source, index, member, _, compiled⟩ := GeneralExecutionAdmission.compiled_rule_origin (List.mem_of_getElem? position)
  have same := (GeneralExecutionAdmission.rulePlan_readout compiled).2.1
  rw [same]
  exact List.fst_mem_of_mem_zipIdx member

theorem enabled_prepared_row_origin (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {ordinal : Nat} {row : GeneralExecutionAdmission.RulePlan}
    (label : String) (inputs : List Pattern) {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} (built : prepare program = .ok prepared)
    (position : (epochPlan prepared table).rules[ordinal]? = some row)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (epochPlan prepared table)) [] (.base "MlConfig")
      (node label inputs) ordinal trace captured completed history target) :
    (∃ index, baseLanguage.rewrites[index]? = some row.authored ∧ index ∈ kernelCandidates label) ∨
    (label = "MlEvaluate" ∧ ∃ reference instruction, program.instruction? reference = some instruction ∧
      compileInstruction? (patterns program) reference instruction = some row.authored) ∨
    (label = "MlApply" ∧ ∃ reference instruction rows, program.instruction? reference = some instruction ∧
      functionRules? program (patterns program) reference instruction = some rows ∧ row.authored ∈ rows) ∨
    (label = "MlMatchOne" ∧ ∃ index parameter, (patterns program)[index]? = some parameter ∧
      row.authored = (patternRules index parameter)[0]'(by simp [patternRules])) ∨
    (label = "MlTryClause" ∧ ∃ index parameter, (patterns program)[index]? = some parameter ∧
      row.authored = (patternRules index parameter)[1]'(by simp [patternRules])) := by
  have declared := GeneralPlanEnvironment.selected_rule (epochPlan prepared table) position
  have member := selected_prepared_authored_member prepared table position
  rcases prepared_row_origin program prepared row.authored built member with
    kernel | ⟨reference, instruction, sourceAt, formed⟩ | ⟨reference, instruction, rows, sourceAt, formed, member⟩ |
      ⟨index, parameter, indexed, member⟩
  · have compatible := GeneralRuleMatchingHeads.rootFiring_potentialChild declared firing
    have authoredCompatible : GeneralPremise.potentialChild (node label inputs) row.authored = true := compatible
    exact .inl (kernel_candidate_origin label inputs row.authored kernel authoredCompatible)
  · obtain ⟨capturedEnvironment, head⟩ := instruction_left_environment (patterns program) reference instruction row.authored formed
    have same := GeneralRuleMatchingHeads.rootFiring_constructor_eq declared head firing
    exact .inr (.inl ⟨same.symm, reference, instruction, sourceAt, formed⟩)
  · obtain ⟨arguments, head⟩ := function_row_apply_constructor program (patterns program) reference instruction rows row.authored formed member
    have same := GeneralRuleMatchingHeads.rootFiring_constructor_eq declared head firing
    exact .inr (.inr (.inl ⟨same.symm, reference, instruction, rows, sourceAt, formed, member⟩))
  · rcases pattern_row_choice index parameter row.authored member with first | second
    · obtain ⟨arguments, head⟩ : ∃ arguments, row.rule.left = node "MlMatchOne" arguments := by
        change ∃ arguments, row.authored.left = node "MlMatchOne" arguments
        rw [first]
        exact ⟨_, rfl⟩
      have same := GeneralRuleMatchingHeads.rootFiring_constructor_eq declared head firing
      exact .inr (.inr (.inr (.inl ⟨same.symm, index, parameter, indexed, first⟩)))
    · obtain ⟨arguments, head⟩ : ∃ arguments, row.rule.left = node "MlTryClause" arguments := by
        change ∃ arguments, row.authored.left = node "MlTryClause" arguments
        rw [second]
        exact ⟨_, rfl⟩
      have same := GeneralRuleMatchingHeads.rootFiring_constructor_eq declared head firing
      exact .inr (.inr (.inr (.inr ⟨same.symm, index, parameter, indexed, second⟩)))

#print axioms selected_prepared_authored_member
#print axioms enabled_prepared_row_origin

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
