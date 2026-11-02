import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCallFiring

/-! The source request fixes the pattern row's pool index. Pattern identity
is recovered from the actual root receipt before looking up its source row.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding

theorem match_one_row_index {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal sourceIndex rowIndex : Nat} {parameter : OCaml.MatchPattern}
    {rest : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules rowIndex parameter)[0]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlMatchOne" (patternId sourceIndex :: rest)) ordinal trace captured completed history target) :
    rowIndex = sourceIndex := by
  have member : row.authored ∈ patternRules rowIndex parameter := by
    rw [authored]
    exact List.getElem_mem _
  obtain ⟨_, _, input, _⟩ := pattern_root_readout position member zero firing
  rw [authored] at input
  change applyBindings (GeneralFirstOrderProjection.ordinary captured)
    (node "MlMatchOne" (patternId rowIndex :: _)) = node "MlMatchOne" (patternId sourceIndex :: rest) at input
  simp only [apply_node, List.map_cons, apply_patternId] at input
  exact patternId_injective (List.cons.inj (Pattern.apply.inj input).2).1

#print axioms match_one_row_index

theorem clause_row_index {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal sourceIndex rowIndex : Nat} {parameter : OCaml.MatchPattern}
    {rest : List Pattern} {target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules rowIndex parameter)[1]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlTryClause" (patternId sourceIndex :: rest)) ordinal trace captured completed history target) :
    rowIndex = sourceIndex := by
  have member : row.authored ∈ patternRules rowIndex parameter := by
    rw [authored]
    exact List.getElem_mem _
  obtain ⟨_, _, input, _⟩ := pattern_root_readout position member zero firing
  rw [authored] at input
  change applyBindings (GeneralFirstOrderProjection.ordinary captured)
    (node "MlTryClause" (patternId rowIndex :: _)) = node "MlTryClause" (patternId sourceIndex :: rest) at input
  simp only [apply_node, List.map_cons, apply_patternId] at input
  exact patternId_injective (List.cons.inj (Pattern.apply.inj input).2).1

#print axioms clause_row_index

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
