import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternShapes
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootReadout

/-! Actual scoped matcher receipts for generated pattern rules reflect to
successful source matches and the exact source environment extension.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem pattern_root_readout {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pattern : OCaml.MatchPattern}
    {bound : List TypeExpr} {type : TypeExpr} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored ∈ patternRules index pattern)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) row.authored.left = source ∧
      applyBindings (ordinary captured) row.authored.right = target := by
  obtain ⟨inputShape, outputShape, premiseFree⟩ := pattern_rule_shapes pattern index row.authored authored
  exact plan_vector_rootFiring_readout position zero inputShape
    (GeneralRuleBindingInference.vector_binderFree outputShape) premiseFree firing

theorem match_one_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pattern : OCaml.MatchPattern}
    {actual : OCaml.Value} {body : OCaml.Code} {capturedEnvironment : OCaml.Environment}
    {continuation target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules index pattern)[0]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value actual, code body, environment capturedEnvironment, continuation])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ boundValues,
      OCaml.matchPattern pattern actual = some boundValues ∧
      target = node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment boundValues), continuation] := by
  have member : row.authored ∈ patternRules index pattern := by
    rw [authored]
    exact List.getElem_mem _
  obtain ⟨sameCaptures, emptyHistory, input, output⟩ := pattern_root_readout position member zero firing
  rw [authored] at input output
  obtain ⟨boundValues, matched, result⟩ := match_one_rule_readback pattern index actual body capturedEnvironment
    continuation (ordinary captured) input
  exact ⟨sameCaptures, emptyHistory, boundValues, matched, output.symm.trans result⟩

theorem try_clause_firing_source {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {pattern : OCaml.MatchPattern}
    {actual : OCaml.Value} {body : OCaml.Code} {later : Pattern} {capturedEnvironment : OCaml.Environment}
    {continuation target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : row.authored = (patternRules index pattern)[1]'(by simp [patternRules]))
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value actual, code body, later, environment capturedEnvironment, continuation])
      ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧ ∃ boundValues,
      OCaml.matchPattern pattern actual = some boundValues ∧
      target = node "MlEvaluate" [code body, environment (OCaml.extend capturedEnvironment boundValues), continuation] := by
  have member : row.authored ∈ patternRules index pattern := by
    rw [authored]
    exact List.getElem_mem _
  obtain ⟨sameCaptures, emptyHistory, input, output⟩ := pattern_root_readout position member zero firing
  rw [authored] at input output
  obtain ⟨boundValues, matched, result⟩ := try_clause_rule_readback pattern index actual body later capturedEnvironment
    continuation (ordinary captured) input
  exact ⟨sameCaptures, emptyHistory, boundValues, matched, output.symm.trans result⟩

#print axioms match_one_firing_source
#print axioms try_clause_firing_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
