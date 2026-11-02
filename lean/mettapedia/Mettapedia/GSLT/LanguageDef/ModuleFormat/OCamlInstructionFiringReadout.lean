import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedRowDependencies
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDirectInstructions
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstanceAgreement
import Mettapedia.OSLF.MeTTaIL.GeneralSelectedRuleBounds

/-! Actual instruction receipts retain their source code reference and agree
with every ordinary instance having the same input. Output-name coverage is
derived from the selected compiled row rather than assumed by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding GeneralFirstOrderProjection

theorem instruction_firing_readout {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal reference : Nat}
    {pool : List OCaml.MatchPattern} {instruction : OCaml.Instruction} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (formed : compileInstruction? pool reference instruction = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      source ordinal trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) row.authored.left = source ∧
      applyBindings (ordinary captured) row.authored.right = target := by
  obtain ⟨left, right, premiseFree, _, _⟩ := instruction_shapes pool reference instruction row.authored formed
  exact plan_vector_rootFiring_readout position zero left
    (GeneralRuleBindingInference.vector_binderFree right) premiseFree firing

theorem instruction_firing_reference {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal rowReference sourceReference : Nat}
    {pool : List OCaml.MatchPattern} {instruction : OCaml.Instruction} {sourceEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (formed : compileInstruction? pool rowReference instruction = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) [] (.base "MlConfig")
      (node "MlEvaluate" [code sourceReference, sourceEnvironment, rest]) ordinal trace captured completed history target) :
    rowReference = sourceReference := by
  obtain ⟨_, _, input, _⟩ := instruction_firing_readout position formed zero firing
  obtain ⟨environmentSchema, left⟩ := instruction_left_environment pool rowReference instruction row.authored formed
  rw [left] at input
  simp only [apply_node, List.map_cons, List.map_nil, apply_code] at input
  exact code_injective (List.cons.inj (Pattern.apply.inj input).2).1

theorem instruction_firing_target {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal reference : Nat}
    {pool : List OCaml.MatchPattern} {instruction : OCaml.Instruction} {source expected target : Pattern}
    {assignment : Bindings}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (formed : compileInstruction? pool reference instruction = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (input : applyBindings assignment row.authored.left = source)
    (output : applyBindings assignment row.authored.right = expected)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
      source ordinal trace captured completed history target) : target = expected := by
  obtain ⟨left, right, premiseFree, _, _⟩ := instruction_shapes pool reference instruction row.authored formed
  obtain ⟨_, _, actualInput, actualOutput⟩ := instruction_firing_readout position formed zero firing
  have same := vector_rule_output_unique left right
    (GeneralExecutionAdmission.selected_premiseFree_bound position premiseFree)
    (ordinary captured) assignment (actualInput.trans input.symm)
  exact actualOutput.symm.trans (same.trans output)

#print axioms instruction_firing_readout
#print axioms instruction_firing_reference
#print axioms instruction_firing_target

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
