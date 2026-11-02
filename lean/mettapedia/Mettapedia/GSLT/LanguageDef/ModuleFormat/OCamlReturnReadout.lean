import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInstantiation
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootReadout
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstanceAgreement

/-! The actual shared root-firing witnesses for O0 structural return rows
read back to their authored transitions. Selected plan ordinals and original
module row positions are distinct evidence, retained throughout the proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

private theorem firstOrder_vector {pattern : Pattern} (shape : FirstOrder pattern) : VectorFirstOrder pattern := by
  induction shape with
  | metavariable name => exact .metavariable name
  | constructor label arguments _ children => exact .constructor label arguments children

private theorem base_shapes : baseLanguage.rewrites.all (fun row =>
    checkFirstOrder row.left && binderFree row.right) = true := by decide +kernel

private theorem base_output_shapes : baseLanguage.rewrites.all (fun row => checkFirstOrder row.right) = true :=
  by decide +kernel

private theorem base_bounds : baseLanguage.rewrites.all (fun row =>
    !row.premises.isEmpty || row.right.freeFvarNames.all row.left.freeFvarNames.contains) = true := by cbv

theorem pure_base_root_readout {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (premiseFree : row.authored.premises = [])
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) row.authored.left = source ∧
      applyBindings (ordinary captured) row.authored.right = target := by
  have shapes := List.all_eq_true.mp base_shapes row.authored (List.mem_of_getElem? authored)
  have both := Bool.and_eq_true_iff.mp shapes
  exact plan_vector_rootFiring_readout position zero (firstOrder_vector (checkFirstOrder_sound both.1))
    both.2 premiseFree firing

theorem pure_base_root_target {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal index : Nat} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice} {bindings : Bindings}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[index]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (premiseFree : row.authored.premises = [])
    (input : applyBindings bindings row.authored.left = source)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = applyBindings bindings row.authored.right := by
  have member := List.mem_of_getElem? authored
  have shapes := Bool.and_eq_true_iff.mp (List.all_eq_true.mp base_shapes row.authored member)
  have leftShape := firstOrder_vector (checkFirstOrder_sound shapes.1)
  have rightShape := firstOrder_vector (checkFirstOrder_sound (List.all_eq_true.mp base_output_shapes row.authored member))
  have bounded := List.all_eq_true.mp base_bounds row.authored member
  simp only [premiseFree, List.isEmpty_nil, Bool.not_true, Bool.false_or] at bounded
  have rightBound : ∀ name ∈ row.authored.right.freeFvarNames, name ∈ row.authored.left.freeFvarNames := by
    intro name present
    exact List.contains_iff_mem.mp (List.all_eq_true.mp bounded name present)
  obtain ⟨sameCaptures, emptyHistory, sourceRead, targetRead⟩ := pure_base_root_readout position authored zero premiseFree firing
  exact ⟨sameCaptures, emptyHistory, targetRead.symm.trans
    (vector_rule_output_unique leftShape rightShape rightBound (ordinary captured) bindings (sourceRead.trans input.symm))⟩

private theorem row_field {α : Type} (field : RewriteRule → α) {index : Nat} {row : RewriteRule}
    {expected : α} (authored : baseLanguage.rewrites[index]? = some row)
    (computed : (baseLanguage.rewrites[index]?).map field = some expected) : field row = expected := by
  rw [authored] at computed
  exact Option.some.inj computed

theorem return_argument_firing {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {bound : List TypeExpr}
    {argument function capturedEnvironment rest target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (authored : baseLanguage.rewrites[1]? = some row.authored)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound (.base "MlConfig")
      (node "MlReturn" [argument, node "MlKArgument" [function, capturedEnvironment, rest]]) ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      target = node "MlEvaluate" [function, capturedEnvironment, node "MlKFunction" [argument, rest]] := by
  have left : row.authored.left = node "MlReturn" [.fvar "argument",
      node "MlKArgument" [.fvar "function", .fvar "environment", .fvar "rest"]] :=
    row_field RewriteRule.left authored (by decide +kernel)
  have right : row.authored.right = node "MlEvaluate" [.fvar "function", .fvar "environment",
      node "MlKFunction" [.fvar "argument", .fvar "rest"]] :=
    row_field RewriteRule.right authored (by decide +kernel)
  have premiseFree : row.authored.premises = [] := row_field RewriteRule.premises authored (by decide +kernel)
  obtain ⟨sameCaptures, emptyHistory, input, output⟩ := pure_base_root_readout position authored zero premiseFree firing
  rw [left] at input
  simp only [apply_node, List.map_cons, List.map_nil] at input
  simp only [node, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at input
  obtain ⟨argumentSame, functionSame, environmentSame, restSame⟩ := input
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  rw [right] at output
  simpa only [apply_node, List.map_cons, List.map_nil, argumentSame, functionSame,
    environmentSame, restSame] using output.symm

#print axioms pure_base_root_readout
#print axioms pure_base_root_target
#print axioms return_argument_firing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
