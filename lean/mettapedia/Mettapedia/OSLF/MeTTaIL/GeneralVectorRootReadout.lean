import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderRootComparison
import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchReadout
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPlanEnvironment

/-! Actual scoped root receipts for premise-free constructor/vector rules
read back to one ordinary substitution of both authored rule sides. The
captured assignment and empty premise history are retained explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match

theorem vector_rootFiring_readout {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {source target : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : binderFree rule.right = true)
    (premiseFree : rule.premises = [])
    (firing : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) rule.left = source ∧
      applyBindings (ordinary captured) rule.right = target := by
  cases firing with
  | fire actualDeclared actualSpecified _ _ matching typed premises reduct _ =>
    have sameRule := Option.some.inj (actualDeclared.symm.trans declared)
    subst sameRule
    have sameSpec := Option.some.inj (actualSpecified.symm.trans specified)
    subst sameSpec
    rw [premiseFree] at premises
    cases premises
    have roots := typed.rootValues zero
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact vector_matching_readout leftShape matching.matching (fun _ _ found => found) roots
    · exact binderFree_instantiation_readout rightShape roots reduct

theorem plan_vector_rootFiring_readout {plan : GeneralExecutionAdmission.Plan}
    {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (position : plan.rules[ordinal]? = some row)
    (zero : GeneralPremise.checkZeroDependencies row.binding.spec = true)
    (leftShape : VectorFirstOrder row.authored.left) (rightShape : binderFree row.authored.right = true)
    (premiseFree : row.authored.premises = [])
    (firing : GeneralPremise.RootFiring (GeneralPlanEnvironment.environment plan) bound type source ordinal
      trace captured completed history target) :
    completed = captured ∧ history = [] ∧
      applyBindings (ordinary captured) row.authored.left = source ∧
      applyBindings (ordinary captured) row.authored.right = target := by
  have read := vector_rootFiring_readout (GeneralPlanEnvironment.selected_rule plan position)
    (GeneralPlanEnvironment.selected_specification plan position) zero
    (by simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate] using leftShape)
    (by simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate] using rightShape)
    (by simpa only [GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate] using premiseFree)
    firing
  exact read

#print axioms vector_rootFiring_readout
#print axioms plan_vector_rootFiring_readout

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
