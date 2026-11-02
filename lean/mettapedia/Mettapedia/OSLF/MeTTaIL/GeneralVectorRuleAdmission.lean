import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralInferredBindingCanonical
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Premise-free constructor/vector rules with inferred bindings and no
new output captures satisfy the actual selected-rule admission checks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax GeneralFirstOrderProjection GeneralRuleBindingInference

theorem vector_rule_ready (snapshot : Snapshot) (index : Nat) (rule : RewriteRule) (binding : BindingPlan)
    (omitted : rule.bindings = none) (left : VectorFirstOrder rule.left) (right : VectorFirstOrder rule.right)
    (premises : rule.premises = [])
    (bound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (compiled : GeneralRuleBindingInference.compile? snapshot.language rule = some binding) :
    rulePlan? snapshot index rule = some ⟨index, rule, binding⟩ ∧ ruleObligations snapshot index rule = [] := by
  have canonical : GeneralEquationCanonicalTemplates.checkRule rule = true := by
    simp only [GeneralEquationCanonicalTemplates.checkRule, vector_canonical left, vector_canonical right,
      premises, List.all_nil]
    rfl
  have spine := omitted_binding_canonical snapshot.language rule binding omitted compiled
  have flow : GeneralPremise.rulePremisesAdmitted snapshot.language snapshot.provider (binding.elaborate rule) binding.spec = true := by
    simp only [GeneralPremise.rulePremisesAdmitted, BindingPlan.elaborate, premises,
      GeneralPremise.premisesFlow, GeneralPremise.namesAvailable, Bool.true_and]
    apply List.all_eq_true.mpr
    intro name member
    exact List.contains_iff_mem.mpr (bound name member)
  constructor
  · simp only [rulePlan?, compiled, Option.bind_eq_bind, Option.bind_some, flow, canonical, spine,
      Bool.and_self, if_true]
  · simp only [ruleObligations, compiled, canonical, spine, Bool.and_self, if_true, flow]

#print axioms vector_rule_ready

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
