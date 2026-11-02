import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDispatchAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlDoubleContinuationInference

/-! Two-payload branch/let continuations use the same selected-rule checks
as the single-payload dispatch families.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar GeneralFirstOrderProjection GeneralExecutionAdmission

theorem double_continuation_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (name label : String)
    (allowed : doublePayloadFrame label) (reference target : Nat) (first second : Pattern)
    (firstShape : VectorFirstOrder first) (secondShape : VectorFirstOrder second)
    (firstClosed : first.freeFvarNames = []) (secondClosed : second.freeFvarNames = []) :
    let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlEvaluate" [code target, hole "environment", node label [first, second, hole "environment", hole "continuation"]])
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨doubleContinuationInference.spec, .inferredGrammar doubleContinuationInference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply vector_rule_ready snapshot index _ _ rfl
  · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
  · exact node_vector_all _ _ (vector_list_cons (code_vector target) (vector_list_cons (.metavariable _)
      (vector_list_cons (node_vector_all _ _ (vector_list_cons firstShape (vector_list_cons secondShape
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))))) vector_list_nil)))
  · rfl
  · intro captured member
    simp only [rule, node_freeNames, code_freeNames, hole_freeNames, firstClosed, secondClosed, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at member ⊢
    tauto
  · rw [GeneralRuleBindingInference.compile?_transport terms types]
    apply GeneralRuleBindingInference.compile_empty_context _ _ rfl rfl
    · simp [rule, node_freeNames, code_freeNames, hole_freeNames]
    · exact double_continuation_infer label allowed name reference target first second firstShape secondShape firstClosed secondClosed

#print axioms double_continuation_rule_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
