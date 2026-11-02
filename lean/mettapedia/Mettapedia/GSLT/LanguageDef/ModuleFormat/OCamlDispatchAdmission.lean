import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralBinding
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlContinuationInference
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRuleAdmission

/-! Source dispatch families satisfy selected-rule admission in every
snapshot with the authored O0 grammar and sorts. Provider-row validity and
whole-program assembly remain separate snapshot obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar GeneralFirstOrderProjection GeneralExecutionAdmission

theorem literal_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (name : String)
    (reference : Nat) (datum : OCaml.Literal) :
    let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlReturn" [literal datum, hole "continuation"])
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨literalInference.spec, .inferredGrammar literalInference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply vector_rule_ready snapshot index _ _ rfl
  · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
  · exact node_vector_all _ _ (vector_list_cons (literal_vector datum) (vector_list_cons (.metavariable _) vector_list_nil))
  · rfl
  · intro captured member
    simp only [rule, node_freeNames, literal_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact Or.inr member
  · exact literal_binding snapshot.language terms types name reference datum

theorem continuation_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (name label : String)
    (allowed : singlePayloadFrame label) (reference target : Nat) (payload : Pattern)
    (shape : VectorFirstOrder payload) (closed : payload.freeFvarNames = []) :
    let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlEvaluate" [code target, hole "environment", node label [payload, hole "environment", hole "continuation"]])
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨continuationInference.spec, .inferredGrammar continuationInference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply vector_rule_ready snapshot index _ _ rfl
  · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
  · exact node_vector_all _ _ (vector_list_cons (code_vector target) (vector_list_cons (.metavariable _)
      (vector_list_cons (node_vector_all _ _ (vector_list_cons shape
        (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))) vector_list_nil)))
  · rfl
  · intro captured member
    simp only [rule, node_freeNames, code_freeNames, hole_freeNames, closed, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at member ⊢
    tauto
  · rw [GeneralRuleBindingInference.compile?_transport terms types]
    apply GeneralRuleBindingInference.compile_empty_context _ _ rfl rfl
    · simp [rule, node_freeNames, code_freeNames, hole_freeNames]
    · exact continuation_infer label allowed name reference target payload shape closed

#print axioms literal_rule_ready
#print axioms continuation_rule_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
