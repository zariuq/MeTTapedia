import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlClosureInference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInferredRuleAdmission

/-! Closure-producing dispatch satisfies the real selected-rule checks
without assuming whole-program admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection GeneralExecutionAdmission

theorem closure_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (name : String) (reference : Nat) :
    let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (node "MlReturn" [node "MlClosure" [node "MlLambdaFunction" [code reference], hole "environment"], hole "continuation"])
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨closureInference.spec, .inferredGrammar closureInference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply inferred_rule_ready snapshot terms types index _ closureInference rfl rfl
  · simp [rule, node_freeNames, code_freeNames, hole_freeNames]
  · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
  · exact node_vector_all _ _ (vector_list_cons
      (node_vector_all _ _ (vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector reference) vector_list_nil))
        (vector_list_cons (.metavariable _) vector_list_nil))) (vector_list_cons (.metavariable _) vector_list_nil))
  · rfl
  · intro captured member
    simpa only [rule, node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, List.append_nil] using member
  · exact closure_infer name reference

#print axioms closure_rule_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
