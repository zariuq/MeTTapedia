import Mettapedia.OSLF.MeTTaIL.GeneralVectorInferenceCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInspectionCompletion
import Mettapedia.OSLF.MeTTaIL.GeneralVectorRuleAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralEmptyContextInference

/-! Sorted constructor/vector schemas derive actual omitted-binding and
selected-rule admission. The source typing context is a proof witness;
the original grammar inference and admission algorithms remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem typed_vector_inference (language : LanguageDef) (rule : RewriteRule)
    (free : FreeTypeContext) (expected : TypeExpr)
    (labels : (language.terms.map GrammarRule.label).Nodup) (choices : CollectionChoiceDeterministic language)
    (empty : rule.typeContext = []) (premiseFree : rule.premises = [])
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (leftTyped : HasType language free [] rule.left expected) (rightTyped : HasType language free [] rule.right expected)
    (head : headType? language [] [] rule.left = some expected) :
    ∃ result, infer? language rule = some result := by
  obtain ⟨leftRows, leftRead, leftTypes⟩ := inspect_vector_complete labels choices leftShape leftTyped .left
  obtain ⟨rightRows, rightRead, rightTypes⟩ := inspect_vector_complete labels choices rightShape rightTyped .right
  apply vector_inference_complete language rule expected leftRows rightRows
    (fun name => (free name).getD expected) empty premiseFree leftShape rightShape
    (by simpa only [empty] using head) (by simpa only [empty] using leftRead) (by simpa only [empty] using rightRead)
  intro row member
  rcases List.mem_append.mp member with first | last
  · simp only [leftTypes row first, Option.getD_some]
  · simp only [rightTypes row last, Option.getD_some]

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

namespace Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

open Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem typed_vector_rule_ready (snapshot : Snapshot) (index : Nat) (rule : RewriteRule)
    (free : FreeTypeContext) (expected : TypeExpr)
    (labels : (snapshot.language.terms.map GrammarRule.label).Nodup)
    (choices : CollectionChoiceDeterministic snapshot.language)
    (omitted : rule.bindings = none) (empty : rule.typeContext = []) (premiseFree : rule.premises = [])
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (leftTyped : HasType snapshot.language free [] rule.left expected)
    (rightTyped : HasType snapshot.language free [] rule.right expected)
    (head : GeneralRuleBindingGrammar.headType? snapshot.language [] [] rule.left = some expected)
    (captures : rule.left.freeFvarNames ≠ [])
    (bound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames) :
    ∃ binding, rulePlan? snapshot index rule = some ⟨index, rule, binding⟩ ∧ ruleObligations snapshot index rule = [] := by
  obtain ⟨inferred, read⟩ := GeneralRuleBindingGrammar.typed_vector_inference snapshot.language rule free expected
    labels choices empty premiseFree leftShape rightShape leftTyped rightTyped head
  let binding : GeneralRuleBindingInference.BindingPlan := ⟨inferred.spec, .inferredGrammar inferred.extraTypes⟩
  refine ⟨binding, ?_⟩
  apply vector_rule_ready snapshot index rule binding omitted leftShape rightShape premiseFree bound
  exact GeneralRuleBindingInference.compile_empty_context snapshot.language rule omitted empty captures inferred read

#print axioms GeneralRuleBindingGrammar.typed_vector_inference
#print axioms typed_vector_rule_ready

end Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
