import Mettapedia.OSLF.MeTTaIL.GeneralVectorInspectionAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralInferredContext

/-! Omitted-binding inference succeeds for premise-free constructor/vector
schemas whose inspected occurrences assign each capture one result sort.
The theorem derives every specification check from the actual inspections.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax RuleBinding GeneralFirstOrderProjection

theorem vector_inference_complete (language : LanguageDef) (rule : RewriteRule)
    (expected : TypeExpr) (leftRows rightRows : List Occurrence) (typeOf : String → TypeExpr)
    (empty : rule.typeContext = []) (premiseFree : rule.premises = [])
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (head : headType? language rule.typeContext [] rule.left = some expected)
    (leftRead : inspect language rule.typeContext .left [] expected rule.left = some leftRows)
    (rightRead : inspect language rule.typeContext .right [] expected rule.right = some rightRows)
    (functional : ∀ row ∈ leftRows ++ rightRows, row.result = typeOf row.name) :
    ∃ result, infer? language rule = some result := by
  let rows := leftRows ++ rightRows
  let context := implicitTypes rule rows
  let result : Inference := ⟨context, specification context rows, rows⟩
  have unbound : ∀ row ∈ rows, row.bound = [] := by
    intro row member
    rcases List.mem_append.mp member with first | last
    · exact inspect_binderFree language rule.typeContext .left [] expected rule.left leftRows
        (GeneralRuleBindingInference.vector_binderFree leftShape) leftRead row first
    · exact inspect_binderFree language rule.typeContext .right [] expected rule.right rightRows
        (GeneralRuleBindingInference.vector_binderFree rightShape) rightRead row last
  have unique := implicitTypes_unique rule empty rows typeOf functional
  have coherent := implicitTypes_consistent rule empty rows typeOf functional unbound
  have covered : ∀ row ∈ rows, row.name ∈ context.map Prod.fst := by
    intro row present
    exact List.mem_map.mpr ⟨(row.name, row.result), implicitTypes_member rule empty rows row present, rfl⟩
  have admitted : admittedFor (elaborate rule result) result.spec = true := by
    change admittedFor {rule with typeContext := rule.typeContext ++ context} (specification context rows) = true
    rw [empty, List.nil_append]
    exact inspected_specification_admitted language rule context expected leftRows rightRows
      leftShape rightShape leftRead rightRead unique covered
  have declared : dependencySortsDeclared language result.spec = true := by
    simp [result, dependencySortsDeclared, specification, dependencyRows_zero context rows unbound]
  refine ⟨result, ?_⟩
  have headRead : headType? language [] [] rule.left = some expected := by simpa only [empty] using head
  have leftInspected : inspect language [] .left [] expected rule.left = some leftRows := by simpa only [empty] using leftRead
  have rightInspected : inspect language [] .right [] expected rule.right = some rightRows := by simpa only [empty] using rightRead
  simp only [infer?, empty, headRead, leftInspected, rightInspected, premiseFree, List.zipIdx_nil, List.mapM_nil,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.flatten_nil, List.append_nil, List.nil_append]
  change (if consistent context rows && admittedFor (elaborate rule result) result.spec &&
    dependencySortsDeclared language result.spec then some result else none) = some result
  rw [coherent, admitted, declared]
  rfl

#print axioms vector_inference_complete

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar
