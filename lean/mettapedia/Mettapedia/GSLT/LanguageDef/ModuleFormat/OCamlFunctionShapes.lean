import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionReadback
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternShapes

/-! Generated lambda and recursive dispatch rows fit the shared
constructor/vector root fragment, with no premises or hidden binders.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem node_vector_all (label : String) (arguments : List Pattern)
    (children : List.Forall VectorFirstOrder arguments) : VectorFirstOrder (node label arguments) :=
  node_vector label arguments (fun item member => List.forall_iff_forall_mem.mp children item member)

theorem vector_list_nil : List.Forall VectorFirstOrder [] := by simp
theorem vector_list_cons {head : Pattern} {rest : List Pattern} (first : VectorFirstOrder head)
    (tail : List.Forall VectorFirstOrder rest) : List.Forall VectorFirstOrder (head :: rest) := by
  rw [List.forall_iff_forall_mem] at tail ⊢
  intro item member
  rcases List.mem_cons.mp member with rfl | later
  · exact first
  · exact tail item later

theorem pattern_reference_vector {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {patternCode : Pattern}
    (resolved : patternReference? pool parameter = some patternCode) : VectorFirstOrder patternCode := by
  unfold patternReference? at resolved
  obtain ⟨index, _, same⟩ := Option.map_eq_some_iff.mp resolved
  cases same
  apply node_vector_all
  exact vector_list_cons (digits_vector index) vector_list_nil

theorem recursive_environment_vector (group : OCaml.Code) (definitions : List OCaml.Code) (captured : Pattern)
    (tail : VectorFirstOrder captured) : VectorFirstOrder (recursiveEnvironment group definitions captured) := by
  unfold recursiveEnvironment
  apply extend_vector _ _ _ tail
  intro item member
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
  apply node_vector_all
  exact vector_list_cons (node_vector_all _ _ (vector_list_cons (code_vector group) (vector_list_cons (code_vector slot) vector_list_nil))) (vector_list_cons tail vector_list_nil)

theorem recursive_row_shapes (group slot body : OCaml.Code) {parameter : OCaml.MatchPattern}
    {pool : List OCaml.MatchPattern} {patternCode : Pattern} (definitions : List OCaml.Code)
    (resolved : patternReference? pool parameter = some patternCode) :
    VectorFirstOrder (recursiveRow group slot body patternCode definitions).left ∧
      VectorFirstOrder (recursiveRow group slot body patternCode definitions).right ∧
      (recursiveRow group slot body patternCode definitions).premises = [] := by
  refine ⟨?_, ?_, rfl⟩
  · apply node_vector_all
    exact vector_list_cons
      (node_vector_all _ _ (vector_list_cons
        (node_vector_all _ _ (vector_list_cons (code_vector group) (vector_list_cons (code_vector slot) vector_list_nil)))
        (vector_list_cons (.metavariable _) vector_list_nil)))
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))
  · apply node_vector_all
    exact vector_list_cons (pattern_reference_vector resolved) (vector_list_cons (.metavariable _) (vector_list_cons (code_vector body)
      (vector_list_cons (recursive_environment_vector group definitions _ (.metavariable _)) (vector_list_cons (.metavariable _) vector_list_nil))))

theorem function_row_shapes (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (compiled : functionRules? program pool reference instruction = some rows) (member : row ∈ rows) :
    VectorFirstOrder row.left ∧ VectorFirstOrder row.right ∧ row.premises = [] := by
  cases instruction with
  | lambda parameter body =>
      cases resolved : patternReference? pool parameter with
      | none => simp [functionRules?, resolved] at compiled
      | some patternCode =>
          rw [function_lambda_rows program reference body resolved] at compiled
          cases Option.some.inj compiled
          have same := List.mem_singleton.mp member
          subst row
          refine ⟨?_, ?_, rfl⟩
          · apply node_vector_all
            exact vector_list_cons (node_vector_all _ _ (vector_list_cons
              (node_vector_all _ _ (vector_list_cons (code_vector reference) vector_list_nil)) (vector_list_cons (.metavariable _) vector_list_nil)))
              (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))
          · apply node_vector_all
            exact vector_list_cons (pattern_reference_vector resolved) (vector_list_cons (.metavariable _) (vector_list_cons (code_vector body)
              (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil))))
  | letRecursive definitions body =>
      obtain ⟨slot, target, parameter, functionBody, patternCode, _, _, resolved, same⟩ :=
        recursive_rule_origin program pool reference body definitions rows row compiled member
      rw [same]
      exact recursive_row_shapes reference slot functionBody definitions resolved
  | _ =>
      simp only [functionRules?] at compiled
      cases Option.some.inj compiled
      cases member

#print axioms function_row_shapes

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
