import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFreeNames
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionShapes
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammarTransport

/-! Generated dispatch rows expose exactly their runtime capture names.
Every output capture is supplied by the input, and their root sort is read
from the actual constructor vocabulary.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem pattern_reference_freeNames {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {encoded : Pattern}
    (found : patternReference? pool parameter = some encoded) : encoded.freeFvarNames = [] := by
  unfold patternReference? at found
  obtain ⟨index, _, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  exact patternId_freeNames index

theorem recursive_row_binding_fields (group slot body : OCaml.Code) (patternCode : Pattern) (definitions : List OCaml.Code)
    (closed : patternCode.freeFvarNames = []) :
    (recursiveRow group slot body patternCode definitions).bindings = none ∧
      (recursiveRow group slot body patternCode definitions).typeContext = [] ∧
      (recursiveRow group slot body patternCode definitions).left.freeFvarNames =
        ["ml:environment", "ml:argument", "ml:continuation"] ∧
      ∀ name ∈ (recursiveRow group slot body patternCode definitions).right.freeFvarNames,
        name ∈ (recursiveRow group slot body patternCode definitions).left.freeFvarNames := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [recursiveRow, rule, node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.singleton_append]
    rfl
  · intro name member
    simpa only [recursiveRow, rule, node_freeNames, code_freeNames, hole_freeNames, closed,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, recursiveEnvironment_freeNames, or_false, or_left_comm] using member

theorem function_binding_fields (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference : OCaml.Code) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (compiled : functionRules? program pool reference instruction = some rows) (member : row ∈ rows) :
    row.bindings = none ∧ row.typeContext = [] ∧
      row.left.freeFvarNames = ["ml:environment", "ml:argument", "ml:continuation"] ∧
      (∀ name ∈ row.right.freeFvarNames, name ∈ row.left.freeFvarNames) ∧
      GeneralRuleBindingGrammar.headType? baseLanguage [] [] row.left = some (.base "MlConfig") := by
  cases instruction with
  | lambda parameter body =>
      cases resolved : patternReference? pool parameter with
      | none => simp [functionRules?, resolved] at compiled
      | some patternCode =>
          rw [function_lambda_rows program reference body resolved] at compiled
          cases Option.some.inj compiled
          have same := List.mem_singleton.mp member
          subst row
          refine ⟨rfl, rfl, ?_, ?_, ?_⟩
          · simp only [rule, node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons, List.flatMap_nil,
              List.nil_append, List.append_nil, List.singleton_append]
            rfl
          · intro name present
            simpa only [rule, node_freeNames, code_freeNames, hole_freeNames, pattern_reference_freeNames resolved,
              List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
              List.mem_append, or_false, or_left_comm] using present
          · change GeneralRuleBindingGrammar.headType? baseLanguage [] [] (node "MlApply" _) = some (.base "MlConfig")
            simp only [node, GeneralRuleBindingGrammar.headType?]
            decide +kernel
  | letRecursive definitions body =>
      obtain ⟨slot, target, parameter, functionBody, patternCode, _, _, resolved, same⟩ :=
        recursive_rule_origin program pool reference body definitions rows row compiled member
      subst row
      obtain ⟨omitted, empty, inputNames, outputBound⟩ := recursive_row_binding_fields reference slot functionBody patternCode
        definitions (pattern_reference_freeNames resolved)
      refine ⟨omitted, empty, inputNames, outputBound, ?_⟩
      change GeneralRuleBindingGrammar.headType? baseLanguage [] [] (node "MlApply" _) = some (.base "MlConfig")
      simp only [node, GeneralRuleBindingGrammar.headType?]
      decide +kernel
  | _ =>
      simp only [functionRules?] at compiled
      cases Option.some.inj compiled
      cases member

#print axioms function_binding_fields

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
