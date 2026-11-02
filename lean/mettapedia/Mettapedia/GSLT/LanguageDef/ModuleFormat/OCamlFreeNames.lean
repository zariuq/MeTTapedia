import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateClosed

/-! Compact constants contain no metavariables. Wrapper/list constructors
retain exactly their children's free names, which makes generated-rule
output binding checks compositional.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_typed_closed {pattern : Pattern} {type : TypeExpr}
    (shape : GeneralFirstOrderProjection.VectorFirstOrder pattern)
    (typed : HasType baseLanguage FreeTypeContext.empty [] pattern type) : pattern.freeFvarNames = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨actualType, impossible⟩ := typed.freeType_of_mem_freeFvarNames_of_isObjectPattern
    (GeneralRuleBindingInference.vector_object shape) member
  cases impossible

@[simp] theorem code_freeNames (reference : Nat) : (code reference).freeFvarNames = [] :=
  vector_typed_closed (code_vector reference) (code_typed baseLanguage rfl FreeTypeContext.empty [] reference)

@[simp] theorem patternId_freeNames (index : Nat) : (patternId index).freeFvarNames = [] := by
  have shape : GeneralFirstOrderProjection.VectorFirstOrder (patternId index) := by
    apply node_vector_all
    exact vector_list_cons (digits_vector index) vector_list_nil
  exact vector_typed_closed shape (patternId_typed baseLanguage rfl FreeTypeContext.empty [] index)

@[simp] theorem literal_freeNames (datum : OCaml.Literal) : (literal datum).freeFvarNames = [] :=
  vector_typed_closed (literal_vector datum) (literal_typed baseLanguage rfl FreeTypeContext.empty [] datum)

@[simp] theorem tag_freeNames (typeId constructor : Nat) : (tag typeId constructor).freeFvarNames = [] :=
  vector_typed_closed (tag_vector typeId constructor) (tag_typed baseLanguage rfl FreeTypeContext.empty [] typeId constructor)

@[simp] theorem value_freeNames (actual : OCaml.Value) : (value actual).freeFvarNames = [] :=
  vector_typed_closed (value_vector actual) (value_typed baseLanguage rfl FreeTypeContext.empty [] actual)

@[simp] theorem linked_freeNames (cons nil : String) (items : List Pattern) :
    (linked cons nil items).freeFvarNames = items.flatMap Pattern.freeFvarNames := by
  induction items with
  | nil => simp only [linked, List.foldr_nil, node, Pattern.freeFvarNames, List.flatMap_nil]
  | cons first rest ih =>
      simpa only [linked, List.foldr_cons, node, Pattern.freeFvarNames, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] using congrArg (fun names => first.freeFvarNames ++ names) ih

@[simp] theorem node_freeNames (label : String) (arguments : List Pattern) :
    (node label arguments).freeFvarNames = arguments.flatMap Pattern.freeFvarNames := by simp only [node, Pattern.freeFvarNames]

@[simp] theorem hole_freeNames (label : String) : (hole label).freeFvarNames = ["ml:" ++ label] := by simp only [hole, Pattern.freeFvarNames]

theorem extend_freeNames (items : List Pattern) (captured : Pattern) (name : String) :
    name ∈ (extend items captured).freeFvarNames ↔ name ∈ captured.freeFvarNames ∨
      ∃ item ∈ items, name ∈ item.freeFvarNames := by
  induction items generalizing captured with
  | nil => simp only [extend, List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | cons first rest ih =>
      rw [extend, List.foldl_cons]
      rw [show List.foldl (fun tail head => node "MlEnvironmentCons" [head, tail])
        (node "MlEnvironmentCons" [first, captured]) rest = extend rest (node "MlEnvironmentCons" [first, captured]) from rfl, ih]
      simp only [node_freeNames, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
        List.mem_cons, exists_eq_or_imp, or_assoc, or_left_comm]

@[simp] theorem recursiveEnvironment_freeNames (group : Nat) (definitions : List OCaml.Code) (captured : Pattern)
    (name : String) : name ∈ (recursiveEnvironment group definitions captured).freeFvarNames ↔ name ∈ captured.freeFvarNames := by
  unfold recursiveEnvironment
  rw [extend_freeNames]
  constructor
  · rintro (here | ⟨item, member, inside⟩)
    · exact here
    · obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
      simpa only [node_freeNames, code_freeNames, List.flatMap_cons, List.flatMap_nil, List.nil_append,
        List.append_nil] using inside
  · exact Or.inl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
