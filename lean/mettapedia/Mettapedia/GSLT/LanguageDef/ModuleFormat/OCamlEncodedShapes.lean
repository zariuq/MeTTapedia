import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionShapes

/-! Encoded source states contain no pending substitutions, open collection
rests or runtime binders. Their ordinary constructor/vector shape supplies
the object and canonical-metadata evidence used by shared root matching.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem value_vector (actual : OCaml.Value) : VectorFirstOrder (value actual) := by
  refine OCaml.Value.rec
    (motive_1 := fun actual => VectorFirstOrder (value actual))
    (motive_2 := fun actuals => VectorFirstOrder (valueList actuals) ∧ VectorFirstOrder (environment actuals))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ actual
  · exact literal_vector
  · intro fields ih
    exact node_vector_all _ _ (vector_list_cons ih.1 vector_list_nil)
  · intro head tail headShape tailShape
    exact node_vector_all _ _ (vector_list_cons headShape (vector_list_cons tailShape vector_list_nil))
  · intro typeId constructor fields ih
    exact node_vector_all _ _ (vector_list_cons (tag_vector typeId constructor) (vector_list_cons ih.1 vector_list_nil))
  · intro function captured ih
    cases function with
    | lambda reference =>
        exact node_vector_all _ _ (vector_list_cons
          (node_vector_all _ _ (vector_list_cons (code_vector reference) vector_list_nil))
          (vector_list_cons ih.2 vector_list_nil))
    | recursive group slot =>
        exact node_vector_all _ _ (vector_list_cons
          (node_vector_all _ _ (vector_list_cons (code_vector group) (vector_list_cons (code_vector slot) vector_list_nil)))
          (vector_list_cons ih.2 vector_list_nil))
  · exact ⟨.constructor _ [] (by simp), .constructor _ [] (by simp)⟩
  · intro head tail headShape tailShapes
    exact ⟨node_vector_all _ _ (vector_list_cons headShape (vector_list_cons tailShapes.1 vector_list_nil)),
      node_vector_all _ _ (vector_list_cons headShape (vector_list_cons tailShapes.2 vector_list_nil))⟩

theorem valueList_vector (items : List OCaml.Value) : VectorFirstOrder (valueList items) := by
  rw [valueList_as_values]
  apply linked_vector
  intro item member
  obtain ⟨actual, _, rfl⟩ := List.mem_map.mp member
  exact value_vector actual

theorem environment_vector (items : List OCaml.Value) : VectorFirstOrder (environment items) := by
  rw [environment_as_linked]
  apply linked_vector
  intro item member
  obtain ⟨actual, _, rfl⟩ := List.mem_map.mp member
  exact value_vector actual

theorem codes_vector (references : List OCaml.Code) : VectorFirstOrder (codes (references.map code)) := by
  apply linked_vector
  intro item member
  obtain ⟨reference, _, rfl⟩ := List.mem_map.mp member
  exact code_vector reference

theorem primitive_vector (operator : OCaml.Primitive) : VectorFirstOrder (primitive operator) := by
  cases operator <;> exact .constructor _ [] (by simp)

theorem fault_vector (error : OCaml.Fault) : VectorFirstOrder (fault error) := by
  cases error <;> exact .constructor _ [] (by simp)

theorem build_vector (kind : OCaml.Build) : VectorFirstOrder (build kind) := by
  cases kind with
  | tuple => exact .constructor _ [] (by simp)
  | variant typeId constructor => exact node_vector_all _ _ (vector_list_cons (tag_vector typeId constructor) vector_list_nil)
  | primitive operator => exact node_vector_all _ _ (vector_list_cons (primitive_vector operator) vector_list_nil)

theorem clauseList?_vector (pool : List OCaml.MatchPattern) (clauses : List OCaml.Clause)
    (encoded : Pattern) (found : clauseList? pool clauses = some encoded) : VectorFirstOrder encoded := by
  induction clauses generalizing encoded with
  | nil =>
      rw [clauseList?_nil] at found
      cases Option.some.inj found
      exact .constructor _ [] (by simp)
  | cons first rest ih =>
      rw [clauseList?_cons] at found
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨parameter, referenced, later, remaining, rfl⟩ := found
      exact node_vector_all _ _ (vector_list_cons (pattern_reference_vector referenced)
        (vector_list_cons (code_vector first.body) (vector_list_cons (ih later remaining) vector_list_nil)))

theorem frame?_vector (pool : List OCaml.MatchPattern) (frame : OCaml.Frame) (rest encoded : Pattern)
    (tailShape : VectorFirstOrder rest) (found : frame? pool frame rest = some encoded) : VectorFirstOrder encoded := by
  cases frame with
  | argument function captured =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (code_vector function)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil)))
  | function argument =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (value_vector argument) (vector_list_cons tailShape vector_list_nil))
  | letValue parameter body captured =>
      simp only [frame?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨patternCode, referenced, rfl⟩ := found
      exact node_vector_all _ _ (vector_list_cons (pattern_reference_vector referenced) (vector_list_cons (code_vector body)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil))))
  | branch yes no captured =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (code_vector yes) (vector_list_cons (code_vector no)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil))))
  | andThen right captured =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (code_vector right)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil)))
  | orElse right captured =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (code_vector right)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil)))
  | booleanResult =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons tailShape vector_list_nil)
  | consTail head captured =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (code_vector head)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil)))
  | consHead tail =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (value_vector tail) (vector_list_cons tailShape vector_list_nil))
  | gather kind remaining captured suffix =>
      cases Option.some.inj found
      exact node_vector_all _ _ (vector_list_cons (build_vector kind) (vector_list_cons (codes_vector remaining)
        (vector_list_cons (environment_vector captured) (vector_list_cons (valueList_vector suffix)
          (vector_list_cons tailShape vector_list_nil)))))
  | matchValue clauses captured =>
      simp only [frame?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨clauseCode, referenced, rfl⟩ := found
      exact node_vector_all _ _ (vector_list_cons (clauseList?_vector pool clauses clauseCode referenced)
        (vector_list_cons (environment_vector captured) (vector_list_cons tailShape vector_list_nil)))

theorem continuation?_vector (pool : List OCaml.MatchPattern) (rest : OCaml.Continuation)
    (encoded : Pattern) (found : continuation? pool rest = some encoded) : VectorFirstOrder encoded := by
  induction rest generalizing encoded with
  | nil => cases Option.some.inj found; exact .constructor _ [] (by simp)
  | cons frame rest ih =>
      simp only [continuation?, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨tail, resolved, result⟩ := found
      exact frame?_vector pool frame tail encoded (ih tail resolved) result

theorem state?_vector (pool : List OCaml.MatchPattern) (state : OCaml.MachineState)
    (encoded : Pattern) (found : state? pool state = some encoded) : VectorFirstOrder encoded := by
  cases state with
  | evaluate reference captured rest =>
      simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨tail, resolved, rfl⟩ := found
      exact node_vector_all _ _ (vector_list_cons (code_vector reference) (vector_list_cons (environment_vector captured)
        (vector_list_cons (continuation?_vector pool rest tail resolved) vector_list_nil)))
  | returned actual rest =>
      simp only [state?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at found
      obtain ⟨tail, resolved, rfl⟩ := found
      exact node_vector_all _ _ (vector_list_cons (value_vector actual)
        (vector_list_cons (continuation?_vector pool rest tail resolved) vector_list_nil))
  | halted result =>
      cases result with
      | ok actual => cases Option.some.inj found; exact node_vector_all _ _ (vector_list_cons (value_vector actual) vector_list_nil)
      | error error => cases Option.some.inj found; exact node_vector_all _ _ (vector_list_cons (fault_vector error) vector_list_nil)

theorem state?_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (pool : List OCaml.MatchPattern)
    (state : OCaml.MachineState) (encoded : Pattern) (found : state? pool state = some encoded) :
    OpenPatternWellSorted language free bound (.base "MlConfig") encoded :=
  typed_node_open (state?_vector pool state encoded found) (state?_typed language terms free bound pool state encoded found)

#print axioms state?_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
