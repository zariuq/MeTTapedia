import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRequestTyping

/-! Administrative build requests retain the source build kind, ordered
values and continuation in the authored machine vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem build_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (kind : OCaml.Build) (items : List OCaml.Value) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlBuildConfig" [build kind, valueList items, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (build_vector kind) (vector_list_cons (valueList_vector items)
      (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil)))
  · exact nonbare_constructor_typed terms
      [("kind", .base "MlBuild"), ("values", .base "MlValues"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons (build_typed language terms free [] kind)
        (.cons (valueList_typed language terms free [] items)
          (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil)))

theorem build_request_closed (kind : OCaml.Build) (items : List OCaml.Value) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (resolved : continuation? pool rest = some encodedRest) :
    (node "MlBuildConfig" [build kind, valueList items, encodedRest]).freeFvarNames = [] := by
  have typed := build_request_open baseLanguage rfl FreeTypeContext.empty kind items pool rest encodedRest resolved
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := typed.1.freeType_of_mem_freeFvarNames_of_isObjectPattern typed.2.2.1 present
  cases impossible

#print axioms build_request_open
#print axioms build_request_closed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
