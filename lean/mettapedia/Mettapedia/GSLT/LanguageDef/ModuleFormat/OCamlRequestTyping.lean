import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodedShapes

/-! Administrative call and pattern requests retain the source values,
body references, captured environments and complete continuation, all
sorted by the actual authored IR vocabulary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem apply_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (function argument : OCaml.Value) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlApply" [value function, value argument, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (value_vector function) (vector_list_cons (value_vector argument)
      (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil)))
  · exact nonbare_constructor_typed terms
      [("function", .base "MlValue"), ("argument", .base "MlValue"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons (value_typed language terms free [] function) (.cons (value_typed language terms free [] argument)
        (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil)))

theorem match_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {patternCode : Pattern}
    (referenced : patternReference? pool parameter = some patternCode) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlMatchOne" [patternCode, value argument, code body, environment captured, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (pattern_reference_vector referenced) (vector_list_cons (value_vector argument)
      (vector_list_cons (code_vector body) (vector_list_cons (environment_vector captured)
        (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil)))))
  · exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternReference?_typed language terms free [] referenced) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] body) (.cons (environment_typed language terms free [] captured)
          (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil)))))

theorem apply_request_closed (function argument : OCaml.Value) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (resolved : continuation? pool rest = some encodedRest) :
    (node "MlApply" [value function, value argument, encodedRest]).freeFvarNames = [] := by
  have typed := apply_request_open baseLanguage rfl FreeTypeContext.empty function argument pool rest encodedRest resolved
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := typed.1.freeType_of_mem_freeFvarNames_of_isObjectPattern typed.2.2.1 present
  cases impossible

theorem clause_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) {pool : List OCaml.MatchPattern} {parameter : OCaml.MatchPattern} {patternCode : Pattern}
    (referenced : patternReference? pool parameter = some patternCode) (argument : OCaml.Value) (body : OCaml.Code)
    (clauses : List OCaml.Clause) (later : Pattern) (clauseResolved : clauseList? pool clauses = some later)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlTryClause" [patternCode, value argument, code body, later, environment captured, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (pattern_reference_vector referenced) (vector_list_cons (value_vector argument)
      (vector_list_cons (code_vector body) (vector_list_cons (clauseList?_vector pool clauses later clauseResolved)
        (vector_list_cons (environment_vector captured)
          (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil))))))
  · exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"), ("later", .base "MlClauses"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternReference?_typed language terms free [] referenced) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] body) (.cons (clauseList?_typed language terms free [] pool clauses later clauseResolved)
          (.cons (environment_typed language terms free [] captured)
            (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil))))))

#print axioms apply_request_open
#print axioms match_request_open
#print axioms clause_request_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
