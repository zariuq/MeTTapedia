import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSelectionRequestTyping

/-! Request typing depends on the encoded pattern index, not on the first
occurrence returned by a source-pattern lookup. Source authorization keeps
its separate pool-membership and failed-match evidence. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem index_shape (index : Nat) : VectorFirstOrder (patternId index) :=
  node_vector_all _ _ (vector_list_cons (digits_vector index) vector_list_nil)

theorem match_index_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (pool : List OCaml.MatchPattern) (index : Nat) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (index_shape index) (vector_list_cons (value_vector argument)
      (vector_list_cons (code_vector body) (vector_list_cons (environment_vector captured)
        (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil)))))
  · exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternId_typed language terms free [] index) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] body) (.cons (environment_typed language terms free [] captured)
          (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil)))))

theorem clause_index_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (pool : List OCaml.MatchPattern) (index : Nat) (argument : OCaml.Value) (body : OCaml.Code)
    (clauses : List OCaml.Clause) (later : Pattern) (clauseResolved : clauseList? pool clauses = some later)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (index_shape index) (vector_list_cons (value_vector argument)
      (vector_list_cons (code_vector body) (vector_list_cons (clauseList?_vector pool clauses later clauseResolved)
        (vector_list_cons (environment_vector captured)
          (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil))))))
  · exact nonbare_constructor_typed terms
      [("pattern", .base "MlPattern"), ("value", .base "MlValue"), ("body", .base "MlCode"), ("later", .base "MlClauses"),
        ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternId_typed language terms free [] index) (.cons (value_typed language terms free [] argument)
        (.cons (code_typed language terms free [] body) (.cons (clauseList?_typed language terms free [] pool clauses later clauseResolved)
          (.cons (environment_typed language terms free [] captured)
            (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil))))))

#print axioms match_index_request_open
#print axioms clause_index_request_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
