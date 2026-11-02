import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRequestTyping

/-! Ordered clause-selection configurations retain the source clause list,
scrutinee, environment and complete continuation in the authored grammar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem select_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (pool : List OCaml.MatchPattern) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (clauseResolved : clauseList? pool clauses = some encodedClauses)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (clauseList?_vector pool clauses encodedClauses clauseResolved)
      (vector_list_cons (value_vector argument) (vector_list_cons (environment_vector captured)
        (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil))))
  · exact nonbare_constructor_typed terms [("clauses", .base "MlClauses"), ("value", .base "MlValue"),
      ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (clauseList?_typed language terms free [] pool clauses encodedClauses clauseResolved)
        (.cons (value_typed language terms free [] argument) (.cons (environment_typed language terms free [] captured)
          (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil))))

theorem select_request_closed (pool : List OCaml.MatchPattern) (clauses : List OCaml.Clause) (encodedClauses : Pattern)
    (argument : OCaml.Value) (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (clauseResolved : clauseList? pool clauses = some encodedClauses)
    (resolved : continuation? pool rest = some encodedRest) :
    (node "MlSelect" [encodedClauses, value argument, environment captured, encodedRest]).freeFvarNames = [] := by
  have typed := select_request_open baseLanguage rfl FreeTypeContext.empty pool clauses encodedClauses argument captured rest encodedRest clauseResolved resolved
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := typed.1.freeType_of_mem_freeFvarNames_of_isObjectPattern typed.2.2.1 present
  cases impossible

#print axioms select_request_open
#print axioms select_request_closed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
