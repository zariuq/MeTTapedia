import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildRequestTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRowTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRequest

/-! Administrative primitive request and answer configurations retain the
source operator, ordered arguments, result and complete continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem primitive_returned_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (result : OCaml.Result) (pool : List OCaml.MatchPattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlPrimitiveReturned" [primitiveResult result, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (primitiveResult_vector result)
      (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil))
  · exact nonbare_constructor_typed terms [("result", .base "MlPrimitiveResult"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons (primitiveResult_typed language terms free [] result)
        (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil))

#print axioms primitive_returned_open

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
