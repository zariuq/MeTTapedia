import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochRequestChecks
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveEpoch

/-! Primitive requests built from source values and a resolved continuation
are closed, typed inputs to the existing runner in every provider epoch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem primitive_request_open (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (pool : List OCaml.MatchPattern) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (resolved : continuation? pool rest = some encodedRest) :
    OpenPatternWellSorted language free [] (.base "MlConfig")
      (node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]) := by
  apply typed_node_open
  · exact node_vector_all _ _ (vector_list_cons (primitive_vector operator)
      (vector_list_cons (valueList_vector arguments)
        (vector_list_cons (continuation?_vector pool rest encodedRest resolved) vector_list_nil)))
  · exact nonbare_constructor_typed terms
      [("operator", .base "MlPrimitive"), ("arguments", .base "MlValues"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons (primitive_typed language terms free [] operator)
        (.cons (valueList_typed language terms free [] arguments)
          (.cons (continuation?_typed language terms free [] pool rest encodedRest resolved) .nil)))

theorem epoch_primitive_request_checked (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (rest : OCaml.Continuation) (encodedRest : Pattern) (built : prepare program = .ok prepared)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlPrimitiveRequest" [primitive operator, valueList arguments, encodedRest]
    source.freeFvarNames = [] ∧ Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") source := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  have typed := primitive_request_open _ grammar (epochPlan prepared table).snapshot.free operator arguments
    (patterns program) rest encodedRest resolved
  have closedTyping := primitive_request_open baseLanguage rfl FreeTypeContext.empty operator arguments
    (patterns program) rest encodedRest resolved
  refine ⟨?_, checkOpenPatternWellSorted_complete typed⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := closedTyping.1.freeType_of_mem_freeFvarNames_of_isObjectPattern closedTyping.2.2.1 present
  cases impossible

#print axioms primitive_request_open
#print axioms epoch_primitive_request_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
