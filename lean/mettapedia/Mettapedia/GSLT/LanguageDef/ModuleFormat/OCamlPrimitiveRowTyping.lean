import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRows
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRowTyping

/-! Primitive answers inhabit the declared provider signature. The
independent source-evaluation invariant remains a separate requirement.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem primitiveResult_vector (result : OCaml.Result) : VectorFirstOrder (primitiveResult result) := by
  cases result with
  | ok actual => exact node_vector_all _ _ (vector_list_cons (value_vector actual) vector_list_nil)
  | error error => exact node_vector_all _ _ (vector_list_cons (fault_vector error) vector_list_nil)

theorem primitiveResult_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (result : OCaml.Result) :
    HasType language free bound (primitiveResult result) (.base "MlPrimitiveResult") := by
  cases result with
  | ok actual =>
    exact nonbare_constructor_typed terms [("value", .base "MlValue")] _ (by decide +kernel)
      (.cons (value_typed language terms free bound actual) .nil)
  | error error =>
    exact nonbare_constructor_typed terms [("fault", .base "MlFaultData")] _ (by decide +kernel)
      (.cons (fault_typed language terms free bound error) .nil)

theorem primitive_row_checked (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) :
    GeneralPremise.checkRow language free []
      ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩
      (primitiveRow operator arguments result) = true := by
  apply GeneralPremise.checkRow_complete
  refine ⟨rfl, .cons ?_ (.cons ?_ (.cons ?_ .nil))⟩
  · exact typed_node_open (primitive_vector operator) (primitive_typed language terms free [] operator)
  · exact typed_node_open (valueList_vector arguments) (valueList_typed language terms free [] arguments)
  · exact typed_node_open (primitiveResult_vector result) (primitiveResult_typed language terms free [] result)

theorem primitive_row_append_checked (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (table : GeneralPremise.ProviderSnapshot)
    (signatures : table.signatures = provider.signatures)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result) :
    GeneralPremise.ProviderAppend.appendChecked? language free table [primitiveRow operator arguments result] =
      some (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) := by
  have signature : GeneralPremise.signature? table "ml-primitive" 3 =
      some ⟨"ml-primitive", [.base "MlPrimitive", .base "MlValues", .base "MlPrimitiveResult"], [.input, .input, .output]⟩ := by
    unfold GeneralPremise.signature?
    rw [signatures]
    decide +kernel
  have checked := primitive_row_checked language terms free operator arguments result
  have rows : GeneralPremise.ProviderAppend.checkRows language free table [primitiveRow operator arguments result] = true := by
    change ((match GeneralPremise.signature? table "ml-primitive" 3 with
      | none => false
      | some declared => GeneralPremise.checkRow language free [] declared (primitiveRow operator arguments result)) && true) = true
    rw [signature]
    simpa only [Bool.and_true] using checked
  simp only [GeneralPremise.ProviderAppend.appendChecked?, rows, if_true]

#print axioms primitive_row_checked
#print axioms primitive_row_append_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
