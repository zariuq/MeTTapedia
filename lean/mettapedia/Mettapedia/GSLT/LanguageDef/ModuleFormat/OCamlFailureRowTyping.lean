import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRows

/-! Failure rows satisfy the actual provider signature. This typing theorem
is separate from the source failure invariant required to authorize a row.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem failure_row_checked (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (index : Nat) (argument : OCaml.Value) :
    GeneralPremise.checkRow language free []
      ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ (failureRow index argument) = true := by
  apply GeneralPremise.checkRow_complete
  refine ⟨rfl, .cons ?_ (.cons ?_ .nil)⟩
  · exact typed_node_open
      (by simp only [patternId]; exact node_vector_all _ _ (vector_list_cons (digits_vector index) vector_list_nil))
      (patternId_typed language terms free [] index)
  · exact typed_node_open (value_vector argument) (value_typed language terms free [] argument)

theorem failure_row_append_checked (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (snapshot : GeneralPremise.ProviderSnapshot)
    (signatures : snapshot.signatures = provider.signatures) (index : Nat) (argument : OCaml.Value) :
    GeneralPremise.ProviderAppend.appendChecked? language free snapshot [failureRow index argument] =
      some (GeneralPremise.ProviderAppend.appendRows snapshot [failureRow index argument]) := by
  have signature : GeneralPremise.signature? snapshot "ml-pattern-failure" 2 =
      some ⟨"ml-pattern-failure", [.base "MlPattern", .base "MlValue"], [.input, .input]⟩ := by
    unfold GeneralPremise.signature?
    rw [signatures]
    decide +kernel
  have checked := failure_row_checked language terms free index argument
  have rows : GeneralPremise.ProviderAppend.checkRows language free snapshot [failureRow index argument] = true := by
    change ((match GeneralPremise.signature? snapshot "ml-pattern-failure" 2 with
      | none => false
      | some declared => GeneralPremise.checkRow language free [] declared (failureRow index argument)) && true) = true
    rw [signature]
    simpa only [Bool.and_true] using checked
  simp only [GeneralPremise.ProviderAppend.appendChecked?, rows, if_true]

#print axioms failure_row_checked
#print axioms failure_row_append_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
