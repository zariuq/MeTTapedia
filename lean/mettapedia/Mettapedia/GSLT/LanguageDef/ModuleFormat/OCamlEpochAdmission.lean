import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRowTyping

/-! A typed replacement table preserves actual plan admission. Appending a
well-typed failure row retains admission and all prior provider positions.
This does not replace its separate semantic failure authorization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem epoch_complete (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (signatures : table.signatures = provider.signatures) (complete : (plan prepared).complete = true)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    (epochPlan prepared table).complete = true :=
  GeneralExecutionAdmission.complete_replace_provider (before := snapshot prepared) (after := epochSnapshot prepared table)
    rfl rfl signatures.symm permissions complete closed

theorem epoch_failure_append_complete (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (argument : OCaml.Value)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (complete : (plan prepared).complete = true)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    (epochPlan prepared (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument])).complete = true := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have extended := GeneralPremise.ProviderAppend.checked_typing prepared.compiled (epochSnapshot prepared table).free table
    (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]) [failureRow index argument] closed
    (failure_row_append_checked prepared.compiled terms _ table signatures index argument)
  exact epoch_complete prepared _ signatures complete extended

#print axioms epoch_complete
#print axioms epoch_failure_append_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
