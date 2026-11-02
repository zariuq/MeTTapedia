import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRowTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderMeaning

/-! A source-authorized primitive answer extends the typed provider without
changing compiled rows or earlier row positions, and preserves both source
meaning invariants.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem epoch_primitive_append_complete (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (complete : (plan prepared).complete = true)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true) :
    (epochPlan prepared (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result])).complete = true := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have extended := GeneralPremise.ProviderAppend.checked_typing prepared.compiled (epochSnapshot prepared table).free table
    (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) [primitiveRow operator arguments result] closed
    (primitive_row_append_checked prepared.compiled terms _ table signatures operator arguments result)
  exact epoch_complete prepared _ signatures complete extended

theorem primitive_epoch_invariant (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (operator : OCaml.Primitive) (arguments : List OCaml.Value)
    (result : OCaml.Result) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures) (complete : (plan prepared).complete = true)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table) (evaluated : operator.eval arguments = .ok result) :
    let next := GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      next.signatures = provider.signatures ∧
      ∀ position, position < table.rows.length → next.rows[position]? = table.rows[position]? := by
  dsimp only
  exact ⟨epoch_primitive_append_complete program prepared table operator arguments result built signatures complete closed,
    primitive_append_preserves_meaning (patterns program) table operator arguments result meaning evaluated,
    signatures, fun position inside => GeneralPremise.ProviderAppend.original_row_at table [primitiveRow operator arguments result] position inside⟩

#print axioms epoch_primitive_append_complete
#print axioms primitive_epoch_invariant

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
