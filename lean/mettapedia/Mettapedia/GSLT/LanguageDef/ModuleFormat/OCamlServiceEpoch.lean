import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveEpoch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochInvariant

/-! Each source-authorized service extension preserves the same combined
provider meaning and actual admission invariant. Both service families
retain all earlier row positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem failure_epoch_meaning (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (built : prepare program = .ok prepared) (complete : (plan prepared).complete = true)
    (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (meaning : ProviderMeaning (patterns program) table)
    (indexed : (patterns program)[index]? = some parameter) (failed : OCaml.matchPattern parameter argument = none) :
    let next := GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]
    (epochPlan prepared next).complete = true ∧ ProviderMeaning (patterns program) next ∧
      next.signatures = provider.signatures ∧
      ∀ position, position < table.rows.length → next.rows[position]? = table.rows[position]? := by
  dsimp only
  exact ⟨epoch_failure_append_complete program prepared table index argument built signatures complete closed,
    failure_append_preserves_meaning (patterns program) table index parameter argument meaning indexed failed,
    signatures, fun position inside => GeneralPremise.ProviderAppend.original_row_at table [failureRow index argument] position inside⟩

#print axioms failure_epoch_meaning

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
