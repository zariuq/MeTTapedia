import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveRows
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFailureRows

/-! The two provider families retain independent meanings across each
other's extensions. A primitive result cannot serve as pattern-failure
information, and vice versa.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem failure_append_preserves_primitives (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (argument : OCaml.Value) (sound : PrimitiveRowsSound table) :
    PrimitiveRowsSound (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]) := by
  intro operator arguments result present
  rcases (GeneralPremise.ProviderAppend.row_membership table [failureRow index argument]
    (primitiveRow operator arguments result)).mp present with old | fresh
  · exact sound operator arguments result old
  · have same := congrArg GeneralPremise.ProviderRow.relation (List.mem_singleton.mp fresh)
    simp [primitiveRow, failureRow] at same

theorem primitive_append_preserves_failures (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (sound : FailureRowsSound pool table) :
    FailureRowsSound pool (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) := by
  intro index parameter argument indexed present
  rcases (GeneralPremise.ProviderAppend.row_membership table [primitiveRow operator arguments result]
    (failureRow index argument)).mp present with old | fresh
  · exact sound index parameter argument indexed old
  · have same := congrArg GeneralPremise.ProviderRow.relation (List.mem_singleton.mp fresh)
    simp [primitiveRow, failureRow] at same

def ProviderMeaning (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot) : Prop :=
  PrimitiveRowsSound table ∧ FailureRowsSound pool table

theorem initial_provider_meaning (pool : List OCaml.MatchPattern) : ProviderMeaning pool provider :=
  ⟨initial_primitive_rows_sound, initial_failure_rows_sound pool⟩

theorem primitive_append_preserves_meaning (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (sound : ProviderMeaning pool table) (evaluated : operator.eval arguments = .ok result) :
    ProviderMeaning pool (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) :=
  ⟨append_primitive_sound table operator arguments result sound.1 evaluated,
   primitive_append_preserves_failures pool table operator arguments result sound.2⟩

theorem failure_append_preserves_meaning (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (sound : ProviderMeaning pool table) (indexed : pool[index]? = some parameter)
    (failed : OCaml.matchPattern parameter argument = none) :
    ProviderMeaning pool (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]) :=
  ⟨failure_append_preserves_primitives table index argument sound.1,
   append_failure_sound pool table index parameter argument sound.2 indexed failed⟩

#print axioms primitive_append_preserves_meaning
#print axioms failure_append_preserves_meaning

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
