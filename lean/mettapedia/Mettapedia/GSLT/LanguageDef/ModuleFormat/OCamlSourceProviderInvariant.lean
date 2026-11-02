import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEncoding

/-! The source cache invariant combines the actual provider signatures,
encoded row identities and independent meanings. Both existing service
append operations preserve it from the empty provider.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

structure SourceProviderInvariant (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot) : Prop where
  signatures : table.signatures = provider.signatures
  meaningful : ProviderMeaning pool table
  encoded : EncodedProviderRows table

theorem initial_source_provider_invariant (pool : List OCaml.MatchPattern) : SourceProviderInvariant pool provider :=
  ⟨rfl, initial_provider_meaning pool, initial_provider_rows_encoded⟩

theorem primitive_append_source_invariant (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (invariant : SourceProviderInvariant pool table) (evaluated : operator.eval arguments = .ok result) :
    SourceProviderInvariant pool (GeneralPremise.ProviderAppend.appendRows table [primitiveRow operator arguments result]) :=
  ⟨invariant.signatures, primitive_append_preserves_meaning pool table operator arguments result invariant.meaningful evaluated,
    primitive_append_preserves_encoding table operator arguments result invariant.encoded⟩

theorem failure_append_source_invariant (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (invariant : SourceProviderInvariant pool table) (indexed : pool[index]? = some parameter)
    (failed : OCaml.matchPattern parameter argument = none) :
    SourceProviderInvariant pool (GeneralPremise.ProviderAppend.appendRows table [failureRow index argument]) :=
  ⟨invariant.signatures, failure_append_preserves_meaning pool table index parameter argument invariant.meaningful indexed failed,
    failure_append_preserves_encoding table index argument invariant.encoded⟩

theorem source_primitive_answers_unique (pool : List OCaml.MatchPattern) (table : GeneralPremise.ProviderSnapshot)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (first second : OCaml.Result)
    (invariant : SourceProviderInvariant pool table)
    (left : primitiveRow operator arguments first ∈ table.rows)
    (right : primitiveRow operator arguments second ∈ table.rows) : first = second := by
  exact Except.ok.inj ((invariant.meaningful.1 operator arguments first left).symm.trans
    (invariant.meaningful.1 operator arguments second right))

#print axioms initial_source_provider_invariant
#print axioms primitive_append_source_invariant
#print axioms failure_append_source_invariant
#print axioms source_primitive_answers_unique

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
