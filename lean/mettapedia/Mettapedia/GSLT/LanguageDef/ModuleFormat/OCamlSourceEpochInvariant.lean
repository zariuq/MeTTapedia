import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceProviderInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPrimitiveEpoch

/-! A service epoch carries source-encoded, meaningful rows, their checked
closed typing, and the finite-provider contract required by the shared
runner. The actual append operations preserve every field.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise

structure SourceEpochInvariant (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot) : Prop where
  source : SourceProviderInvariant (patterns program) table
  closed : checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true
  finite : table.dynamicRelations = []

theorem initial_source_epoch_invariant (program : OCaml.Program) (prepared : Prepared) :
    SourceEpochInvariant program prepared provider :=
  ⟨initial_source_provider_invariant _, initial_provider_checked prepared, rfl⟩

theorem SourceEpochInvariant.complete {program : OCaml.Program} {prepared : Prepared} {table : ProviderSnapshot}
    (invariant : SourceEpochInvariant program prepared table) (built : prepare program = .ok prepared) :
    (epochPlan prepared table).complete = true :=
  prepared_epoch_complete program prepared table built invariant.source.signatures invariant.closed

theorem SourceEpochInvariant.primitive {program : OCaml.Program} {prepared : Prepared} {table : ProviderSnapshot}
    (invariant : SourceEpochInvariant program prepared table) (built : prepare program = .ok prepared)
    (operator : OCaml.Primitive) (arguments : List OCaml.Value) (result : OCaml.Result)
    (evaluated : operator.eval arguments = .ok result) :
    SourceEpochInvariant program prepared (ProviderAppend.appendRows table [primitiveRow operator arguments result]) := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  exact ⟨primitive_append_source_invariant _ _ _ _ _ invariant.source evaluated,
    ProviderAppend.checked_typing prepared.compiled (epochSnapshot prepared table).free table
      (ProviderAppend.appendRows table [primitiveRow operator arguments result]) [primitiveRow operator arguments result]
      invariant.closed (primitive_row_append_checked prepared.compiled terms _ table invariant.source.signatures operator arguments result),
    invariant.finite⟩

theorem SourceEpochInvariant.failure {program : OCaml.Program} {prepared : Prepared} {table : ProviderSnapshot}
    (invariant : SourceEpochInvariant program prepared table) (built : prepare program = .ok prepared)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value)
    (indexed : (patterns program)[index]? = some parameter) (failed : OCaml.matchPattern parameter argument = none) :
    SourceEpochInvariant program prepared (ProviderAppend.appendRows table [failureRow index argument]) := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  exact ⟨failure_append_source_invariant _ _ _ _ _ invariant.source indexed failed,
    ProviderAppend.checked_typing prepared.compiled (epochSnapshot prepared table).free table
      (ProviderAppend.appendRows table [failureRow index argument]) [failureRow index argument]
      invariant.closed (failure_row_append_checked prepared.compiled terms _ table invariant.source.signatures index argument),
    invariant.finite⟩

#print axioms initial_source_epoch_invariant
#print axioms SourceEpochInvariant.complete
#print axioms SourceEpochInvariant.primitive
#print axioms SourceEpochInvariant.failure

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
