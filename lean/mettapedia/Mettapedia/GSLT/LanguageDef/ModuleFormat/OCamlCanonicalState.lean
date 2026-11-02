import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedLanguage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProviderEpoch
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodedShapes
import Mettapedia.OSLF.MeTTaIL.GeneralVectorCanonical
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! Canonical commitment fixes actual encoded O0 source states. The
prepared language retains its authored empty equation and algebra tables;
the source codec uses constructors and ordered vectors only.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection

theorem epoch_laws_empty (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (built : prepare program = .ok prepared) : Complete.Normalized.laws (epochPlan prepared table) = [] := by
  have terms := (prepare_readback program prepared built).2.2.1
  change CollectionLaws.declared prepared.compiled = []
  unfold CollectionLaws.declared
  rw [terms]
  decide +kernel

theorem epoch_extrusions_empty (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (built : prepare program = .ok prepared) : Complete.Normalized.extrusions (epochPlan prepared table) = [] := by
  have equations := prepared_equations program prepared built
  change CollectionLaws.extrusions prepared.compiled = []
  unfold CollectionLaws.extrusions
  rw [equations]
  decide +kernel

theorem epoch_state_commit (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source : OCaml.MachineState) (encoded : Pattern)
    (built : prepare program = .ok prepared) (resolved : state? (patterns program) source = some encoded) :
    Complete.Normalized.commit (epochPlan prepared table) .canonical encoded = encoded := by
  simp only [Complete.Normalized.commit, Complete.Normalized.standard,
    epoch_laws_empty program prepared table built, epoch_extrusions_empty program prepared table built,
    CollectionLaws.standardForm_nil]
  exact (state?_vector (patterns program) source encoded resolved).canon_fixed

#print axioms epoch_laws_empty
#print axioms epoch_extrusions_empty
#print axioms epoch_state_commit

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
