import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochRequestChecks
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlStateClosed

/-! Every successfully encoded source state is a closed checked O0 state
in each provider epoch. This uses source typing, independently of execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem epoch_state_checked (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source : OCaml.MachineState) (encoded : Pattern)
    (built : prepare program = .ok prepared) (resolved : state? (patterns program) source = some encoded) :
    encoded.freeFvarNames = [] ∧ Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") encoded := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  exact ⟨state?_closed _ source encoded resolved,
    checkOpenPatternWellSorted_complete (state?_open _ grammar _ [] _ source encoded resolved)⟩

#print axioms epoch_state_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
