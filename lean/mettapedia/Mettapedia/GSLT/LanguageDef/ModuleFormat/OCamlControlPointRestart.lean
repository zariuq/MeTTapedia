import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceEpochInvariant

/-! Reinitializing the actual normalized runner after a provider change
preserves the source control point. Canonical commitment cannot change its
encoded state; the fresh runner has the shared reached invariant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem control_point_epoch_restart (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    {source : OCaml.MachineState} {config : Pattern} {rank : Nat}
    (built : prepare program = .ok prepared) (point : ControlPoint program source config rank) :
    let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
    let fresh := Machine.begin search (Complete.Normalized.commit (epochPlan prepared table) .canonical config)
    Reached search fresh ∧ ControlPoint program source fresh.state rank := by
  refine ⟨begin_reached _, ?_⟩
  change ControlPoint program source (Complete.Normalized.commit (epochPlan prepared table) .canonical config) rank
  rw [control_point_commit program prepared table built point]
  exact point

#print axioms control_point_epoch_restart

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
