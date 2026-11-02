import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdmittedRunningTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeNormalized
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTyping

/-! Loaded MeTTa running ticks at pending administrative configurations
execute the existing normalized runner and preserve their source state.
Preparation and source provider evidence discharge admission and typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdministrativeTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution

theorem returns_preserving_source (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source : OCaml.MachineState)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum rank : Nat)
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (point : ControlPoint program source runner.state rank) (positive : 0 < rank) (running : runner.phase = .running) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
      (encoded (machine "MlRunning" plan standard (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)) ∧
    ∃ nextRank, ControlPoint program source next.state nextRank ∧ nextRank ≤ rank := by
  exact ⟨OCamlRunningTick.returns state prepared table runner epochs quantum
      (prepared_epoch_complete program prepared table built invariant.signatures closed) finite reached
      (control_point_epoch_checked program prepared table built point).2 running,
    administrative_runner_tick program prepared table runner quantum built invariant reached point positive⟩

#print axioms returns_preserving_source

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdministrativeTick
