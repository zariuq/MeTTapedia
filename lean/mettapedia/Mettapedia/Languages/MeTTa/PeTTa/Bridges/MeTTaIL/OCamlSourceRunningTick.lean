import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochStateChecks

/-! A reached runner at an encoded source state supplies its own typing
and readiness certificates. The source interface retains only preparation,
finite epoch admission and the actual reached runner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceRunningTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source : OCaml.MachineState) (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (complete : (epochPlan prepared table).complete = true)
    (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (resolved : state? (patterns program) source = some runner.state) (running : runner.phase = .running) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
      (encoded (machine "MlRunning" plan standard (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)) :=
  OCamlRunningTick.returns state prepared table runner epochs quantum complete finite reached
    (epoch_state_checked program prepared table source runner.state built resolved).2 running

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceRunningTick
