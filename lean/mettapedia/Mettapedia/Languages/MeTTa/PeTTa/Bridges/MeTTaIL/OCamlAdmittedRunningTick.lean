import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceRunningTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedExecution

/-! Actual loaded-controller ticks derive their plan admission from the
prepared source program and checked provider table. The reached runner,
source encoding and retained epoch history remain the execution inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdmittedRunningTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (source : OCaml.MachineState) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs : Term) (quantum : Nat) (built : prepare program = .ok prepared)
    (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
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
      (encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)) :=
  OCamlSourceRunningTick.returns state program prepared table source runner epochs quantum built
    (prepared_epoch_complete program prepared table built signatures closed) finite reached resolved running

theorem observation_iff (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source : OCaml.MachineState)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (resolved : state? (patterns program) source = some runner.state) (running : runner.phase = .running)
    (after : State) (answers input output : List Atom) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:tick"
      [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum])}
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (returns state program prepared table source runner epochs quantum built signatures closed finite reached resolved running)
    after answers input output

#print axioms returns
#print axioms observation_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdmittedRunningTick
