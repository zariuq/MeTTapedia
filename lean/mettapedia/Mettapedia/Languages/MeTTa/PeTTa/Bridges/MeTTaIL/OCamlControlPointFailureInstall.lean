import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochInstallExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunnerBeginExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointRestart

/-! Failure-row installation derives fresh runner execution from the current
source control point, independently of first-occurrence pattern lookup.
The actual old runner and epoch history are retained by the loaded install.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControlPointFailureInstall

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (index : Nat) (argument : OCaml.Value) (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term)
    {source : OCaml.MachineState} {rank : Nat} (built : prepare program = .ok prepared)
    (invariant : SourceEpochInvariant program prepared table) (point : ControlPoint program source runner.state rank)
    (done : runner.phase = .done) :
    let next := ProviderAppend.appendRows table [failureRow index argument]
    let oldPlan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let nextPlan := CompletePlanWire.planTerm (epochPlan prepared next) [] [] (.base "MlConfig")
    let fresh := CompleteExecution.classMachineTerm (epochPlan prepared next) (OCamlRunnerBeginExecution.begun prepared next runner.state)
    PureReturns runtime [] state (apply "gslt:ml:install" [encoded oldPlan, encoded (OCamlEpochStandard.standard prepared),
      encoded (CompleteExecution.classMachineTerm (epochPlan prepared table) runner), encoded epochs,
      encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm (failureRow index argument))]) state
      (encoded (machine "MlRunning" nextPlan (OCamlEpochStandard.standard prepared) fresh
        (.application "LCons" [.application "MlEpoch" [oldPlan, CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]))) := by
  let next := ProviderAppend.appendRows table [failureRow index argument]
  have checked := control_point_epoch_checked program prepared next built point
  have begun := OCamlRunnerBeginExecution.begin_returns state prepared next runner.state checked.1 checked.2
  have installed := OCamlEpochInstallExecution.epoch_install_returns state program prepared table index argument
    (OCamlEpochStandard.standard prepared) (InferenceCettaWire.encodePattern runner.state)
    (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
    (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts)
    epochs _ built invariant.source.signatures begun
  have sameRunner : CompleteExecution.classMachineTerm (epochPlan prepared table) runner =
      doneRunner (InferenceCettaWire.encodePattern runner.state) (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
        (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, doneRunner]
  rw [← sameRunner] at installed
  exact installed

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControlPointFailureInstall
