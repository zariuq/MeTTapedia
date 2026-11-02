import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTerminal

/-! Terminal controller execution reads the exact result of its independent
source control point. The source state is recovered from the terminal target,
not supplied as a halted-state assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalCorrespondence

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlTerminalObservation

theorem complete_and_read (state : State) (program : OCaml.Program) (plan : GeneralExecutionAdmission.Plan)
    (standard epochs : Term) (source : OCaml.MachineState) (result : OCaml.Result)
    (runner : CompleteExecution.ClassMachine plan) (rank ticks quantum : Nat)
    (point : ControlPoint program source runner.state rank)
    (terminal : state? (patterns program) (.halted result) = some runner.state)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done) :
    let planTerm := CompletePlanWire.planTerm plan [] [] (.base "MlConfig")
    let runnerTerm := CompleteExecution.classMachineTerm plan runner
    let complete := machine "MlComplete" planTerm standard runnerTerm epochs
    rank = 0 ∧ source = .halted result ∧
      PureReturns runtime [] state (apply "gslt:ml:advance" [number (ticks + 1), number quantum,
        encoded (machine "MlRunning" planTerm standard runnerTerm epochs)]) state (encoded complete) ∧
      PureReturns runtime [] state (apply "gslt:ml:result" [encoded complete]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern result),
          epochs, .application "MlEpoch" [planTerm, runnerTerm]])) := by
  obtain ⟨zero, sourceSame⟩ := control_point_terminal_readback program result point terminal
  refine ⟨zero, sourceSame, OCamlSourceTerminalAdvance.returns state plan standard epochs (patterns program) result runner ticks quantum
    reached done terminal, ?_⟩
  have computed := OCamlControllerReadout.result_returns state (.symbol "MlComplete")
    (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")) standard
    (.symbol (CompleteExecution.classPhaseSymbol runner.phase)) (InferenceCettaWire.encodePattern runner.state)
    (CompleteExecution.classStateTerm plan runner.program) (encodeList InferenceCettaWire.encodePattern runner.states)
    (encodeList CompleteExecution.classReceiptTerm runner.receipts) epochs
  have same : runner.state = resultPattern result := (Option.some.inj ((state_exact _ _).symm.trans terminal)).symm
  simpa only [machine, CompleteExecution.classMachineTerm, same] using computed

#print axioms complete_and_read

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalCorrespondence
