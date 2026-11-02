import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTickDispatch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalService

/-! A settled runner is dispatched through the real controller tick.
The service result may complete the controller or restart a new provider
epoch; neither case replaces the retained runner history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (plan : GeneralExecutionAdmission.Plan) (standard epochs answer : Term)
    (runner : CompleteExecution.ClassMachine plan) (done : runner.phase = .done) (quantum : Nat)
    (serviced : PureReturns runtime [] state
      (apply "gslt:ml:service" [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan runner), encoded epochs]) state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:ml:tick"
      [encoded (machine "MlRunning" (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")) standard
        (CompleteExecution.classMachineTerm plan runner) epochs), number quantum]) state (encoded answer) := by
  have same : CompleteExecution.classMachineTerm plan runner = doneRunner (InferenceCettaWire.encodePattern runner.state)
      (CompleteExecution.classStateTerm plan runner.program) (encodeList InferenceCettaWire.encodePattern runner.states)
      (encodeList CompleteExecution.classReceiptTerm runner.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, doneRunner]
  rw [same] at serviced ⊢
  exact OCamlTickDispatch.settled_returns state _ standard _ _ _ _ epochs answer quantum serviced

theorem terminal_returns (state : State) (plan : GeneralExecutionAdmission.Plan) (standard arguments epochs : Term)
    (name : String) (terminal : name = "MlDone" ∨ name = "MlFault")
    (runner : CompleteExecution.ClassMachine plan) (quantum : Nat)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern runner.state = .application "PApp" [.string name, arguments]) :
    let planTerm := CompletePlanWire.planTerm plan [] [] (.base "MlConfig")
    PureReturns runtime [] state (apply "gslt:ml:tick"
      [encoded (machine "MlRunning" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs), number quantum]) state
      (encoded (machine "MlComplete" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs)) :=
  returns state plan standard epochs _ runner done quantum
    (OCamlTerminalService.reached_returns state plan standard arguments epochs name terminal runner reached done encodedState)

#print axioms returns
#print axioms terminal_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick
