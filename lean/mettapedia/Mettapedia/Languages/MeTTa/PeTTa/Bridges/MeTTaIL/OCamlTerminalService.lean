import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledServiceExecution

/-! Settled value and fault states complete the actual controller while
retaining the full current runner and all prior provider epochs.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalService

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution OCamlFailureServiceExecution

theorem terminal_returns (state : State) (plan standard arguments query states receipts epochs : Term)
    (name : String) (terminal : name = "MlDone" ∨ name = "MlFault")
    (finished : PureReturns runtime [] state
      (apply "gslt:search:status" [encoded (.symbol "ClassSearch"), encoded plan, encoded query]) state
      (encoded (.symbol "SearchComplete")))
    (empty : PureReturns runtime [] state
      (apply "gslt:search:publication" [encoded (.symbol "ClassSearch"), encoded query]) state (encoded (.symbol "LNil"))) :
    let runner := doneRunner (.application "PApp" [.string name, arguments]) query states receipts
    PureReturns runtime [] state (apply "gslt:ml:service" [encoded plan, encoded standard, encoded runner, encoded epochs]) state
      (encoded (machine "MlComplete" plan standard runner epochs)) := by
  rcases terminal with rfl | rfl <;> metta_call checked <;>
    service_eval [finished, empty] unfolding [doneRunner, machine]

theorem reached_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (standard arguments epochs : Term) (name : String) (terminal : name = "MlDone" ∨ name = "MlFault")
    (runner : CompleteExecution.ClassMachine plan)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern runner.state = .application "PApp" [.string name, arguments]) :
    PureReturns runtime [] state (apply "gslt:ml:service"
      [encoded (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")), encoded standard,
        encoded (CompleteExecution.classMachineTerm plan runner), encoded epochs]) state
      (encoded (machine "MlComplete" (CompletePlanWire.planTerm plan [] [] (.base "MlConfig")) standard
        (CompleteExecution.classMachineTerm plan runner) epochs)) := by
  have status := OCamlSearchWireExecution.settled_status_returns state plan [] [] (.base "MlConfig") .canonical runner reached done
  have empty := OCamlSearchWireExecution.settled_publication_returns state plan [] (.base "MlConfig") .canonical runner reached done
  have same : CompleteExecution.classMachineTerm plan runner = doneRunner
      (.application "PApp" [.string name, arguments]) (CompleteExecution.classStateTerm plan runner.program)
      (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) := by
    simp only [CompleteExecution.classMachineTerm, done, CompleteExecution.classPhaseSymbol, encodedState, doneRunner]
  rw [same]
  exact terminal_returns state _ standard arguments _ _ _ epochs name terminal status empty

#print axioms terminal_returns
#print axioms reached_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalService
