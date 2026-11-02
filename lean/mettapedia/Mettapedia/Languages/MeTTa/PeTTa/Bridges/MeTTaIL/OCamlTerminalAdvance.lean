import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSettledTick
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStep
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStopped

/-! A source terminal state in a settled runner becomes complete on the
next controller tick. Every later tick budget preserves its exact epochs
and receipts; zero ticks leave completion pending at the controller level.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalAdvance

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns (state : State) (plan : GeneralExecutionAdmission.Plan) (standard arguments epochs : Term)
    (name : String) (terminal : name = "MlDone" ∨ name = "MlFault")
    (runner : CompleteExecution.ClassMachine plan) (ticks quantum : Nat)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done)
    (encodedState : InferenceCettaWire.encodePattern runner.state = .application "PApp" [.string name, arguments]) :
    let planTerm := CompletePlanWire.planTerm plan [] [] (.base "MlConfig")
    PureReturns runtime [] state (apply "gslt:ml:advance"
      [number (ticks + 1), number quantum,
        encoded (machine "MlRunning" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs)]) state
      (encoded (machine "MlComplete" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs)) := by
  dsimp only
  exact OCamlAdvanceStep.running_returns state _ standard _ epochs _ _ ticks quantum
    (OCamlSettledTick.terminal_returns state plan standard arguments epochs name terminal runner quantum reached done encodedState)
    (OCamlAdvanceStopped.returns state "MlComplete" _ standard _ epochs ticks quantum (Or.inl rfl))

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalAdvance
