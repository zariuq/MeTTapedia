import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTerminalObservation

/-! A settled runner at an encoded source result becomes a complete
controller result under every positive tick budget. Its source value/fault
and retained histories are read by the actual public result operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlTerminalObservation

theorem returns (state : State) (plan : GeneralExecutionAdmission.Plan) (standard epochs : Term)
    (pool : List OCaml.MatchPattern) (result : OCaml.Result) (runner : CompleteExecution.ClassMachine plan) (ticks quantum : Nat)
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search plan [] (.base "MlConfig") .canonical) runner)
    (done : runner.phase = .done) (resolved : state? pool (.halted result) = some runner.state) :
    let planTerm := CompletePlanWire.planTerm plan [] [] (.base "MlConfig")
    PureReturns runtime [] state (apply "gslt:ml:advance" [number (ticks + 1), number quantum,
      encoded (machine "MlRunning" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs)]) state
      (encoded (machine "MlComplete" planTerm standard (CompleteExecution.classMachineTerm plan runner) epochs)) := by
  dsimp only
  rw [state_exact] at resolved
  have same := (Option.some.inj resolved).symm
  cases result with
  | ok actual =>
    apply OCamlTerminalAdvance.returns state plan standard (encodeList InferenceCettaWire.encodePattern [value actual])
      epochs "MlDone" (Or.inl rfl) runner ticks quantum reached done
    simp only [same, resultPattern, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]
  | error error =>
    apply OCamlTerminalAdvance.returns state plan standard (encodeList InferenceCettaWire.encodePattern [fault error])
      epochs "MlFault" (Or.inr rfl) runner ticks quantum reached done
    simp only [same, resultPattern, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance
