import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerResultInvariant
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlOccurrenceProgressControls

/-! The loaded controller's arbitrary advance pages retain the independent
capture result. Its public reader cannot publish the argument in place of
the captured value, even across service epochs.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerProgressControls

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant
open ControlFlowControls

def expected : OCaml.Result := .ok (.cons (number 42) (.literal .nil))
def wrong : OCaml.Result := .ok (.cons (number 7) (.literal .nil))

theorem captured_source_result : OCaml.Evaluates captureProgram [] captureProgram.entry expected :=
  OCaml.run_sound (budget := 100) (by rfl)

theorem arbitrary_pages_preserve_capture (state : State) (prepared : Prepared) (ticks quantum : Nat)
    (built : prepare captureProgram = .ok prepared) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial captureProgram)) (.symbol "LNil")
    ∃ answer, PureReturns runtime [] state
      (apply "gslt:ml:advance" [WireKit.number ticks, WireKit.number quantum, encoded startValue]) state (encoded answer) ∧
      Realizes captureProgram prepared expected answer :=
  (OCamlControllerAdvanceInvariant.begin_and_advance state captureProgram prepared expected ticks quantum built captured_source_result).2

theorem argument_cannot_replace_capture (state after : State) (prepared : Prepared) (input epochs current : Term)
    (related : Realizes captureProgram prepared expected input) :
    ¬ Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:result" [encoded input])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (OCamlTerminalObservation.resultPattern wrong), epochs, current])] [] []) := by
  intro claimed
  have same := OCamlControllerResultInvariant.completed_readback state captureProgram prepared expected wrong
    input epochs current after related claimed
  have integers : (7 : Int) = 42 := congrArg (fun result : OCaml.Result => match result with
    | .ok (.cons (.literal (.integer integer)) _) => integer
    | _ => 0) same
  exact (by decide +kernel : (7 : Int) ≠ 42) integers

#print axioms captured_source_result
#print axioms arbitrary_pages_preserve_capture
#print axioms argument_cannot_replace_capture

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerProgressControls
