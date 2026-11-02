import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompletionControls

/-! The named entry realizes finite source fixtures and rejects the value
of a failed first clause as its completed observation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedObservationControls

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlCompletionControls OCamlTerminalObservation OCamlEmittedEntrySource

theorem sample_entry_completes (state : State) (sample : OCaml.Program × OCaml.Result)
    (prepared : Prepared) (name : String) (emitted : SpaceSemantics.Program) (quantum : Nat)
    (member : sample ∈ samples) (preparedSource : prepare sample.1 = .ok prepared)
    (built : ExecutionData.emit? prepared name = .ok emitted) (positive : 0 < quantum) :
    ∃ (ticks : Nat) (epochs current : Term),
      PureReturns (moduleRuntime prepared name) [] state
        (apply (ExecutionData.runHead name) [number ticks, number quantum]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern sample.2),
          epochs, current])) :=
  OCamlEmittedFiniteEvaluation.finite_evaluation_realized state sample.1 prepared name emitted sample.2 quantum
    preparedSource built (sample_evaluates sample member) positive

theorem failed_clause_cannot_publish (state after : State) (prepared : Prepared) (name : String)
    (emitted : SpaceSemantics.Program) (ticks quantum : Nat) (epochs current : Term)
    (preparedSource : prepare fallbackProgram = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted) :
    ¬ Runs (moduleRuntime prepared name) {state := state, control := .evaluate [] (apply
      (ExecutionData.runHead name) [number ticks, number quantum])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern (.ok (integer 99))), epochs, current])] [] []) := by
  intro completed
  have same := OCamlEmittedFiniteEvaluation.completed_run_readback state after fallbackProgram prepared name emitted
    (.ok (integer 7)) (.ok (integer 99)) ticks quantum epochs current preparedSource built
    (OCaml.run_sound (budget := 100) (by rfl)) completed
  have integers : (99 : Int) = 7 := congrArg (fun result : OCaml.Result => match result with
    | .ok (.literal (.integer number)) => number
    | _ => 0) same
  exact (by decide +kernel : (99 : Int) ≠ 7) integers

#print axioms sample_entry_completes
#print axioms failed_clause_cannot_publish

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedObservationControls
