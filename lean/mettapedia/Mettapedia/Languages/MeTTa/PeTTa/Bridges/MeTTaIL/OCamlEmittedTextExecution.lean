import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation

/-! Execution is joined to the program actually read from accepted emitted
text, loaded after the controller. Parsing, emission and source evaluation
remain separate premises with their own correspondence theorems. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedTextExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlTerminalObservation OCamlEmittedEntrySource

theorem accepted_text {prepared : Prepared} {name text : String}
    (built : ExecutionData.emitText? prepared name = .ok text) :
    ExecutionData.emit? prepared name = .ok (ExecutionData.program prepared name) ∧
      SpaceSemantics.readProgram text = .ok (ExecutionData.program prepared name) := by
  refine ⟨?_, OCamlEmissionReadback.emitted_text_reads_back built⟩
  cases emitted : ExecutionData.emit? prepared name with
  | error reason => simp [ExecutionData.emitText?, emitted] at built
  | ok output =>
    have same := (OCamlEmissionReadback.emitted_program emitted).1
    exact congrArg Except.ok same

theorem finite_evaluation_realized (state : State) (program : OCaml.Program) (prepared : Prepared)
    (name text : String) (loaded : SpaceSemantics.Program) (expected : OCaml.Result) (quantum : Nat)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emitText? prepared name = .ok text)
    (read : SpaceSemantics.readProgram text = .ok loaded)
    (evaluation : OCaml.Evaluates program [] program.entry expected) (positive : 0 < quantum) :
    ∃ (ticks : Nat) (epochs current : Term),
      PureReturns (OCamlControllerSource.runtime.append loaded) [] state
        (apply (ExecutionData.runHead name) [number ticks, number quantum]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern expected),
          epochs, current])) := by
  obtain ⟨emitted, reads⟩ := accepted_text built
  have same := Except.ok.inj (read.symm.trans reads)
  subst loaded
  exact OCamlEmittedFiniteEvaluation.finite_evaluation_realized state program prepared name _ expected quantum
    preparedSource emitted evaluation positive

theorem completed_run_readback (state after : State) (program : OCaml.Program) (prepared : Prepared)
    (name text : String) (loaded : SpaceSemantics.Program) (expected observed : OCaml.Result)
    (ticks quantum : Nat) (epochs current : Term)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emitText? prepared name = .ok text)
    (read : SpaceSemantics.readProgram text = .ok loaded)
    (evaluation : OCaml.Evaluates program [] program.entry expected)
    (completed : Runs (OCamlControllerSource.runtime.append loaded) {state := state, control := .evaluate [] (apply
      (ExecutionData.runHead name) [number ticks, number quantum])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] [])) :
    observed = expected := by
  obtain ⟨emitted, reads⟩ := accepted_text built
  have same := Except.ok.inj (read.symm.trans reads)
  subst loaded
  exact OCamlEmittedFiniteEvaluation.completed_run_readback state after program prepared name _ expected observed
    ticks quantum epochs current preparedSource emitted evaluation completed

#print axioms accepted_text
#print axioms finite_evaluation_realized
#print axioms completed_run_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedTextExecution
