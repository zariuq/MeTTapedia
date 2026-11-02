import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedWrapperExecution

/-! Every finite independent source evaluation has a completed execution
through the named entry of an admitted emitted O0 module. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlEmittedEntrySource OCamlEmittedWrapperExecution OCamlTerminalObservation
open OCamlInstallExecution OCamlControllerInvariant DeclarativeSpec

theorem result_pattern_injective : Function.Injective resultPattern := by
  intro first second same
  apply halted_encoding_injective [] first second
  rw [state_exact, state_exact, same]

theorem completed_run_readback (state after : State) (program : OCaml.Program) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program) (expected observed : OCaml.Result)
    (ticks quantum : Nat) (epochs current : Term)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted)
    (evaluation : OCaml.Evaluates program [] program.entry expected)
    (completed : Runs (moduleRuntime prepared name) {state := state, control := .evaluate [] (apply
      (ExecutionData.runHead name) [number ticks, number quantum])}
      (.complete after [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] [])) :
    observed = expected := by
  obtain ⟨answer, advanced, related⟩ := OCamlControllerAdvanceInvariant.advance_returns state program prepared expected ticks quantum
    (initialController program prepared) preparedSource
    (OCamlControllerAdvanceInvariant.initial_related program prepared expected preparedSource evaluation)
  cases related with
  | running table runner earlier source rank work invariant reached point finite =>
    have readout := OCamlControllerReadout.result_returns state (.symbol "MlRunning")
      (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
      (.symbol (CompleteExecution.classPhaseSymbol runner.phase)) (InferenceCettaWire.encodePattern runner.state)
      (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
      (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) earlier
    have computed := run_returns state program prepared name emitted ticks quantum _ _ preparedSource built advanced readout
    have observations := (pure_returns_derivation_iff _ [] state state _ _ computed after _ [] []).mp completed
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj observations.2.1).1
    have fields := (Term.application.inj same).2
    simp at fields
  | complete table runner earlier invariant reached done terminal =>
    have readout := OCamlFiniteEvaluationExecution.read_complete state program prepared table runner earlier expected terminal
    have computed := run_returns state program prepared name emitted ticks quantum _ _ preparedSource built advanced readout
    have observations := (pure_returns_derivation_iff _ [] state state _ _ computed after _ [] []).mp completed
    have same := CettaWireAtom.encode_injective _ _ (List.cons.inj observations.2.1).1
    have fields := List.cons.inj (Term.application.inj same).2
    exact result_pattern_injective (InferenceCettaWire.encodePattern_injective (List.cons.inj fields.2).1)

theorem finite_evaluation_realized (state : State) (program : OCaml.Program) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program) (expected : OCaml.Result) (quantum : Nat)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted)
    (evaluation : OCaml.Evaluates program [] program.entry expected) (positive : 0 < quantum) :
    ∃ (ticks : Nat) (epochs current : Term),
      PureReturns (moduleRuntime prepared name) [] state
        (apply (ExecutionData.runHead name) [number ticks, number quantum]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern expected),
          epochs, current])) := by
  obtain ⟨ticks, answer, epochs, current, advanced, _, readout⟩ :=
    (OCamlFiniteEvaluationExecution.finite_evaluation_realized state program prepared expected quantum
      preparedSource evaluation positive).2
  exact ⟨ticks, epochs, current,
    run_returns state program prepared name emitted ticks quantum answer _ preparedSource built advanced readout⟩

#print axioms finite_evaluation_realized
#print axioms result_pattern_injective
#print axioms completed_run_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedFiniteEvaluation
