import Mettapedia.GSLT.Dynamics.OrderedOCamlRegion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution

/-!
# Prepared OCaml regions and the actual loaded PeTTa controller

The prepared handler worker refines the independent OCaml machine. Existing
LanguageDef/controller adequacy then realizes its finite completed result
through actual loaded PeTTa begin/advance/result calls. Public readback cannot
invent a different completed value or fault.

This is a completed-result bridge. A CEK step is not a controller search tick,
and the theorem does not identify their intermediate page counts or receipts.
Prepared LanguageDef admission remains an explicit checked prerequisite.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.OCamlRegionSourceBridge

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec MeTTaIL WireKit OCamlControllerSource OCamlInstallExecution
open OCamlControllerInvariant OCamlTerminalObservation

theorem compiled_completion_realized (state : State) (program : OCaml.Program) (prepared : Prepared)
    (expected : OCaml.Result) (budget quantum : Nat)
    (built : prepare program = .ok prepared)
    (completed : OCaml.CompiledDispatch.run program (OCaml.CompiledDispatch.prepare program)
      budget (OCaml.begin program) = .complete expected) (positive : 0 < quantum) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")
    PureReturns runtime [] state (apply "gslt:ml:begin"
      [encoded (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern (initial program))]) state
      (encoded startValue) ∧
    ∃ (ticks : Nat) (answer epochs current : Term),
      PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded startValue]) state
        (encoded answer) ∧ Realizes program prepared expected answer ∧
      PureReturns runtime [] state (apply "gslt:ml:result" [encoded answer]) state
        (encoded (.application "MlResult" [.symbol "MlComplete",
          InferenceCettaWire.encodePattern (resultPattern expected), epochs, current])) := by
  have evaluated : OCaml.Evaluates program [] program.entry expected :=
    OCaml.run_sound (by simpa only [OCaml.CompiledDispatch.run_exact] using completed)
  exact OCamlFiniteEvaluationExecution.finite_evaluation_realized state program prepared expected quantum
    built evaluated positive

theorem compiled_public_readback (state afterAdvance afterRead : State) (program : OCaml.Program)
    (prepared : Prepared) (expected observed : OCaml.Result) (budget ticks quantum : Nat)
    (answer epochs current : Term) (built : prepare program = .ok prepared)
    (completed : OCaml.CompiledDispatch.run program (OCaml.CompiledDispatch.prepare program)
      budget (OCaml.begin program) = .complete expected) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:advance"
      [number ticks, number quantum, encoded startValue])} (.complete afterAdvance [encoded answer] [] []) →
    Runs runtime {state := afterAdvance, control := .evaluate [] (apply "gslt:ml:result" [encoded answer])}
      (.complete afterRead [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] []) → observed = expected := by
  have evaluated : OCaml.Evaluates program [] program.entry expected :=
    OCaml.run_sound (by simpa only [OCaml.CompiledDispatch.run_exact] using completed)
  exact OCamlFiniteEvaluationExecution.finite_evaluation_readback state afterAdvance afterRead program prepared
    expected observed ticks quantum answer epochs current built evaluated

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.OCamlRegionSourceBridge
