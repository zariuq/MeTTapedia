import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution
import Mettapedia.Languages.OCaml.EvaluationControls

/-! Finite source fixtures exercise recursive execution, failed-clause
fallthrough and a language fault through loaded controller completion.
Negative controls forbid a successful-pattern failure cache and the body
of a failed first clause as a completed public observation.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompletionControls

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant OCamlTerminalObservation

def integer (value : Int) : OCaml.Value := .literal (.integer value)

def fallbackProgram : OCaml.Program where
  code := #[.literal (.integer 7), .literal (.integer 99), .variable 0,
    .matchValue 0 [⟨.literal (.integer 0), 1⟩, ⟨.bind, 2⟩]]
  entry := 3

def faultProgram : OCaml.Program where
  code := #[.literal (.integer 7), .literal (.integer 0), .primitive .divide [0, 1]]
  entry := 2

def samples : List (OCaml.Program × OCaml.Result) := [
  (fallbackProgram, .ok (integer 7)), (faultProgram, .error .divisionByZero),
  (OCaml.Examples.recursion, .ok (.tuple [integer 720, integer 55]))]

#guard (prepare fallbackProgram).toOption.isSome
#guard (prepare faultProgram).toOption.isSome
#guard (prepare OCaml.Examples.recursion).toOption.isSome
#guard OCaml.run fallbackProgram 100 (OCaml.begin fallbackProgram) == .complete (.ok (integer 7))
#guard !(OCaml.run fallbackProgram 100 (OCaml.begin fallbackProgram) == .complete (.ok (integer 99)))
#guard OCaml.run faultProgram 100 (OCaml.begin faultProgram) == .complete (.error .divisionByZero)

theorem sample_evaluates (sample : OCaml.Program × OCaml.Result) (member : sample ∈ samples) :
    OCaml.Evaluates sample.1 [] sample.1.entry sample.2 := by
  rcases List.mem_cons.mp member with rfl | member
  · exact OCaml.run_sound (budget := 100) (by rfl)
  · rcases List.mem_cons.mp member with rfl | member
    · exact OCaml.run_sound (budget := 100) (by rfl)
    · have same := List.mem_singleton.mp member
      subst sample
      exact OCaml.EvaluationControls.recursion_evaluates

theorem samples_eventually_complete (state : State) (sample : OCaml.Program × OCaml.Result)
    (prepared : Prepared) (quantum : Nat) (member : sample ∈ samples)
    (built : prepare sample.1 = .ok prepared) (positive : 0 < quantum) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial sample.1)) (.symbol "LNil")
    ∃ (ticks : Nat) (answer epochs current : Term),
      PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded startValue]) state (encoded answer) ∧
      Realizes sample.1 prepared sample.2 answer ∧
      PureReturns runtime [] state (apply "gslt:ml:result" [encoded answer]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern sample.2), epochs, current])) :=
  (OCamlFiniteEvaluationExecution.finite_evaluation_realized state sample.1 prepared sample.2 quantum built
    (sample_evaluates sample member) positive).2

theorem successful_pattern_not_cached_as_failure (table : GeneralPremise.ProviderSnapshot)
    (invariant : SourceProviderInvariant (patterns fallbackProgram) table) :
    failureRow 1 (integer 7) ∉ table.rows := by
  intro cached
  have failed := invariant.meaningful.2 1 .bind (integer 7) (by rfl) cached
  cases failed

theorem failed_body_not_publishable (state afterAdvance afterRead : State) (prepared : Prepared)
    (ticks quantum : Nat) (answer epochs current : Term) (built : prepare fallbackProgram = .ok prepared) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial fallbackProgram)) (.symbol "LNil")
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:advance"
      [number ticks, number quantum, encoded startValue])} (.complete afterAdvance [encoded answer] [] []) →
    ¬ Runs runtime {state := afterAdvance, control := .evaluate [] (apply "gslt:ml:result" [encoded answer])}
      (.complete afterRead [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern (.ok (integer 99))), epochs, current])] [] []) := by
  dsimp only
  intro advanced read
  have same := OCamlFiniteEvaluationExecution.finite_evaluation_readback state afterAdvance afterRead fallbackProgram prepared
    (.ok (integer 7)) (.ok (integer 99)) ticks quantum answer epochs current built
    (OCaml.run_sound (budget := 100) (by rfl)) advanced read
  have integers : (99 : Int) = 7 := congrArg (fun result : OCaml.Result => match result with
    | .ok (.literal (.integer number)) => number
    | _ => 0) same
  exact (by decide +kernel : (99 : Int) ≠ 7) integers

#print axioms sample_evaluates
#print axioms samples_eventually_complete
#print axioms successful_pattern_not_cached_as_failure
#print axioms failed_body_not_publishable

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompletionControls
