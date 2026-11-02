import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerCompletion
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerResultInvariant

/-! Every finite independent O0 evaluation is realized by actual loaded
begin, advance and result calls, for every positive work quantum. The
public readout includes the exact source value or fault and retained epochs.
This does not replace source frontend or general domain/reflection proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant OCamlTerminalObservation

theorem read_complete (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs : Term) (expected : OCaml.Result)
    (terminal : state? (patterns program) (.halted expected) = some runner.state) :
    PureReturns runtime [] state (apply "gslt:ml:result" [encoded (controller prepared table "MlComplete" runner epochs)]) state
      (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern expected),
        epochs, .application "MlEpoch" [CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"),
          CompleteExecution.classMachineTerm (epochPlan prepared table) runner]])) := by
  have computed := OCamlControllerReadout.result_returns state (.symbol "MlComplete")
    (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
    (.symbol (CompleteExecution.classPhaseSymbol runner.phase)) (InferenceCettaWire.encodePattern runner.state)
    (CompleteExecution.classStateTerm (epochPlan prepared table) runner.program)
    (encodeList InferenceCettaWire.encodePattern runner.states) (encodeList CompleteExecution.classReceiptTerm runner.receipts) epochs
  have same : runner.state = resultPattern expected := (Option.some.inj ((state_exact _ _).symm.trans terminal)).symm
  simpa only [controller, machine, CompleteExecution.classMachineTerm, same] using computed

theorem finite_evaluation_realized (state : State) (program : OCaml.Program) (prepared : Prepared)
    (expected : OCaml.Result) (quantum : Nat) (built : prepare program = .ok prepared)
    (evaluation : OCaml.Evaluates program [] program.entry expected) (positive : 0 < quantum) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")
    PureReturns runtime [] state (apply "gslt:ml:begin"
      [encoded (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern (initial program))]) state (encoded startValue) ∧
    ∃ (ticks : Nat) (answer epochs current : Term),
      PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded startValue]) state (encoded answer) ∧
      Realizes program prepared expected answer ∧
      PureReturns runtime [] state (apply "gslt:ml:result" [encoded answer]) state
        (encoded (.application "MlResult" [.symbol "MlComplete", InferenceCettaWire.encodePattern (resultPattern expected), epochs, current])) := by
  refine ⟨OCamlBeginExecution.returns state program prepared built, ?_⟩
  obtain ⟨work, completed⟩ := OCaml.evaluates_iff_completed_run.mp evaluation
  have restarted := control_point_epoch_restart program prepared provider built (initial_control_point program)
  obtain ⟨ticks, finalTable, finalRunner, finalEpochs, invariant, reached, done, terminal, computed⟩ :=
    OCamlControllerCompletion.completes state program prepared provider
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil") quantum
      built (initial_source_epoch_invariant program prepared) restarted.1 restarted.2 completed positive
  exact ⟨ticks, controller prepared finalTable "MlComplete" finalRunner finalEpochs, finalEpochs,
    .application "MlEpoch" [CompletePlanWire.planTerm (epochPlan prepared finalTable) [] [] (.base "MlConfig"),
      CompleteExecution.classMachineTerm (epochPlan prepared finalTable) finalRunner], computed,
    .complete finalTable finalRunner finalEpochs invariant reached done terminal,
    read_complete state program prepared finalTable finalRunner finalEpochs expected terminal⟩

theorem finite_evaluation_readback (state afterAdvance afterRead : State) (program : OCaml.Program) (prepared : Prepared)
    (expected observed : OCaml.Result) (ticks quantum : Nat) (answer epochs current : Term)
    (built : prepare program = .ok prepared) (evaluation : OCaml.Evaluates program [] program.entry expected) :
    let startValue := controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")
    Runs runtime {state := state, control := .evaluate [] (apply "gslt:ml:advance"
      [number ticks, number quantum, encoded startValue])} (.complete afterAdvance [encoded answer] [] []) →
    Runs runtime {state := afterAdvance, control := .evaluate [] (apply "gslt:ml:result" [encoded answer])}
      (.complete afterRead [encoded (.application "MlResult" [.symbol "MlComplete",
        InferenceCettaWire.encodePattern (resultPattern observed), epochs, current])] [] []) →
    observed = expected := by
  dsimp only
  intro advanced read
  obtain ⟨actual, computed, related⟩ := OCamlControllerAdvanceInvariant.advance_returns state program prepared expected ticks quantum _ built
    (OCamlControllerAdvanceInvariant.initial_related program prepared expected built evaluation)
  have observations := (pure_returns_derivation_iff runtime [] state state _ _ computed afterAdvance _ [] []).mp advanced
  have sameState := observations.1
  have same := CettaWireAtom.encode_injective _ _ (List.cons.inj observations.2.1).1
  cases same
  subst afterAdvance
  exact OCamlControllerResultInvariant.completed_readback state program prepared expected observed _ epochs current afterRead related read

#print axioms read_complete
#print axioms finite_evaluation_realized
#print axioms finite_evaluation_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution
