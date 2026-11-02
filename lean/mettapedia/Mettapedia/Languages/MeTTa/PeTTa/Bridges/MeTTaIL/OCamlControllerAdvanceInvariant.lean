import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerTickInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStep
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStopped
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlBeginExecution

/-! Actual loaded advance pages preserve the source relation across any
number of running ticks, service restarts and terminal completion. The
initial relation is derived from an independent source evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerAdvanceInvariant

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant

theorem advance_returns (state : State) (program : OCaml.Program) (prepared : Prepared) (expected : OCaml.Result)
    (ticks quantum : Nat) (input : Term) (built : prepare program = .ok prepared)
    (related : Realizes program prepared expected input) :
    ∃ answer, PureReturns runtime [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded input]) state (encoded answer) ∧
      Realizes program prepared expected answer := by
  induction ticks generalizing input with
  | zero => exact ⟨input, OCamlAdvanceCall.zero_returns state quantum input, related⟩
  | succ ticks ih =>
    cases related with
    | running table runner epochs source rank work invariant reached point completed =>
      obtain ⟨next, ticked, nextRelated⟩ := OCamlControllerTickInvariant.running_tick state program prepared table runner epochs quantum
        source rank work expected built invariant reached point completed
      obtain ⟨answer, later, answerRelated⟩ := ih next nextRelated
      exact ⟨answer, OCamlAdvanceStep.running_returns state _ _ _ epochs next answer ticks quantum ticked later, answerRelated⟩
    | complete table runner epochs invariant reached done terminal =>
      exact ⟨_, OCamlAdvanceStopped.returns state "MlComplete" _ _ _ epochs (ticks + 1) quantum (.inl rfl),
        .complete table runner epochs invariant reached done terminal⟩

theorem initial_related (program : OCaml.Program) (prepared : Prepared) (expected : OCaml.Result)
    (built : prepare program = .ok prepared) (evaluation : OCaml.Evaluates program [] program.entry expected) :
    Realizes program prepared expected (controller prepared provider "MlRunning"
      (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")) := by
  obtain ⟨work, completed⟩ := OCaml.evaluates_iff_completed_run.mp evaluation
  have restarted := control_point_epoch_restart program prepared provider built (initial_control_point program)
  exact .running provider _ (.symbol "LNil") (OCaml.begin program) 0 work
    (initial_source_epoch_invariant program prepared) restarted.1 restarted.2 completed

theorem begin_and_advance (state : State) (program : OCaml.Program) (prepared : Prepared) (expected : OCaml.Result)
    (ticks quantum : Nat) (built : prepare program = .ok prepared)
    (evaluation : OCaml.Evaluates program [] program.entry expected) :
    let startValue := controller prepared provider "MlRunning" (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")
    PureReturns runtime [] state (apply "gslt:ml:begin"
      [encoded (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern (initial program))]) state (encoded startValue) ∧
    ∃ answer, PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded startValue]) state (encoded answer) ∧
      Realizes program prepared expected answer := by
  exact ⟨OCamlBeginExecution.returns state program prepared built,
    advance_returns state program prepared expected ticks quantum _ built (initial_related program prepared expected built evaluation)⟩

#print axioms advance_returns
#print axioms initial_related
#print axioms begin_and_advance

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerAdvanceInvariant
