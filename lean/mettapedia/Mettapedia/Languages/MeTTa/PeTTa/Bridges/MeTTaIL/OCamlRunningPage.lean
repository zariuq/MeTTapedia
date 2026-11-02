import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerAdvanceInvariant
import Mettapedia.Machines.ResumableSearchRunnerPrefix

/-! Running model prefixes execute as actual loaded controller pages.
An arbitrary subsequent page can be appended, including a service restart
or completion; no stopped model tick is mistaken for controller dispatch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningPage

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant

theorem then_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs answer : Term) (ticks laterTicks quantum : Nat) {source : OCaml.MachineState} {rank budget : Nat} {expected : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (point : ControlPoint program source runner.state rank) (completed : OCaml.run program budget source = .complete expected)
    (before : RunningBefore (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum ticks)
    (later : PureReturns runtime [] state (apply "gslt:ml:advance" [number laterTicks, number quantum,
      encoded (controller prepared table "MlRunning"
        (Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum runner) epochs)])
      state (encoded answer)) :
    PureReturns runtime [] state (apply "gslt:ml:advance" [number (ticks + laterTicks), number quantum,
      encoded (controller prepared table "MlRunning" runner epochs)]) state (encoded answer) := by
  induction ticks generalizing runner source rank budget with
  | zero => simpa only [Nat.zero_add, Machine.advance] using later
  | succ ticks ih =>
    have running : runner.phase = .running := before 0 (Nat.zero_lt_succ _)
    have ticked := OCamlRunningTick.returns state prepared table runner epochs quantum (invariant.complete built) invariant.finite
      reached (control_point_epoch_checked program prepared table built point).2 running
    obtain ⟨nextSource, nextRank, work, nextPoint, remaining⟩ := runner_tick_preserves_completed_source program prepared table runner quantum
      built invariant.source reached point completed
    have nextReached := tick_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical) reached quantum
    have nextBefore : RunningBefore (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical)
        (Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum) quantum ticks := by
      intro earlier inside
      exact before (earlier + 1) (by omega)
    have following := ih (runner := Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum) nextReached nextPoint remaining nextBefore later
    simpa only [Nat.succ_add, Nat.add_one, controller] using OCamlAdvanceStep.running_returns state
      (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
      (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs
      (controller prepared table "MlRunning" (Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum) epochs) answer (ticks + laterTicks) quantum ticked following

theorem returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs : Term) (ticks quantum : Nat) {source : OCaml.MachineState} {rank budget : Nat} {expected : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (point : ControlPoint program source runner.state rank) (completed : OCaml.run program budget source = .complete expected)
    (before : RunningBefore (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum ticks) :
    PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum,
      encoded (controller prepared table "MlRunning" runner epochs)]) state
      (encoded (controller prepared table "MlRunning"
        (Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum runner) epochs)) := by
  have computed := then_returns state program prepared table runner epochs _ ticks 0 quantum built invariant reached point completed before
    (OCamlAdvanceCall.zero_returns state quantum _)
  simpa only [Nat.add_zero] using computed

#print axioms then_returns
#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningPage
