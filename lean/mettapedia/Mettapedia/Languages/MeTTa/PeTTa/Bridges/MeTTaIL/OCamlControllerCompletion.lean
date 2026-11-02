import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningPage
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlServiceProgress
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTerminalAdvance
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSearchEvent
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlNormalizedProgress

/-! Finite independent source evaluation reaches a complete loaded O0
controller result. Positive search quanta suffice: finite searches settle,
service installation enables a step, and committed transitions decrease
source work or administrative rank. Every page is an actual MeTTa call.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerCompletion

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant

theorem completes (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (runner : CompleteExecution.ClassMachine (epochPlan prepared table))
    (epochs : Term) (quantum : Nat) {source : OCaml.MachineState} {rank budget : Nat} {expected : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (point : ControlPoint program source runner.state rank) (completed : OCaml.run program budget source = .complete expected)
    (positive : 0 < quantum) :
    ∃ (ticks : Nat) (finalTable : GeneralPremise.ProviderSnapshot)
      (finalRunner : CompleteExecution.ClassMachine (epochPlan prepared finalTable)) (finalEpochs : Term),
      SourceEpochInvariant program prepared finalTable ∧
      Reached (Complete.Normalized.search (epochPlan prepared finalTable) [] (.base "MlConfig") .canonical) finalRunner ∧
      finalRunner.phase = .done ∧ state? (patterns program) (.halted expected) = some finalRunner.state ∧
      PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum,
        encoded (controller prepared table "MlRunning" runner epochs)]) state
        (encoded (controller prepared finalTable "MlComplete" finalRunner finalEpochs)) := by
  let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
  rcases epoch_runner_event program prepared table runner quantum built reached positive with
    ⟨pageTicks, before, done, same⟩ | ⟨pageTicks, receipt, before, valid, committed⟩
  · let stopped := Machine.advance search pageTicks quantum runner
    have stoppedReached := advance_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
      pageTicks quantum reached
    have stoppedPoint : ControlPoint program source stopped.state rank := same.symm ▸ point
    rcases settled_control_point_cases program prepared table stopped built invariant stoppedPoint completed stoppedReached done with request | terminal
    · obtain ⟨next, fresh, nextEpochs, nextInvariant, nextReached, freshPoint, enabled, serviced⟩ :=
        OCamlServiceProgress.supplies_enabled_step state program prepared table stopped epochs quantum built invariant
          stoppedReached done stoppedPoint request
      let nextSearch := Complete.Normalized.search (epochPlan prepared next) [] (.base "MlConfig") .canonical
      obtain ⟨followingPrefix, receipt, freshBefore, valid, committed⟩ :=
        epoch_enabled_event program prepared next fresh quantum built nextReached positive enabled
      let advanced := Machine.advance nextSearch followingPrefix quantum fresh
      have reacted : Complete.Normalized.NormalizedStep (epochPlan prepared next) [] (.base "MlConfig") .canonical fresh.state advanced.state := by
        refine ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid, ?_⟩
        change Complete.Normalized.commit (epochPlan prepared next) .canonical receipt.target =
          (Machine.advance nextSearch followingPrefix quantum fresh).state
        rw [committed]
        rfl
      obtain ⟨nextSource, nextRank, work, nextPoint, remaining, smaller⟩ :=
        normalized_step_progress program prepared next built nextInvariant.source freshPoint completed reacted
      have advancedReached := advance_reached (Complete.Normalized.search_lawful (epochPlan prepared next) [] (.base "MlConfig") .canonical)
        followingPrefix quantum nextReached
      obtain ⟨tailTicks, finalTable, finalRunner, finalEpochs, finalInvariant, finalReached, finalDone, finalState, following⟩ :=
        completes state program prepared next advanced nextEpochs quantum built nextInvariant advancedReached nextPoint remaining positive
      let answer := controller prepared finalTable "MlComplete" finalRunner finalEpochs
      have fromFresh := OCamlRunningPage.then_returns state program prepared next fresh nextEpochs answer followingPrefix tailTicks quantum
        built nextInvariant nextReached freshPoint completed freshBefore following
      have afterService := OCamlAdvanceStep.running_returns state
        (CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")) (OCamlEpochStandard.standard prepared)
        (CompleteExecution.classMachineTerm (epochPlan prepared table) stopped) epochs
        (controller prepared next "MlRunning" fresh nextEpochs) answer (followingPrefix + tailTicks) quantum serviced fromFresh
      have whole := OCamlRunningPage.then_returns state program prepared table runner epochs answer pageTicks
        (followingPrefix + tailTicks + 1) quantum built invariant reached point completed before afterService
      exact ⟨pageTicks + (followingPrefix + tailTicks + 1), finalTable, finalRunner, finalEpochs,
        finalInvariant, finalReached, finalDone, finalState, whole⟩
    · let answer := controller prepared table "MlComplete" stopped epochs
      have finished := OCamlSourceTerminalAdvance.returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared) epochs
        (patterns program) expected stopped 0 quantum stoppedReached done terminal
      have whole := OCamlRunningPage.then_returns state program prepared table runner epochs answer pageTicks 1 quantum built invariant
        reached point completed before finished
      exact ⟨pageTicks + 1, table, stopped, epochs, invariant, stoppedReached, done, terminal, whole⟩
  · let advanced := Machine.advance search pageTicks quantum runner
    have reacted : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical runner.state advanced.state := by
      refine ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid, ?_⟩
      change Complete.Normalized.commit (epochPlan prepared table) .canonical receipt.target =
        (Machine.advance search pageTicks quantum runner).state
      rw [committed]
      rfl
    obtain ⟨nextSource, nextRank, work, nextPoint, remaining, smaller⟩ :=
      normalized_step_progress program prepared table built invariant.source point completed reacted
    have advancedReached := advance_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
      pageTicks quantum reached
    obtain ⟨tailTicks, finalTable, finalRunner, finalEpochs, finalInvariant, finalReached, finalDone, finalState, following⟩ :=
      completes state program prepared table advanced epochs quantum built invariant advancedReached nextPoint remaining positive
    let answer := controller prepared finalTable "MlComplete" finalRunner finalEpochs
    have whole := OCamlRunningPage.then_returns state program prepared table runner epochs answer pageTicks tailTicks quantum
      built invariant reached point completed before following
    exact ⟨pageTicks + tailTicks, finalTable, finalRunner, finalEpochs, finalInvariant, finalReached, finalDone, finalState, whole⟩
termination_by (budget, rank)
decreasing_by
  all_goals
    rcases smaller with less | ⟨same, less⟩
    · exact Prod.Lex.left _ _ less
    · rw [same]
      exact Prod.Lex.right _ less

#print axioms completes

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerCompletion
