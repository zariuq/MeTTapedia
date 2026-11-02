import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSearchTermination
import Mettapedia.OSLF.MeTTaIL.Complete.NormalizedPhase
import Mettapedia.Machines.ResumableSearchRunnerPrefix

/-! A prepared O0 runner reaches a first stopping or committing event.
Every earlier prefix remains running, so the loaded controller can execute
the same page before its service dispatch becomes applicable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem epoch_runner_event (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (quantum : Nat) (built : prepare program = .ok prepared)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (positive : 0 < quantum) :
    let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
    (∃ ticks, RunningBefore search runner quantum ticks ∧ (Machine.advance search ticks quantum runner).phase = .done ∧
      (Machine.advance search ticks quantum runner).state = runner.state) ∨
    ∃ ticks, ∃ receipt : GeneralOccurrenceSemantics.Receipt, RunningBefore search runner quantum ticks ∧
      search.Valid runner.state receipt ∧ Machine.advance search ticks quantum runner =
        ⟨.running, search.target receipt, search.run (search.target receipt) 0,
          search.target receipt :: runner.states, receipt :: runner.receipts⟩ := by
  let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
  rcases Complete.Normalized.reached_phase (epochPlan prepared table) [] (.base "MlConfig") .canonical runner reached with running | done
  · rcases epoch_runner_stop_or_commit program prepared table runner quantum built reached running positive with
      ⟨ticks, stopped, same⟩ | ⟨ticks, receipt, valid, committed⟩
    · obtain ⟨first, before, stoppedFirst, stable⟩ := first_stopped_prefix search runner quantum ⟨ticks, stopped⟩
      have bounded : first ≤ ticks := by
        by_contra bigger
        exact stopped (before ticks (by omega))
      have sameFirst := stable ticks bounded
      have reachedFirst := advance_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
        first quantum reached
      have doneFirst : (Machine.advance search first quantum runner).phase = .done := by
        rcases Complete.Normalized.reached_phase (epochPlan prepared table) [] (.base "MlConfig") .canonical _ reachedFirst with running | done
        · exact False.elim (stoppedFirst running)
        · exact done
      exact .inl ⟨first, before, doneFirst, (congrArg Machine.state sameFirst).symm.trans same⟩
    · have before := running_before_of_running_after search runner quantum ticks (by rw [committed])
      exact .inr ⟨ticks, receipt, before, valid, committed⟩
  · exact .inl ⟨0, by intro earlier impossible; omega, done, rfl⟩

theorem epoch_enabled_event (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot)
    (runner : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    (quantum : Nat) (built : prepare program = .ok prepared)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (positive : 0 < quantum)
    (enabled : ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step runner.state target) :
    let search := Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical
    ∃ ticks, ∃ receipt : GeneralOccurrenceSemantics.Receipt, RunningBefore search runner quantum ticks ∧
      search.Valid runner.state receipt ∧ Machine.advance search ticks quantum runner =
        ⟨.running, search.target receipt, search.run (search.target receipt) 0,
          search.target receipt :: runner.states, receipt :: runner.receipts⟩ := by
  rcases epoch_runner_event program prepared table runner quantum built reached positive with
    ⟨ticks, _, done, same⟩ | committed
  · obtain ⟨target, step⟩ := enabled
    have checked : Complete.Predecessors.equationsChecked (epochPlan prepared table) = true := by
      rw [Complete.Predecessors.equationsChecked, epoch_compiled_equations_empty program prepared table built]
      rfl
    have later := advance_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
      ticks quantum reached
    exact False.elim (Complete.Normalized.done_no_step (epochPlan prepared table) [] (.base "MlConfig") checked later done target
      (same.symm ▸ step))
  · exact committed

#print axioms epoch_runner_event
#print axioms epoch_enabled_event

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
