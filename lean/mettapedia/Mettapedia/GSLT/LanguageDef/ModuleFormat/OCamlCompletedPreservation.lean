import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceStepNormalized
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlAdministrativeNormalized
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlTerminalNoStep
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointTerminal
import Mettapedia.Languages.OCaml.CompletedProgress
import Mettapedia.Languages.OCaml.MachineCompleteness

/-! Every normalized step retains the result of an independent finite source
run. Source-step witnesses come from that actual run; administrative steps
preserve its current state. This is preservation, not target termination.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner

theorem normalized_step_preserves_completed_source (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) {source : OCaml.MachineState} {config target : Pattern}
    {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (point : ControlPoint program source config rank) (completed : OCaml.run program budget source = .complete result)
    (step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical config target) :
    ∃ next nextRank work, ControlPoint program next target nextRank ∧ OCaml.run program work next = .complete result := by
  by_cases zero : rank = 0
  · subst rank
    have encoded := rank_zero_encodes_source point
    rcases OCaml.completed_run_cases completed with stopped | ⟨next, work, sourceStep, later⟩
    · subst source
      exact False.elim (prepared_terminal_no_normalized_step program prepared table result config target built encoded step)
    · obtain ⟨nextRank, nextPoint⟩ := prepared_source_normalized_entry program prepared table source next config target
        built encoded sourceStep step
      exact ⟨next, nextRank, work, nextPoint, later⟩
  · have positive : 0 < rank := Nat.pos_of_ne_zero zero
    obtain ⟨nextRank, nextPoint, _⟩ := administrative_normalized_step program prepared table built invariant point positive step
    exact ⟨source, nextRank, budget, nextPoint, completed⟩

theorem runner_tick_preserves_completed_source (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table))
      GeneralOccurrenceSemantics.Receipt) (quantum : Nat) {source : OCaml.MachineState} {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (point : ControlPoint program source machine.state rank) (completed : OCaml.run program budget source = .complete result) :
    let next := Machine.tick (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine quantum
    ∃ source nextRank work, ControlPoint program source next.state nextRank ∧ OCaml.run program work source = .complete result := by
  rcases tick_commit_or_keep (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical)
    reached quantum with kept | committed
  · exact ⟨source, rank, budget, kept.1 ▸ point, completed⟩
  · obtain ⟨receipt, valid, next⟩ := committed
    have step : Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical
        machine.state (Complete.Normalized.commit (epochPlan prepared table) .canonical receipt.target) :=
      ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step _ _ _ valid, rfl⟩
    obtain ⟨source, nextRank, work, nextPoint, later⟩ :=
      normalized_step_preserves_completed_source program prepared table built invariant point completed step
    exact ⟨source, nextRank, work, next ▸ nextPoint, later⟩

theorem runner_advance_preserves_completed_source (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (ticks quantum : Nat)
    (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    {source : OCaml.MachineState} {rank budget : Nat} {result : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (point : ControlPoint program source machine.state rank) (completed : OCaml.run program budget source = .complete result) :
    let next := Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum machine
    ∃ source nextRank work, ControlPoint program source next.state nextRank ∧ OCaml.run program work source = .complete result := by
  induction ticks generalizing machine source rank budget with
  | zero => exact ⟨source, rank, budget, point, completed⟩
  | succ ticks ih =>
    obtain ⟨nextSource, nextRank, work, nextPoint, later⟩ :=
      runner_tick_preserves_completed_source program prepared table machine quantum built invariant reached point completed
    exact ih (Machine.tick _ machine quantum)
      (tick_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical) reached quantum)
      nextPoint later

theorem runner_terminal_result_unique (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (ticks quantum : Nat)
    (machine : Machine Pattern (Complete.Classes.State (epochPlan prepared table)) GeneralOccurrenceSemantics.Receipt)
    {source : OCaml.MachineState} {rank budget : Nat} {expected observed : OCaml.Result}
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) machine)
    (point : ControlPoint program source machine.state rank) (completed : OCaml.run program budget source = .complete expected)
    (terminal : state? (patterns program) (.halted observed) = some
      (Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum machine).state) :
    observed = expected := by
  obtain ⟨source, _, work, point, completed⟩ := runner_advance_preserves_completed_source program prepared table ticks quantum
    machine built invariant reached point completed
  have same := (control_point_terminal_readback program observed point terminal).2
  subst source
  cases work <;> exact OCaml.RunResult.complete.inj completed

theorem source_evaluation_controls_runner_result (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (ticks quantum : Nat) (expected observed : OCaml.Result)
    (built : prepare program = .ok prepared) (invariant : SourceProviderInvariant (patterns program) table)
    (evaluation : OCaml.Evaluates program [] program.entry expected)
    (terminal : state? (patterns program) (.halted observed) = some
      (Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum
        (Machine.begin (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) (initial program))).state) :
    observed = expected := by
  obtain ⟨budget, completed⟩ := OCaml.evaluates_iff_completed_run.mp evaluation
  exact runner_terminal_result_unique program prepared table ticks quantum _ built invariant
    (begin_reached _) (initial_control_point program) completed terminal

#print axioms normalized_step_preserves_completed_source
#print axioms runner_tick_preserves_completed_source
#print axioms runner_advance_preserves_completed_source
#print axioms runner_terminal_result_unique
#print axioms source_evaluation_controls_runner_result

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
