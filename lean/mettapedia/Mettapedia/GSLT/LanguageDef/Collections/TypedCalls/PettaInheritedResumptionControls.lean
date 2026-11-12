import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckpointControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-!
# Composed controller controls over independent source execution proofs

The source fixtures already have kernel-checked full named-call results. These
controls transport those independent results through the actual region machine,
including retained guard resumption. The larger collapse/commit reduction suite
is separate; no result from its diagnostic evaluation is assumed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedResumptionControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open PettaOccurrenceOverlay
open PettaCheckpointFixtures (num text services initial suspended)

def observation (operations : Services Unit) (bad : Bool) (source : State Unit) :
    Option (List Atom × List Atom) :=
  let result := (PettaInheritedMachine.machine operations (PettaCheckpointFixtures.program bad)).run
    100 (.inl (PettaInheritedContext.nest source))
  PettaInheritedFixtures.observe (result.1, PettaInheritedMachine.outcome result.2)

theorem observation_eq_source (operations : Services Unit) (bad : Bool) (source : State Unit) :
    observation operations bad source = PettaCheckpointFixtures.observation operations bad source := by
  exact congrArg PettaInheritedFixtures.observe
    (PettaInheritedMachine.run_in_host operations (PettaCheckpointFixtures.program bad) 100 source)

theorem full_named_controller_returns_the_checked_result :
    observation services false (initial false) = some ([num 4], [text "before", text "body"]) := by
  rw [observation_eq_source]
  exact PettaCheckpointControls.full_named_entry_returns_one_guarded_answer

theorem controller_refuses_the_wrong_range_after_the_effect :
    observation services true (initial true) = some ([], [text "before", text "body"]) := by
  rw [observation_eq_source]
  exact PettaCheckpointControls.bad_result_is_refused_after_its_effect

theorem lying_about_the_range_changes_the_controller_answer :
    observation PettaCheckpointFixtures.erasedRange true (initial true) =
      some ([text "wrong"], [text "before", text "body"]) := by
  rw [observation_eq_source]
  exact PettaCheckpointControls.erasing_the_declared_range_changes_the_full_named_call

def resumed : Option (List Atom × List Atom) := do
  let reached ← suspended
  observation services false reached

theorem controller_resumes_the_actual_guard_without_replay :
    resumed = some ([num 4], [text "before", text "body"]) := by
  have same : resumed = PettaCheckpointFixtures.resumed := by
    simp only [resumed, observation_eq_source, PettaCheckpointFixtures.resumed]
  rw [same]
  exact PettaCheckpointControls.resuming_the_actual_guard_does_not_replay_the_body

def replayed : Option (List Atom × List Atom) := do
  let reached ← suspended
  let start := initial false
  observation services false (start.1, {start.2 with world := reached.2.world})

theorem restarting_the_controller_repeats_the_body_effect :
    replayed = some ([num 4], [text "before", text "body", text "body"]) := by
  have same : replayed = PettaCheckpointFixtures.replayed := by
    simp only [replayed, observation_eq_source, PettaCheckpointFixtures.replayed]
  rw [same]
  exact PettaCheckpointControls.restarting_the_call_replays_the_completed_effect

theorem retained_guard_is_an_inherited_boundary :
    suspended.map (fun reached => PettaInheritedContext.boundary (PettaInheritedContext.nest reached)) = some true := by cbv

theorem real_collection_entry_retains_its_actual_depth :
    PettaInheritedFixtures.readyView true false = some (2, 2, true, true) := by cbv

def missing_guard_packets : Option (List Atom) := do
  let reached ← suspended
  let result := (PettaInheritedMachine.machine PettaCheckpointFixtures.missingResult
    (PettaCheckpointFixtures.program false)).run 1 (.inl (PettaInheritedContext.nest reached))
  pure (result.1.map (·.value))

def omitted_handoff_packets : Option (List Atom) := do
  let reached ← suspended
  let result := (PettaOccurrenceOverlay.machine
    (PettaInheritedContext.services PettaCheckpointFixtures.missingResult) .eagerValue
    (PettaCheckpointFixtures.program false)).run 1 (PettaInheritedContext.nest reached)
  pure (result.1.map (·.value))

theorem unavailable_inherited_guard_publishes_nothing : missing_guard_packets = some [] := by cbv

theorem omitting_the_inherited_guard_publishes_without_authority :
    omitted_handoff_packets = some [num 4] := by cbv

theorem reflexive_open_type_equation_is_satisfiable :
    TypeEquationSolver.check
      [((Ty.app [.sym "List", .var 0], Ty.app [.sym "List", .var 0]) : Eqn Nat)] = true := by cbv

theorem different_scalar_names_remain_inconsistent :
    TypeEquationSolver.check [((Ty.sym "Number", Ty.sym "String") : Eqn Nat)] = false := by cbv

theorem dropping_a_reflexive_equation_does_not_erase_the_conflict :
    TypeEquationSolver.check
      [((Ty.var 0, Ty.var 0) : Eqn Nat), (.sym "Number", .sym "String")] = false := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedResumptionControls
