import Mettapedia.Machines.ScheduledRun.Finite

/-!
# Scheduled-run liveness controls from the shared runner fixtures

`waitNext` represents `observe_run_wait.tcalc` and
`observe_run_rotating_wakes.tcalc`; `cycleNext` represents
`observe_run_rotating_cycle.tcalc`; `staleNext` represents
`observe_run_rotating_period.tcalc`. The dining-philosophers fixture
`observe_run_rotating.tcalc` exercises the same schedule choice in a larger
language state space; no language-to-graph decoding is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun.Controls

inductive State where
  | wait
  | wake
  deriving DecidableEq, Repr

open State

instance : Fintype State := ⟨{wait, wake}, fun state => by cases state <;> simp⟩

theorem second_pick_distinguishes_the_schedules :
    canonical.pick 1 2 = 0 ∧ rotating.pick 1 2 = 1 := by decide

def waitNext : State → List State
  | wait => [wait, wake]
  | wake => []

theorem rotating_revisit_trace : (List.range 4).map (run waitNext rotating wait) =
    [some wait, some wait, some wake, none] := by decide

theorem rotating_revisit_not_infinite :
    run waitNext rotating wait 0 = run waitNext rotating wait 1 ∧
      EndsAt waitNext rotating wait 2 ∧ ¬ Nonterminating waitNext rotating wait := by
  have ended : EndsAt waitNext rotating wait 2 := ⟨wake, by decide, rfl⟩
  exact ⟨by decide, ended, ended_not_nonterminating waitNext rotating wait ended⟩

theorem canonical_waits_forever :
    Nonterminating waitNext canonical wait ∧ PeriodicFrom waitNext canonical wait 0 1 :=
  canonical_return_periodic waitNext wait (first := 0) (last := 1) (by decide) wait (by decide) (by decide)

def cycleNext : State → List State
  | wait => [wait, wake]
  | wake => [wait]

theorem rotating_cycle_trace : (List.range 6).map (run cycleNext rotating wait) =
    [some wait, some wait, some wake, some wait, some wake, some wait] := by decide

theorem cycle_segment_period : segmentPeriod cycleNext rotating wait 1 3 = 2 := by decide

theorem rotating_cycle_is_infinite :
    Nonterminating cycleNext rotating wait ∧ PeriodicFrom cycleNext rotating wait 1 2 := by
  apply rotating_return_periodic cycleNext wait (first := 1) (last := 3) (by decide) wait
    (by decide) (by decide)
  intro turn lower upper state present
  simpa only [cycle_segment_period] using
    arity_dvd_segmentPeriod cycleNext rotating wait ⟨lower, upper⟩ present

theorem rotating_cycle_lcm_certificate :
    Nonterminating cycleNext rotating wait ∧ PeriodicFrom cycleNext rotating wait 1 2 := by
  apply return_mod_lcm_periodic cycleNext wait (first := 1) (last := 3) (by decide) wait
    (by decide) (by decide)
  rw [cycle_segment_period]
  decide

theorem finite_infinite_cycle_is_detected :
    ∃ first last state, first < last ∧ run cycleNext rotating wait first = some state ∧
      run cycleNext rotating wait last = some state ∧
      Nat.ModEq (visitedPeriod cycleNext rotating wait (Set.toFinite _)) first last :=
  finite_infinite_detected cycleNext wait (Set.toFinite _) rotating_cycle_is_infinite.1

def staleNext : Nat → List Nat
  | 1 => [2]
  | 2 => [3]
  | 3 => [4]
  | 4 => [0, 2]
  | _ => []

theorem stale_phase_trace : (List.range 9).map (run staleNext rotating 1) =
    [some 1, some 2, some 3, some 4, some 2, some 3, some 4, some 0, none] := by decide

theorem stale_periods : segmentPeriod staleNext rotating 1 0 3 = 1 ∧
    segmentPeriod staleNext rotating 1 0 4 = 2 := by decide

theorem stale_phase_not_infinite :
    run staleNext rotating 1 1 = run staleNext rotating 1 4 ∧
      1 % 1 = 4 % 1 ∧ EndsAt staleNext rotating 1 7 ∧ ¬ Nonterminating staleNext rotating 1 := by
  have ended : EndsAt staleNext rotating 1 7 := ⟨0, by decide, rfl⟩
  exact ⟨by decide, by decide, ended, ended_not_nonterminating staleNext rotating 1 ended⟩

theorem residues_from_different_epochs_are_not_comparable :
    1 % 1 = 4 % 2 ∧ ¬ Nat.ModEq 2 1 4 := by decide

def noNext (_ : Unit) : List Unit := []

theorem stopped_equality_is_not_a_live_return :
    run noNext canonical () 1 = run noNext canonical () 2 ∧
      ¬ Nonterminating noNext canonical () := by
  exact ⟨by decide, ended_not_nonterminating noNext canonical () (turn := 0) ⟨(), rfl, rfl⟩⟩

end Mettapedia.Machines.ScheduledRun.Controls
