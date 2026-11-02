import Mettapedia.Machines.ScopedCommitCursor

/-! # Selection, irreversible effects and retained-continuation controls -/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommitCursor.Controls

open ScopedCommit
open Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor

def answer (value event : Nat) : Body Nat (List Nat) :=
  .effect (fun _ world => (value, world ++ [event])) .done

def program : Body Nat (List Nat) := .choice (answer 1 10) (answer 2 20)

def selected (demand : Nat) :=
  readout pull (execute demand (stream program 0) []).2

theorem zero_demand_runs_no_effect :
    (selected 0).answers = [] ∧ (selected 0).world = [] := by
  decide +kernel

theorem one_answer_stops_before_the_second_effect :
    (selected 1).answers = [1] ∧ (selected 1).world = [10] ∧
      (selected 1).stop = .limit := by
  decide +kernel

theorem two_answers_keep_their_effect_order :
    (selected 2).answers = [1, 2] ∧ (selected 2).world = [10, 20] := by
  decide +kernel

theorem resume_runs_only_the_remaining_effect :
    resume (sourceView (selected 1)).2.2 (selected 1).world = ([2], [10, 20]) := by
  decide +kernel

theorem restart_is_not_resume :
    run program 0 (selected 1).world = ([1, 2], [10, 10, 20]) := by
  decide +kernel

/-- The failing branch's local binding is abandoned, but its world effect
remains visible when the next branch succeeds. -/
def failingEffect : Body Nat (List Nat) :=
  .choice (.effect (fun _ world => (99, world ++ [30])) .fail) (answer 2 20)

theorem local_failure_does_not_undo_world_effects :
    run failingEffect 0 [] = ([2], [30, 20]) := by
  decide +kernel

theorem once_keeps_the_first_world_and_discards_later_search :
    run (once program) 0 [] = ([1], [10]) := by
  decide +kernel

theorem changed_world_is_refused :
    (resumeIfCurrent (sourceView (selected 1)) [10, 99]).2 = none := by
  rfl

end Mettapedia.Machines.ScopedCommitCursor.Controls
