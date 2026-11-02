import Mettapedia.Machines.ResumableSearchRunner
import Mathlib.Data.Nat.Find

/-! A running prefix of a resumable search can be replayed through a host
controller without invoking its stopped-state dispatch early. This module
only describes existing runner pages; it adds no execution machine.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumableSearchRunner

variable {σ Run Receipt : Type} (S : Search σ Run Receipt)

def RunningBefore (machine : Machine σ Run Receipt) (quantum ticks : Nat) : Prop :=
  ∀ earlier < ticks, (Machine.advance S earlier quantum machine).phase = .running

theorem running_before_of_running_after (machine : Machine σ Run Receipt) (quantum ticks : Nat)
    (running : (Machine.advance S ticks quantum machine).phase = .running) : RunningBefore S machine quantum ticks := by
  intro earlier before
  by_contra stopped
  have stays := advance_stopped (S := S) stopped quantum (ticks - earlier)
  have split := Machine.advance_add S earlier (ticks - earlier) quantum machine
  rw [Nat.add_sub_of_le (Nat.le_of_lt before), stays] at split
  exact stopped (split.symm ▸ running)

theorem first_stopped_prefix (machine : Machine σ Run Receipt) (quantum : Nat)
    (stops : ∃ ticks, (Machine.advance S ticks quantum machine).phase ≠ .running) :
    ∃ ticks, RunningBefore S machine quantum ticks ∧
      (Machine.advance S ticks quantum machine).phase ≠ .running ∧
      ∀ later, ticks ≤ later → Machine.advance S later quantum machine = Machine.advance S ticks quantum machine := by
  classical
  let ticks := Nat.find stops
  have stopped : (Machine.advance S ticks quantum machine).phase ≠ .running := Nat.find_spec stops
  refine ⟨ticks, ?_, stopped, ?_⟩
  · intro earlier before
    exact Classical.not_not.mp (Nat.find_min stops before)
  · intro later after
    have stays := advance_stopped (S := S) stopped quantum (later - ticks)
    have split := Machine.advance_add S ticks (later - ticks) quantum machine
    rw [Nat.add_sub_of_le after, stays] at split
    exact split

#print axioms running_before_of_running_after
#print axioms first_stopped_prefix

end Mettapedia.Machines.ResumableSearchRunner
