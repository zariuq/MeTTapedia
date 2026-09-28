import Mettapedia.Machines.InformationFlow.TimedSchedule

/-!
# Deadline admission and observable readiness

Equal publication times do not hide whether a private computation finished.
These controls execute the countdown worker from `TimedSchedule`, rather than
assuming a secret completion predicate. A public logical-step bound suffices
for readiness in this worker model. Real deadlines additionally require a
bound on the physical implementation of each reserved slot.
-/

namespace Mettapedia.Machines.InformationFlow.Deadline

open TimedSchedule TimedSchedule.Examples

def advance : Nat → Work → Work
  | 0, work => work
  | ticks + 1, work => advance ticks (countdown true work).1

theorem advance_remaining (ticks : Nat) (work : Work) :
    (advance ticks work).remaining = work.remaining - ticks := by
  induction ticks generalizing work with
  | zero => rfl
  | succ ticks ih =>
      rw [advance, ih]
      cases work with
      | mk remaining accumulated =>
        cases remaining <;> simp [countdown]

/-- The admission bound establishes readiness independently of the stored
accumulator, which may contain private data. -/
theorem ready_of_admitted (deadline : Nat) (work : Work)
    (admitted : work.remaining ≤ deadline) :
    (advance deadline work).remaining = 0 := by
  rw [advance_remaining]
  exact Nat.sub_eq_zero_of_le admitted

def publishAtDeadline (deadline : Nat) (work : Work) : Event Bool (Option Nat) :=
  let completed := advance deadline work
  ⟨deadline, false, if completed.remaining = 0 then some completed.accumulated else none⟩

def fast : Work := ⟨1, 259⟩
def slow : Work := ⟨20, 50⟩

/-- These private jobs compute the same final value. Publication at time 10
nevertheless reveals which one finished: `some 260` versus `none`. -/
theorem fixed_timestamp_can_leak_readiness :
    (advance 20 fast).accumulated = 260 ∧
    (advance 20 slow).accumulated = 260 ∧
    (publishAtDeadline 10 fast).time = (publishAtDeadline 10 slow).time ∧
    (publishAtDeadline 10 fast).value = some 260 ∧
    (publishAtDeadline 10 slow).value = none := by
  decide

/-- A common admitted deadline removes the readiness distinction for the two
jobs while still publishing their useful result. -/
theorem common_admitted_deadline_preserves_result :
    fast.remaining ≤ 20 ∧ slow.remaining ≤ 20 ∧
    publishAtDeadline 20 fast = publishAtDeadline 20 slow ∧
    (publishAtDeadline 20 fast).value = some 260 := by
  decide

end Mettapedia.Machines.InformationFlow.Deadline
