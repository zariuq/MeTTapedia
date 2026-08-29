import Mettapedia.GSLT.Core.AgeProtectedSchedule
import Mettapedia.GSLT.Core.ResourceBackpressureAdmission

/-!
# Resource backpressure over the existing age-protected scheduler

Backpressure and fairness use one queue law.  The canonical resource policy
admits a finite prefix of `QueueDiscipline.breadthFirst.integrate pending
generated`; it does not maintain a second ordering beside the scheduler's
FIFO age lane.

Freshly generated occurrences are appended after existing work, so they do
not increase an existing occurrence's finite age debt.  Finite capacity then
either admits that exact occurrence or retains it in the exact residual.  The
existing `AgeProtectedSchedule` theorem supplies unbounded eventual selection
for a live occurrence; resource admission does not re-prove or weaken it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ResourceBackpressureScheduling

open Mettapedia.GSLT.Core.AgeProtectedSchedule
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.ResourceBackpressureAdmission
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

universe uItem uAnswer

/-- Resource admission is a finite prefix of the scheduler's authored FIFO
integration of old pending work with newly generated occurrences. -/
def fifoAdmission {Item : Type uItem} (capacity : Nat)
    (pending generated : List Item) :
    Admission Nat unitDemand capacity capacity
      (QueueDiscipline.breadthFirst.integrate pending generated) :=
  prefixAdmission capacity
    (QueueDiscipline.breadthFirst.integrate pending generated)

@[simp] theorem fifoAdmission_admitted {Item : Type uItem}
    (capacity : Nat) (pending generated : List Item) :
    (fifoAdmission capacity pending generated).admitted =
      (pending ++ generated).take capacity :=
  rfl

@[simp] theorem fifoAdmission_pending {Item : Type uItem}
    (capacity : Nat) (pending generated : List Item) :
    (fifoAdmission capacity pending generated).pending =
      (pending ++ generated).drop capacity :=
  rfl

/-- The resource decision partitions the same occurrence bag represented by
the FIFO age lane. -/
theorem fifoAdmission_occurrence_partition {Item : Type uItem}
    (capacity : Nat) (pending generated : List Item) :
    ((fifoAdmission capacity pending generated).admitted : Multiset Item) +
        ((fifoAdmission capacity pending generated).pending : Multiset Item) =
      ((QueueDiscipline.breadthFirst.integrate pending generated) :
        Multiset Item) :=
  (fifoAdmission capacity pending generated).occurrencePartition

/-- Appending fresh work behind an existing occurrence does not change the
number of predecessors protecting it from starvation. -/
theorem generated_work_does_not_increase_existing_ageDebt
    {Item : Type uItem} [DecidableEq Item]
    (pending generated : List Item) {target : Item}
    (targetPending : target ∈ pending) :
    QueueDiscipline.ageDebt
        (QueueDiscipline.breadthFirst.integrate pending generated) target =
      QueueDiscipline.ageDebt pending target := by
  change (pending ++ generated).idxOf target = pending.idxOf target
  exact List.idxOf_append_of_mem targetPending

/-- An existing occurrence lies in the finite admitted prefix exactly when
its pre-arrival FIFO debt fits within the available capacity. -/
theorem existing_admitted_iff_ageDebt_lt_capacity
    {Item : Type uItem} [DecidableEq Item]
    (capacity : Nat) (pending generated : List Item) {target : Item}
    (targetPending : target ∈ pending) :
    target ∈ (fifoAdmission capacity pending generated).admitted ↔
      QueueDiscipline.ageDebt pending target < capacity := by
  change target ∈ (pending ++ generated).take capacity ↔
    pending.idxOf target < capacity
  rw [List.mem_take_iff_idxOf_lt (by simp [targetPending])]
  rw [List.idxOf_append_of_mem targetPending]

/-- Finite resource pressure cannot erase old work: the exact occurrence is
either admitted now or retained in the residual queue. -/
theorem existing_admitted_or_pending
    {Item : Type uItem} (capacity : Nat)
    (pending generated : List Item) {target : Item}
    (targetPending : target ∈ pending) :
    target ∈ (fifoAdmission capacity pending generated).admitted ∨
      target ∈ (fifoAdmission capacity pending generated).pending := by
  have targetOffered : target ∈ pending ++ generated := by
    simp [targetPending]
  rw [← List.take_append_drop capacity (pending ++ generated)] at targetOffered
  change target ∈ (pending ++ generated).take capacity ∨
    target ∈ (pending ++ generated).drop capacity
  exact List.mem_append.mp targetOffered

/-- The existing age-protected theorem applies to the same FIFO integration:
an occurrence pending before an arrival batch is eventually selected, even
when the branching system continues to generate new work. -/
theorem existing_eventually_selected
    {Item : Type uItem} {Answer : Type uAnswer} {count : Nat}
    [NeZero count] [DecidableEq Item]
    (schedule : AgeProtectedSchedule.Spec Item count)
    (system : BranchingSystem Item Answer)
    (pending generated : List Item) (start : Fin count)
    {target : Item} (targetPending : target ∈ pending) :
    ∃ fuel,
      target ∈
        (PortfolioSnapshot.run system schedule.disciplines fuel
          (schedule.initial (Answer := Answer) (pending ++ generated)
            start)).selections := by
  apply schedule.eventually_selects_root system (pending ++ generated) start
  simp [targetPending]

/-! ## Positive and negative queue controls -/

namespace Canary

theorem fifo_arrival_preserves_existing_debt :
    QueueDiscipline.ageDebt
        (QueueDiscipline.breadthFirst.integrate [1] [2]) (1 : Nat) =
      QueueDiscipline.ageDebt [1] 1 :=
  generated_work_does_not_increase_existing_ageDebt [1] [2] (by simp)

/-- An occurrence-preserving priority discipline may still put fresh work in
front.  Such a lane cannot replace the independent FIFO fairness duty. -/
theorem depth_first_arrival_can_increase_existing_debt :
    QueueDiscipline.ageDebt
        (QueueDiscipline.depthFirst.integrate [1] [2]) (1 : Nat) >
      QueueDiscipline.ageDebt [1] 1 :=
  QueueDiscipline.depthFirst_can_increase_ageDebt

theorem zero_capacity_retains_existing_work :
    (1 : Nat) ∈ (fifoAdmission 0 [1] [2]).pending := by
  decide

end Canary

#print axioms fifoAdmission_occurrence_partition
#print axioms generated_work_does_not_increase_existing_ageDebt
#print axioms existing_admitted_iff_ageDebt_lt_capacity
#print axioms existing_admitted_or_pending
#print axioms existing_eventually_selected
#print axioms Canary.fifo_arrival_preserves_existing_debt
#print axioms Canary.depth_first_arrival_can_increase_existing_debt
#print axioms Canary.zero_capacity_retains_existing_work

end Mettapedia.GSLT.Core.ResourceBackpressureScheduling
