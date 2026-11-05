import Mettapedia.Machines.Resources.Jobs

/-!
# Ranked persistent-job waits

A registered wake source is an obligation, not a proof of eventual progress.
When one persistent job depends on another job, a strict rank supplies a small,
compositional rule which refuses circular waits. External wake sources do not
need a job rank; their liveness remains a stated scheduler/service assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.JobSchedules

open Mettapedia.Machines.Resources

structure Order where
  rank : JobId → Nat

/-- `waiter` may suspend for `source` only when dependency rank decreases. -/
def Permitted (order : Order) (waiter source : JobId) : Prop :=
  order.rank source < order.rank waiter

/-- Dependency arrows point from a source toward the job waiting on it. -/
def Dependency (order : Order) (source waiter : JobId) : Prop :=
  Permitted order waiter source

theorem dependency_path_strict (order : Order) {source waiter : JobId}
    (path : Relation.TransGen (Dependency order) source waiter) :
    order.rank source < order.rank waiter := by
  induction path with
  | single edge => exact edge
  | tail _ edge ih => exact Nat.lt_trans ih edge

theorem no_dependency_cycle (order : Order) (job : JobId) :
    ¬ Relation.TransGen (Dependency order) job job := by
  intro cycle
  exact Nat.lt_irrefl _ (dependency_path_strict order cycle)

theorem reverse_wait_refused (order : Order) (first second : JobId)
    (forward : Permitted order second first) : ¬ Permitted order first second := by
  exact Nat.not_lt_of_ge (Nat.le_of_lt forward)

theorem self_wait_refused (order : Order) (job : JobId) : ¬ Permitted order job job :=
  Nat.lt_irrefl _

namespace Controls

def order : Order := ⟨fun job => job.number⟩
def refresh : JobId := ⟨3, 1⟩
def presentation : JobId := ⟨3, 2⟩

theorem presentation_may_wait_for_refresh : Permitted order presentation refresh := by
  simp [Permitted, order, refresh, presentation]
theorem refresh_cannot_wait_for_presentation : ¬ Permitted order refresh presentation := by
  simp [Permitted, order, refresh, presentation]
theorem circular_pair_refused :
    ¬ (Permitted order presentation refresh ∧ Permitted order refresh presentation) := by
  simp [Permitted, order, refresh, presentation]

end Controls

#print axioms dependency_path_strict
#print axioms no_dependency_cycle

end Mettapedia.Machines.Resources.JobSchedules
