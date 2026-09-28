import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Collection headroom and the cost of repeated full tracing

An executable threshold policy allocates one short-lived cell at each request
and collects after `headroom` such allocations. A separate transition relation
allows arbitrary collection times, subject to the same capacity. Every
collection discards the accumulated garbage and traverses the persistent live
graph. The threshold policy attains the minimum number of full collections
among these schedules at every request boundary where garbage is strictly
below the threshold.

The meter counts visits to that fixed live graph. It excludes root scanning,
dead-cell sweeping, allocator costs and cache behavior. Reference counting,
regions, generational collectors and changing live graphs are different
comparison classes. In particular a retained-space minimum does not imply a
minimum tracing cost: the controls give arbitrarily different work with the
same empty garbage at the end.

The policy is defined for every finite prefix of an ongoing allocation stream;
no bound is imposed on the stream's eventual length or the heap's address type.
This scheduling model does not itself implement allocation or heap tracing.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceCollectionSchedule

structure State where
  allocated : Nat
  garbage : Nat
  collections : Nat
  deriving DecidableEq, Repr

def start : State := ⟨0, 0, 0⟩

def allocate (s : State) : State :=
  { s with allocated := s.allocated + 1, garbage := s.garbage + 1 }

def collect (s : State) : State :=
  { s with garbage := 0, collections := s.collections + 1 }

/-- Capacity is checked before allocation. A collection can happen earlier
than necessary, including when it reclaims nothing. -/
inductive Trace (headroom : Nat) : State → Prop
  | start : Trace headroom start
  | allocate {s : State} : Trace headroom s → s.garbage < headroom →
      Trace headroom (allocate s)
  | collect {s : State} : Trace headroom s → Trace headroom (collect s)

/-- A request performs its allocation, then collects exactly when the
threshold has been reached. With zero headroom it always collects; capacity
and optimality theorems require a positive threshold. -/
def step (headroom : Nat) (s : State) : State :=
  let next := allocate s
  if next.garbage < headroom then next else collect next

def run (headroom : Nat) : Nat → State
  | 0 => start
  | n + 1 => step headroom (run headroom n)

theorem trace_capacity {headroom : Nat} {s : State} (trace : Trace headroom s) :
    s.garbage ≤ headroom := by
  induction trace with
  | start => simp [start]
  | allocate _ room _ => simp only [allocate]; omega
  | collect => simp [collect]

/-- No schedule in this class can reclaim more than one threshold's worth
per collection. This is derived from the capacity rule, not stipulated as a
cost or final-run premise. -/
theorem trace_allocation_bound {headroom : Nat} {s : State}
    (trace : Trace headroom s) :
    s.allocated ≤ headroom * s.collections + s.garbage := by
  induction trace with
  | start => simp [start]
  | @allocate s prior room ih =>
      simp only [allocate]
      omega
  | @collect s prior ih =>
      have bound := trace_capacity prior
      simp only [collect, Nat.mul_add, Nat.mul_one, Nat.add_zero]
      omega

theorem run_allocated (headroom n : Nat) : (run headroom n).allocated = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, step]
      split <;> simp [allocate, collect, ih]

theorem run_garbage_lt {headroom : Nat} (positive : 0 < headroom) (n : Nat) :
    (run headroom n).garbage < headroom := by
  cases n with
  | zero => exact positive
  | succ n =>
      simp only [run, step]
      split
      next below => exact below
      next _ => simpa only [collect] using positive

theorem run_trace {headroom : Nat} (positive : 0 < headroom) (n : Nat) :
    Trace headroom (run headroom n) := by
  induction n with
  | zero => exact .start
  | succ n ih =>
      have next := Trace.allocate ih (run_garbage_lt positive n)
      simp only [run, step]
      split
      · exact next
      · exact .collect next

/-- Every collection of the threshold algorithm reclaims exactly one full
batch; the residual allocation debt is retained at pauses. -/
theorem run_accounting {headroom : Nat} (positive : 0 < headroom) (n : Nat) :
    headroom * (run headroom n).collections + (run headroom n).garbage = n := by
  induction n with
  | zero => simp [run, start]
  | succ n ih =>
      have below := run_garbage_lt positive n
      simp only [run, step]
      split
      · simp only [allocate]
        omega
      next full =>
        have batch : (run headroom n).garbage + 1 = headroom := by
          change ¬ (run headroom n).garbage + 1 < headroom at full
          omega
        simp only [collect, allocate, Nat.mul_add, Nat.mul_one, Nat.add_zero]
        omega

theorem run_collections {headroom : Nat} (positive : 0 < headroom) (n : Nat) :
    (run headroom n).collections = n / headroom := by
  have account := run_accounting positive n
  have below := run_garbage_lt positive n
  conv_rhs => rw [← account]
  simp [Nat.add_div, Nat.mul_mod_right, Nat.mod_eq_of_lt below,
    Nat.div_eq_of_lt below, positive, Nat.not_le_of_gt below]

theorem run_garbage {headroom : Nat} (positive : 0 < headroom) (n : Nat) :
    (run headroom n).garbage = n % headroom := by
  have account := run_accounting positive n
  have below := run_garbage_lt positive n
  conv_rhs => rw [← account]
  simp [Nat.add_mod, Nat.mod_eq_of_lt below]

/-- A lower bound over all legal schedules, including ones which collect
prematurely. The final strict bound is the same request-boundary convention
as the threshold algorithm. -/
theorem schedule_lower_bound {headroom : Nat} (positive : 0 < headroom)
    {s : State} (trace : Trace headroom s) (settled : s.garbage < headroom) :
    s.allocated / headroom ≤ s.collections := by
  have bound := trace_allocation_bound trace
  have strict : s.allocated < (s.collections + 1) * headroom := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm s.collections headroom]
    omega
  have := (Nat.div_lt_iff_lt_mul positive).mpr strict
  omega

theorem threshold_minimizes_collections {headroom : Nat} (positive : 0 < headroom)
    {s : State} (trace : Trace headroom s) (settled : s.garbage < headroom) :
    (run headroom s.allocated).collections ≤ s.collections := by
  rw [run_collections positive]
  exact schedule_lower_bound positive trace settled

/-- The persistent live graph can have arbitrary size and sharing. Its
per-collection visit count is a separate parameter from allocation headroom. -/
def tracingWork (liveVisits : Nat) (s : State) : Nat := liveVisits * s.collections

theorem exact_work {headroom : Nat} (positive : 0 < headroom) (liveVisits n : Nat) :
    tracingWork liveVisits (run headroom n) = liveVisits * (n / headroom) := by
  simp only [tracingWork, run_collections positive]

theorem threshold_minimizes_work {headroom : Nat} (positive : 0 < headroom)
    (liveVisits : Nat) {s : State} (trace : Trace headroom s)
    (settled : s.garbage < headroom) :
    tracingWork liveVisits (run headroom s.allocated) ≤ tracingWork liveVisits s :=
  Nat.mul_le_mul_left liveVisits (threshold_minimizes_collections positive trace settled)

/-- Multiplying by headroom avoids rounding and expresses an exact amortized
upper bound on every finite prefix, rather than only on completed epochs. -/
theorem amortized_work {headroom : Nat} (positive : 0 < headroom) (liveVisits n : Nat) :
    headroom * tracingWork liveVisits (run headroom n) ≤ liveVisits * n := by
  have account := run_accounting positive n
  have debit : headroom * (run headroom n).collections ≤ n := by omega
  simpa only [tracingWork, Nat.mul_left_comm headroom liveVisits] using
    Nat.mul_le_mul_left liveVisits debit

/-- Retained garbage stays bounded even when the stream of requests has no
fixed eventual length. This is live size plus headroom, not root count. -/
theorem prefix_memory_bound {headroom : Nat} (positive : 0 < headroom)
    (liveCells n : Nat) : liveCells + (run headroom n).garbage < liveCells + headroom := by
  exact Nat.add_lt_add_left (run_garbage_lt positive n) liveCells

/-- The allocation immediately before a possible collection also fits. -/
theorem allocation_peak_bound {headroom : Nat} (positive : 0 < headroom)
    (liveCells n : Nat) :
    liveCells + (allocate (run headroom n)).garbage ≤ liveCells + headroom := by
  have := run_garbage_lt positive n
  simp only [allocate]
  omega

namespace Controls

theorem no_collection_before_full {headroom n : Nat} (below : n < headroom) :
    (run headroom n).collections = 0 ∧ (run headroom n).garbage = n := by
  have positive : 0 < headroom := by omega
  rw [run_collections positive, run_garbage positive,
    Nat.div_eq_of_lt below, Nat.mod_eq_of_lt below]
  exact ⟨rfl, rfl⟩

/-- Both policies finish with no garbage, yet immediate full tracing pays an
arbitrarily large multiplicative factor. The larger headroom is real space
between collections, not uncharged memory. -/
theorem same_final_retention_different_work (liveVisits : Nat) {n : Nat}
    (positive : 0 < n) :
    (run 1 n).garbage = 0 ∧ (run n n).garbage = 0 ∧
      tracingWork liveVisits (run 1 n) = n * tracingWork liveVisits (run n n) := by
  simp only [run_garbage (by decide : 0 < 1), Nat.mod_one,
    run_garbage positive, Nat.mod_self, exact_work (by decide : 0 < 1),
    Nat.div_one, exact_work positive, Nat.div_self positive, Nat.mul_one]
  exact ⟨trivial, trivial, Nat.mul_comm _ _⟩

theorem collecting_every_request_costs_1000_times_more :
    tracingWork 100 (run 1 1000) = 100000 ∧
      tracingWork 100 (run 1000 1000) = 100 := by
  simp [exact_work]

/-- Fewer collections are possible if the final strict boundary is dropped:
the last full batch has not yet been collected. -/
theorem boundary_convention_matters :
    Trace 1 ⟨1, 1, 0⟩ ∧ ¬ (1 / 1 ≤ (0 : Nat)) := by
  constructor
  · exact .allocate .start (by decide)
  · decide

theorem zero_headroom_is_not_an_admissible_allocation :
    ¬ Trace 0 ⟨1, 0, 1⟩ := by
  intro trace
  have bound := trace_allocation_bound trace
  simp at bound

end Controls

end Mettapedia.Machines.ResourceCollectionSchedule
