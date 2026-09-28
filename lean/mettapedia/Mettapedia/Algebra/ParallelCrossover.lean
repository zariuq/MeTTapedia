import Mettapedia.Algebra.WorkSpan

/-!
# Finite-worker parallel crossover and background optimization

Parallel speed depends on actual worker loads and overhead, not merely on a
thread-count threshold. This module extends the existing work/span algebra
with an explicit finite-worker schedule. Its equations are cost-model laws;
they are not measurements or semantic licenses to reorder a computation.

The background-optimizer model keeps the baseline running while a proposal is
sought. It accounts for search delay, baseline progress, contention, transfer,
and the cost of the optimized residual. Correct transfer of that residual is
an independent obligation supplied by the execution theory.
-/

namespace Mettapedia.Algebra.ParallelCrossover

/-- Sequential load assigned to each available worker. Empty and idle workers
are represented explicitly rather than assumed to contribute useful width. -/
def workers (loads : List Nat) : WorkSpan :=
  loads.foldr (fun load rest => WorkSpan.parallel ⟨load, load⟩ rest) 0

/-- Ideal critical path of one fixed worker assignment. -/
def peak (loads : List Nat) : Nat := loads.foldr max 0

@[simp] theorem workers_work (loads : List Nat) :
    (workers loads).work = loads.sum := by
  induction loads with
  | nil => rfl
  | cons load rest ih =>
    change load + (workers rest).work = load + rest.sum
    rw [ih]

@[simp] theorem workers_span (loads : List Nat) :
    (workers loads).span = peak loads := by
  induction loads with
  | nil => rfl
  | cons load rest ih =>
    change max load (workers rest).span = max load (peak rest)
    rw [ih]

/-- Explicit preparation, dispatch, synchronization, transfer, and contention
costs may be combined into `overhead`. Work and span remain separate so idle
waiting need not be charged as productive instruction work. -/
def scheduled (overhead : WorkSpan) (loads : List Nat) : WorkSpan :=
  WorkSpan.sequential overhead (workers loads)

/-- Sequential execution of the same work, with no parallel-only overhead. -/
def serial (loads : List Nat) : WorkSpan := ⟨loads.sum, loads.sum⟩

@[simp] theorem scheduled_work (overhead : WorkSpan) (loads : List Nat) :
    (scheduled overhead loads).work = overhead.work + loads.sum := by
  simp [scheduled, WorkSpan.sequential]

@[simp] theorem scheduled_span (overhead : WorkSpan) (loads : List Nat) :
    (scheduled overhead loads).span = overhead.span + peak loads := by
  simp [scheduled, WorkSpan.sequential]

theorem peak_le_sum (loads : List Nat) : peak loads ≤ loads.sum := by
  induction loads with
  | nil => simp [peak]
  | cons load rest ih =>
    change max load (peak rest) ≤ load + rest.sum
    omega

/-- The useful average load cannot exceed the critical worker load. Merely
requesting more threads does not make a skewed assignment balanced. -/
theorem sum_le_workers_mul_peak (loads : List Nat) :
    loads.sum ≤ loads.length * peak loads := by
  induction loads with
  | nil => simp
  | cons load rest ih =>
    have tailBound : rest.sum ≤ rest.length * max load (peak rest) :=
      ih.trans (Nat.mul_le_mul_left _ (le_max_right _ _))
    have headBound : load ≤ max load (peak rest) := le_max_left _ _
    change load + rest.sum ≤ (rest.length + 1) * max load (peak rest)
    calc
      load + rest.sum ≤ max load (peak rest) +
          rest.length * max load (peak rest) := Nat.add_le_add headBound tailBound
      _ = (rest.length + 1) * max load (peak rest) := by
        simp [Nat.add_mul, Nat.add_comm]

/-- Necessary and sufficient crossover for this explicit cost model. -/
theorem faster_iff (overhead : WorkSpan) (loads : List Nat) :
    (scheduled overhead loads).span < (serial loads).span ↔
      overhead.span + peak loads < loads.sum := by
  simp [serial]

/-- With two workers, overhead must fit below the smaller useful load. This
exhibits why an idle second worker cannot produce a strict speedup. -/
theorem two_workers_faster_iff (overhead : WorkSpan) (left right : Nat) :
    (scheduled overhead [left, right]).span < (serial [left, right]).span ↔
      overhead.span < min left right := by
  simp only [scheduled_span, peak, List.foldr_cons, List.foldr_nil, max_zero,
    serial, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- A balanced three-worker assignment tolerates overhead below the work
saved by the two additional workers. -/
theorem three_balanced_workers_faster_iff (overhead : WorkSpan) (load : Nat) :
    (scheduled overhead [load, load, load]).span <
        (serial [load, load, load]).span ↔
      overhead.span < 2 * load := by
  simp only [scheduled_span, peak, List.foldr_cons, List.foldr_nil, max_zero,
    max_self, serial, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- More overhead can never turn a losing assignment into a winning one. -/
theorem faster_of_overhead_span_le (loads : List Nat) (small large : WorkSpan)
    (overheadBound : small.span ≤ large.span)
    (largeFaster : (scheduled large loads).span < (serial loads).span) :
    (scheduled small loads).span < (serial loads).span := by
  simp only [scheduled_span] at *
  omega

/-- Boundary estimates can justify a robust decision: the complete parallel
upper bound must beat a lower bound on the sequential execution. -/
theorem faster_of_bounds {parallelActual serialActual parallelUpper serialLower : Nat}
    (parallelBound : parallelActual ≤ parallelUpper)
    (serialBound : serialLower ≤ serialActual)
    (margin : parallelUpper < serialLower) :
    parallelActual < serialActual := by omega

/-- A proposal search is concurrent with the baseline prefix. `progress` is
baseline work already discharged, not an invented answer count; the residual
theory must establish what work and observations remain. -/
structure BackgroundProposal where
  baseline : Nat
  progress : Nat
  searchDelay : Nat
  contention : Nat
  transfer : Nat
  optimizedResidual : Nat
  progress_le : progress ≤ baseline

namespace BackgroundProposal

/-- Even a discovered optimization is not usable before search completion.
Waiting beyond useful baseline progress, contention, and transfer are real
overhead rather than work silently removed from the comparison. -/
def ready (proposal : BackgroundProposal) : Nat :=
  max proposal.progress proposal.searchDelay

def switchTime (proposal : BackgroundProposal) : Nat :=
  proposal.ready + proposal.contention + proposal.transfer + proposal.optimizedResidual

def oldResidual (proposal : BackgroundProposal) : Nat :=
  proposal.baseline - proposal.progress

def overhead (proposal : BackgroundProposal) : Nat :=
  (proposal.searchDelay - proposal.progress) + proposal.contention + proposal.transfer

/-- Background specialization pays exactly when residual saving exceeds all
delay, contention, and transfer costs in this model. -/
theorem switch_faster_iff (proposal : BackgroundProposal) :
    proposal.switchTime < proposal.baseline ↔
      proposal.overhead + proposal.optimizedResidual < proposal.oldResidual := by
  have progressBound := proposal.progress_le
  simp only [switchTime, ready, overhead, oldResidual]
  omega

/-- Searching on a second thread is not free. Even a search that is ready
early cannot help if transfer and interference consume all residual savings. -/
theorem no_gain_of_overhead (proposal : BackgroundProposal)
    (tooMuch : proposal.oldResidual ≤ proposal.overhead + proposal.optimizedResidual) :
    proposal.baseline ≤ proposal.switchTime := by
  have := proposal.switch_faster_iff
  omega

/-- A late discovery cannot justify switching to a nonnegative-cost residual
after the baseline would already have completed. -/
theorem no_gain_of_late_search (proposal : BackgroundProposal)
    (late : proposal.baseline ≤ proposal.searchDelay) :
    proposal.baseline ≤ proposal.switchTime := by
  simp only [switchTime, ready]
  omega

/-- Keeping the baseline as an available completion route bounds a race only
by the baseline *with contention*. It does not promise baseline-only latency. -/
def raceTime (proposal : BackgroundProposal) : Nat :=
  min (proposal.baseline + proposal.contention) proposal.switchTime

theorem race_le_contended_baseline (proposal : BackgroundProposal) :
    proposal.raceTime ≤ proposal.baseline + proposal.contention :=
  min_le_left _ _

theorem race_faster_of_switch_faster (proposal : BackgroundProposal)
    (gain : proposal.switchTime < proposal.baseline) :
    proposal.raceTime < proposal.baseline :=
  (min_le_right _ _).trans_lt gain

end BackgroundProposal

namespace Controls

theorem two_workers_pay :
    (scheduled ⟨20, 20⟩ [100, 100]).work = 220 ∧
    (scheduled ⟨20, 20⟩ [100, 100]).span = 120 ∧
    (serial [100, 100]).span = 200 := by decide

theorem three_workers_pay :
    (scheduled ⟨30, 30⟩ [100, 100, 100]).span = 130 ∧
      (scheduled ⟨30, 30⟩ [100, 100, 100]).span <
        (serial [100, 100, 100]).span := by decide

theorem tiny_batch_loses :
    (serial [1, 1]).span < (scheduled ⟨2, 2⟩ [1, 1]).span := by decide

theorem high_overhead_loses :
    (serial [100, 100, 100]).span <
      (scheduled ⟨250, 250⟩ [100, 100, 100]).span := by decide

theorem idle_worker_no_gain :
    (scheduled 0 [1000, 0]).span = (serial [1000, 0]).span := by decide

def usefulProposal : BackgroundProposal :=
  ⟨1000, 200, 250, 20, 30, 200, by decide⟩

theorem second_thread_optimizer_pays :
    usefulProposal.switchTime = 500 ∧
      usefulProposal.raceTime < usefulProposal.baseline := by decide

def harmfulProposal : BackgroundProposal :=
  ⟨1000, 200, 250, 300, 300, 200, by decide⟩

theorem second_thread_optimizer_can_lose :
    harmfulProposal.baseline < harmfulProposal.raceTime := by decide

end Controls

end Mettapedia.Algebra.ParallelCrossover
