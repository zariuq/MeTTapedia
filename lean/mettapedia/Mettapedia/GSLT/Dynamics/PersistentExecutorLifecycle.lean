import Mettapedia.GSLT.Dynamics.OperatorRealization

/-!
# Persistent executor episode lifecycle

An operating-system worker may serve many execution episodes, but semantic
work, cancellation, failure, and resources remain owned by exactly one
episode.  This module separates the reusable worker authority from the
per-episode task and receipt products.

The abstract executor does not prescribe scheduling order.  It records an
assignment of unique task occurrences to reusable workers, balanced worker
entry/leave brackets, exact completion or cancellation partitions, and a
total nested-execution fallback.  Scratch storage is intentionally absent
from the persistent authority: storage may be reused only under a separate
lease whose release follows observation of all episode results.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.PersistentExecutorLifecycle

universe uTask uWorker

variable {Task : Type uTask} {Worker : Type uWorker}

/-- Authored work enters an episode as distinct occurrences. -/
structure EpisodeInput (Task : Type uTask) where
  tasks : List Task
  unique : tasks.Nodup

/-- The reusable physical authority.  `nextEpisode` is fresh identity, while
the worker family survives completed episodes. -/
structure Pool (Worker : Type uWorker) where
  workers : List Worker
  unique : workers.Nodup
  live : workers ≠ []
  nextEpisode : Nat

/-- The workers participating in one episode form a nonempty, duplicate-free
subfamily of the persistent authority.  A later episode may use a smaller
roster without terminating the authority's other workers. -/
structure EpisodeRoster (pool : Pool Worker) where
  workers : List Worker
  unique : workers.Nodup
  live : workers ≠ []
  owned : ∀ worker ∈ workers, worker ∈ pool.workers

/-- A scheduler may select any participating worker for each task
occurrence. -/
structure Assignment
    (workers : List Worker) (input : EpisodeInput Task) where
  pick : Task → Worker
  pick_mem : ∀ task ∈ input.tasks, pick task ∈ workers

structure DispatchEntry
    (Task : Type uTask) (Worker : Type uWorker) where
  task : Task
  worker : Worker
deriving DecidableEq, Repr

/-- Scheduling metadata retains exact task occurrences without making its
order or worker choice part of the extensional result. -/
def dispatch
    {workers : List Worker}
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) workers input) :
    List (DispatchEntry Task Worker) :=
  input.tasks.map fun task => ⟨task, assignment.pick task⟩

@[simp]
theorem dispatch_tasks
    {workers : List Worker}
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) workers input) :
    (dispatch input assignment).map DispatchEntry.task = input.tasks := by
  simp [dispatch, List.map_map, Function.comp_def]

theorem dispatch_workers_live
    {pool : Pool Worker}
    (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input)
    (entry : DispatchEntry Task Worker)
    (present : entry ∈ dispatch input assignment) :
    entry.worker ∈ pool.workers := by
  simp only [dispatch, List.mem_map] at present
  obtain ⟨task, taskMem, rfl⟩ := present
  exact roster.owned _ (assignment.pick_mem task taskMem)

inductive LifecycleEvent
    (Task : Type uTask) (Worker : Type uWorker) where
  | enter (episode : Nat) (worker : Worker)
  | execute (episode : Nat) (task : Task) (worker : Worker)
  | leave (episode : Nat) (worker : Worker)
deriving DecidableEq, Repr

/-- Every worker participating in an episode is bracketed.  Task order inside
the middle segment is schedule evidence, not result-bag authority. -/
def lifecycleTrace
    {pool : Pool Worker}
    (roster : EpisodeRoster pool) (episode : Nat)
    (entries : List (DispatchEntry Task Worker)) :
    List (LifecycleEvent Task Worker) :=
  roster.workers.map (.enter episode) ++
    entries.map (fun entry => .execute episode entry.task entry.worker) ++
    roster.workers.map (.leave episode)

def enteredWorkers :
    List (LifecycleEvent Task Worker) → List Worker
  | [] => []
  | .enter _ worker :: rest => worker :: enteredWorkers rest
  | _ :: rest => enteredWorkers rest

def leftWorkers :
    List (LifecycleEvent Task Worker) → List Worker
  | [] => []
  | .leave _ worker :: rest => worker :: leftWorkers rest
  | _ :: rest => leftWorkers rest

def executedTasks :
    List (LifecycleEvent Task Worker) → List Task
  | [] => []
  | .execute _ task _ :: rest => task :: executedTasks rest
  | _ :: rest => executedTasks rest

@[simp]
theorem enteredWorkers_append
    (first second : List (LifecycleEvent Task Worker)) :
    enteredWorkers (first ++ second) =
      enteredWorkers first ++ enteredWorkers second := by
  induction first with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [enteredWorkers, ih]

@[simp]
theorem leftWorkers_append
    (first second : List (LifecycleEvent Task Worker)) :
    leftWorkers (first ++ second) =
      leftWorkers first ++ leftWorkers second := by
  induction first with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [leftWorkers, ih]

@[simp]
theorem executedTasks_append
    (first second : List (LifecycleEvent Task Worker)) :
    executedTasks (first ++ second) =
      executedTasks first ++ executedTasks second := by
  induction first with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [executedTasks, ih]

@[simp]
theorem enteredWorkers_map_enter
    (episode : Nat) (workers : List Worker) :
    enteredWorkers
        (workers.map (LifecycleEvent.enter (Task := Task) episode)) =
      workers := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [enteredWorkers, ih]

@[simp]
theorem enteredWorkers_map_execute
    (episode : Nat) (entries : List (DispatchEntry Task Worker)) :
    enteredWorkers
        (entries.map fun entry =>
          LifecycleEvent.execute episode entry.task entry.worker) = [] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [enteredWorkers, ih]

@[simp]
theorem enteredWorkers_map_leave
    (episode : Nat) (workers : List Worker) :
    enteredWorkers
        (workers.map (LifecycleEvent.leave (Task := Task) episode)) = [] := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [enteredWorkers, ih]

@[simp]
theorem leftWorkers_map_enter
    (episode : Nat) (workers : List Worker) :
    leftWorkers
        (workers.map (LifecycleEvent.enter (Task := Task) episode)) = [] := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [leftWorkers, ih]

@[simp]
theorem leftWorkers_map_execute
    (episode : Nat) (entries : List (DispatchEntry Task Worker)) :
    leftWorkers
        (entries.map fun entry =>
          LifecycleEvent.execute episode entry.task entry.worker) = [] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [leftWorkers, ih]

@[simp]
theorem leftWorkers_map_leave
    (episode : Nat) (workers : List Worker) :
    leftWorkers
        (workers.map (LifecycleEvent.leave (Task := Task) episode)) =
      workers := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [leftWorkers, ih]

@[simp]
theorem executedTasks_map_enter
    (episode : Nat) (workers : List Worker) :
    executedTasks
        (workers.map (LifecycleEvent.enter (Task := Task) episode)) =
      ([] : List Task) := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [executedTasks, ih]

@[simp]
theorem executedTasks_map_execute
    (episode : Nat) (entries : List (DispatchEntry Task Worker)) :
    executedTasks
        (entries.map fun entry =>
          LifecycleEvent.execute episode entry.task entry.worker) =
      entries.map DispatchEntry.task := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [executedTasks, ih]

@[simp]
theorem executedTasks_map_leave
    (episode : Nat) (workers : List Worker) :
    executedTasks
        (workers.map (LifecycleEvent.leave (Task := Task) episode)) =
      ([] : List Task) := by
  induction workers with
  | nil => rfl
  | cons worker rest ih => simp [executedTasks, ih]

@[simp]
theorem lifecycleTrace_entered
    {pool : Pool Worker} (roster : EpisodeRoster pool) (episode : Nat)
    (entries : List (DispatchEntry Task Worker)) :
    enteredWorkers (lifecycleTrace roster episode entries) =
      roster.workers := by
  simp [lifecycleTrace]

@[simp]
theorem lifecycleTrace_left
    {pool : Pool Worker} (roster : EpisodeRoster pool) (episode : Nat)
    (entries : List (DispatchEntry Task Worker)) :
    leftWorkers (lifecycleTrace roster episode entries) =
      roster.workers := by
  simp [lifecycleTrace]

@[simp]
theorem lifecycleTrace_executed
    {pool : Pool Worker} (roster : EpisodeRoster pool) (episode : Nat)
    (entries : List (DispatchEntry Task Worker)) :
    executedTasks (lifecycleTrace roster episode entries) =
      entries.map DispatchEntry.task := by
  simp [lifecycleTrace]

/-- Entry and leave are balanced independently of task scheduling. -/
theorem lifecycleTrace_bracket_balance
    {pool : Pool Worker} (roster : EpisodeRoster pool) (episode : Nat)
    (entries : List (DispatchEntry Task Worker)) :
    (enteredWorkers (lifecycleTrace roster episode entries)).length =
      (leftWorkers (lifecycleTrace roster episode entries)).length := by
  simp

inductive Completion where
  | complete
  | cancelled
  | failed
deriving DecidableEq, Repr

/-- The receipt separates settled occurrences from the residual owned by the
same episode.  A caller may release episode storage only after observing this
receipt and any result values it names. -/
structure EpisodeReceipt
    (Task : Type uTask) (Worker : Type uWorker) where
  episode : Nat
  participants : List Worker
  dispatch : List (DispatchEntry Task Worker)
  completed : List Task
  residual : List Task
  completion : Completion
  trace : List (LifecycleEvent Task Worker)

def advance (pool : Pool Worker) : Pool Worker :=
  { pool with nextEpisode := pool.nextEpisode + 1 }

/-- The complete realization settles every authored occurrence exactly once. -/
def runComplete
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input) :
    Pool Worker × EpisodeReceipt Task Worker :=
  let entries := dispatch input assignment
  (advance pool, {
    episode := pool.nextEpisode
    participants := roster.workers
    dispatch := entries
    completed := input.tasks
    residual := []
    completion := .complete
    trace := lifecycleTrace roster pool.nextEpisode entries
  })

/-- Cancellation at an observation boundary settles a prefix and returns the
unselected suffix as explicit residual work. -/
def runCancelled
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input)
    (settled : Nat) :
    Pool Worker × EpisodeReceipt Task Worker :=
  let completed := input.tasks.take settled
  let entries := completed.map fun task =>
    (⟨task, assignment.pick task⟩ : DispatchEntry Task Worker)
  (advance pool, {
    episode := pool.nextEpisode
    participants := roster.workers
    dispatch := entries
    completed := completed
    residual := input.tasks.drop settled
    completion := .cancelled
    trace := lifecycleTrace roster pool.nextEpisode entries
  })

@[simp]
theorem runComplete_preserves_worker_authority
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input) :
    (runComplete pool roster input assignment).1.workers = pool.workers := by
  rfl

@[simp]
theorem runComplete_advances_episode
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input) :
    (runComplete pool roster input assignment).1.nextEpisode =
      pool.nextEpisode + 1 := by
  rfl

theorem runComplete_exact
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input) :
    let receipt := (runComplete pool roster input assignment).2
    receipt.participants = roster.workers ∧
      receipt.completed = input.tasks ∧
      receipt.residual = [] ∧
      receipt.dispatch.map DispatchEntry.task = input.tasks ∧
      executedTasks receipt.trace = input.tasks := by
  simp [runComplete]

/-- Cancellation loses and duplicates no occurrence: completed and residual
reconstruct the authored episode exactly. -/
theorem runCancelled_partition
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input)
    (settled : Nat) :
    let receipt := (runCancelled pool roster input assignment settled).2
    receipt.completed ++ receipt.residual = input.tasks := by
  simp [runCancelled, List.take_append_drop]

theorem runCancelled_completed_unique
    (pool : Pool Worker) (roster : EpisodeRoster pool)
    (input : EpisodeInput Task)
    (assignment : Assignment (Task := Task) roster.workers input)
    (settled : Nat) :
    ((runCancelled pool roster input assignment settled).2.completed).Nodup := by
  change (input.tasks.take settled).Nodup
  exact input.unique.take

/-- Successive episodes keep physical worker identity while receiving fresh
episode identity and fresh semantic receipts. -/
theorem successive_runs_reuse_workers
    (pool : Pool Worker)
    (firstInput secondInput : EpisodeInput Task)
    (firstRoster : EpisodeRoster pool)
    (firstAssignment :
      Assignment (Task := Task) firstRoster.workers firstInput)
    (secondRoster :
      EpisodeRoster (runComplete pool firstRoster firstInput firstAssignment).1)
    (secondAssignment :
      Assignment (Task := Task) secondRoster.workers secondInput) :
    let first := runComplete pool firstRoster firstInput firstAssignment
    let second := runComplete first.1 secondRoster secondInput secondAssignment
    second.1.workers = pool.workers ∧
      first.2.episode ≠ second.2.episode := by
  simp [runComplete, advance]

/-- A persistent authority may grow between episodes, but workers already in
the authority are not silently removed.  This relation deliberately says
nothing about episode participation: a roster may use any owned subfamily. -/
def PoolExtends (before after : Pool Worker) : Prop :=
  ∀ worker ∈ before.workers, worker ∈ after.workers

@[refl]
theorem PoolExtends.refl (pool : Pool Worker) : PoolExtends pool pool := by
  intro worker present
  exact present

@[trans]
theorem PoolExtends.trans
    {first second third : Pool Worker}
    (firstSecond : PoolExtends first second)
    (secondThird : PoolExtends second third) :
    PoolExtends first third := by
  intro worker present
  exact secondThird worker (firstSecond worker present)

inductive Realization where
  | persistentWorkers
  | oneShotWorkers
deriving DecidableEq, Repr

/-- A worker that recursively requests parallel execution uses an independent
one-shot realization.  This is a total fallback that avoids waiting for the
same bounded persistent pool from inside one of its occupied workers. -/
def chooseRealization (nested : Bool) : Realization :=
  if nested then .oneShotWorkers else .persistentWorkers

@[simp]
theorem nested_uses_total_fallback :
    chooseRealization true = .oneShotWorkers := by
  rfl

@[simp]
theorem outer_uses_persistent_workers :
    chooseRealization false = .persistentWorkers := by
  rfl

namespace Canaries

def pool : Pool Nat where
  workers := [10, 11]
  unique := by decide
  live := by decide
  nextEpisode := 7

def input : EpisodeInput Nat where
  tasks := [1, 2, 3]
  unique := by decide

def bothWorkers : EpisodeRoster pool where
  workers := [10, 11]
  unique := by decide
  live := by decide
  owned := by simp [pool]

def firstWorker : EpisodeRoster pool where
  workers := [10]
  unique := by decide
  live := by decide
  owned := by simp [pool]

def allLeft : Assignment bothWorkers.workers input where
  pick := fun _ => 10
  pick_mem := by simp [bothWorkers]

def split : Assignment bothWorkers.workers input where
  pick := fun task => if task % 2 = 0 then 10 else 11
  pick_mem := by
    intro task _
    by_cases h : task % 2 = 0 <;> simp [h, bothWorkers]

def firstOnly : Assignment firstWorker.workers input where
  pick := fun _ => 10
  pick_mem := by simp [firstWorker]

def completed := runComplete pool bothWorkers input allLeft
def cancelled := runCancelled pool bothWorkers input split 2

def grownPool : Pool Nat where
  workers := [10, 11, 12]
  unique := by decide
  live := by decide
  nextEpisode := 8

/-- Positive: all occurrences complete once and the worker family survives. -/
example :
    completed.2.completed = [1, 2, 3] ∧
      completed.2.residual = [] ∧
      completed.1.workers = [10, 11] := by
  decide

/-- Positive: cancellation exposes the exact unsettled suffix. -/
example :
    cancelled.2.completed = [1, 2] ∧
      cancelled.2.residual = [3] := by
  decide

/-- Schedule metadata may differ while extensional completed occurrences are
identical. -/
example :
    (runComplete pool bothWorkers input allLeft).2.dispatch ≠
        (runComplete pool bothWorkers input split).2.dispatch ∧
      (runComplete pool bothWorkers input allLeft).2.completed =
        (runComplete pool bothWorkers input split).2.completed := by
  decide

/-- Positive: a grown pool may run a smaller roster while inactive owned
workers remain outside that episode's lifecycle trace. -/
example :
    (runComplete pool firstWorker input firstOnly).2.participants = [10] ∧
      enteredWorkers
        (runComplete pool firstWorker input firstOnly).2.trace = [10] ∧
      (runComplete pool firstWorker input firstOnly).1.workers = [10, 11] := by
  decide

/-- Positive: adding a worker is a monotone authority extension. -/
example : PoolExtends pool grownPool := by
  intro worker present
  simp [pool] at present
  rcases present with rfl | rfl <;> simp [grownPool]

/-- Negative: dropping an existing worker is not an authority extension. -/
example : ¬ PoolExtends grownPool pool := by
  intro extension
  have present := extension 12 (by simp [grownPool])
  simp [pool] at present

/-- Negative identity control: duplicate task identifiers cannot inhabit the
episode-input occurrence invariant. -/
example : ¬ ([1, 1] : List Nat).Nodup := by
  decide

def unbalancedTrace : List (LifecycleEvent Nat Nat) := [.enter 7 10]

/-- Negative lifecycle control: an unmatched entry is observably unbalanced. -/
example :
    (enteredWorkers unbalancedTrace).length ≠
      (leftWorkers unbalancedTrace).length := by
  decide

end Canaries

#print axioms dispatch_tasks
#print axioms dispatch_workers_live
#print axioms lifecycleTrace_bracket_balance
#print axioms runComplete_exact
#print axioms runCancelled_partition
#print axioms runCancelled_completed_unique
#print axioms successive_runs_reuse_workers
#print axioms nested_uses_total_fallback
#print axioms outer_uses_persistent_workers

end Mettapedia.GSLT.Dynamics.PersistentExecutorLifecycle
