import Mettapedia.GSLT.Dynamics.OperatorRealization
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

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

/-! ## Quiescent shutdown with independently owned leases

The reference state retains individual episode/context owners and unjoined
worker slots. The counted protocol uses bounded admission counters and a
reserved foreign-counter sentinel instead. Their comparison is a protocol
refinement, not a proof of a mutex, atomic memory order, foreign allocator or
thread-join implementation. Releases require their original owner receipts;
a positive aggregate counter cannot establish those receipts.

Closing admission and testing quiescence are one transition. Actual joins
occur afterward. A failed join leaves admission closed and preserves the
remaining slots and complete caller checkpoint for a later retry.
-/

namespace Quiescence

universe uLease uCheckpoint

variable {Lease : Type uLease} {Checkpoint : Type uCheckpoint}

inductive Phase where
  | open
  | joining
  | retry
  | joined
deriving DecidableEq, Repr

structure Reference (Lease : Type uLease) (Checkpoint : Type uCheckpoint) where
  phase : Phase
  episodes : Finset Lease
  foreignOwners : Finset Lease
  foreignSealed : Bool
  unjoined : Finset Nat
  checkpoint : Checkpoint
deriving DecidableEq

structure Counted (Checkpoint : Type uCheckpoint) where
  phase : Phase
  episodes : Nat
  foreignWord : Nat
  remainingJoins : Nat
  checkpoint : Checkpoint
deriving DecidableEq

/-- This relation compares independently represented owners, not two copies
of the same counter. The sentinel is never a live foreign-owner count. -/
structure Corresponds (limit : Nat) (reference : Reference Lease Checkpoint)
    (counted : Counted Checkpoint) : Prop where
  phase : counted.phase = reference.phase
  episodes : counted.episodes = reference.episodes.card
  foreignWord : counted.foreignWord =
    if reference.foreignSealed = true then limit else reference.foreignOwners.card
  joins : counted.remainingJoins = reference.unjoined.card
  checkpoint : counted.checkpoint = reference.checkpoint
  episodeBound : reference.episodes.card ≤ limit
  foreignBound : reference.foreignOwners.card < limit
  sealedEmpty : reference.foreignSealed = true → reference.foreignOwners = ∅
  closedEmpty : reference.phase ≠ .open → reference.episodes = ∅
  joinedEmpty : reference.phase = .joined → reference.unjoined = ∅

abbrev referenceMayBegin (sealForeign : Bool)
    (state : Reference Lease Checkpoint) : Prop :=
  state.phase ≠ .joining ∧ state.episodes = ∅ ∧
    (sealForeign = true → state.foreignOwners = ∅)

abbrev countedMayBegin (limit : Nat) (sealForeign : Bool)
    (state : Counted Checkpoint) : Prop :=
  state.phase ≠ .joining ∧ state.episodes = 0 ∧
    (sealForeign = true → state.foreignWord = 0 ∨ state.foreignWord = limit)

theorem foreign_quiescence_iff {limit : Nat}
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    (counted.foreignWord = 0 ∨ counted.foreignWord = limit) ↔
      reference.foreignOwners = ∅ := by
  rw [related.foreignWord]
  by_cases sealed : reference.foreignSealed = true
  · rw [if_pos sealed]
    exact ⟨fun _ => related.sealedEmpty sealed, fun _ => Or.inr rfl⟩
  · rw [if_neg sealed]
    constructor
    · rintro (zero | sentinel)
      · exact Finset.card_eq_zero.mp zero
      · exact False.elim ((Nat.ne_of_lt related.foreignBound) sentinel)
    · intro empty
      exact Or.inl (by rw [empty]; rfl)

/-- The bounded sentinel guard accepts exactly the same owner-free boundary
as the independently tracked reference ledger. -/
theorem may_begin_iff {limit : Nat} (sealForeign : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    countedMayBegin limit sealForeign counted ↔
      referenceMayBegin sealForeign reference := by
  simp only [countedMayBegin, referenceMayBegin, related.phase, related.episodes,
    Finset.card_eq_zero, foreign_quiescence_iff related]

def beginPhase (phase : Phase) : Phase :=
  if phase = .joined then .joined else .joining

variable [DecidableEq Lease]

def referenceBegin (sealForeign : Bool) (state : Reference Lease Checkpoint) :
    Option (Reference Lease Checkpoint) :=
  if referenceMayBegin sealForeign state then
    some { state with phase := beginPhase state.phase,
                      foreignSealed := state.foreignSealed || sealForeign }
  else none

def countedBegin (limit : Nat) (sealForeign : Bool) (state : Counted Checkpoint) :
    Option (Counted Checkpoint) :=
  if countedMayBegin limit sealForeign state then
    some { state with phase := beginPhase state.phase,
                      foreignWord := if sealForeign = true then limit else state.foreignWord }
  else none

theorem begin_refused_iff {limit : Nat} (sealForeign : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    countedBegin limit sealForeign counted = none ↔
      referenceBegin sealForeign reference = none := by
  by_cases allowed : referenceMayBegin sealForeign reference
  · have countedAllowed := (may_begin_iff sealForeign related).mpr allowed
    unfold countedBegin referenceBegin
    rw [if_pos countedAllowed, if_pos allowed]
    simp only [Option.some_ne_none]
  · have countedRefused := mt (may_begin_iff sealForeign related).mp allowed
    unfold countedBegin referenceBegin
    rw [if_neg countedRefused, if_neg allowed]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

omit [DecidableEq Lease] in
theorem begin_corresponds {limit : Nat} (sealForeign : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted)
    (allowed : referenceMayBegin sealForeign reference) :
    Corresponds limit
      { reference with phase := beginPhase reference.phase,
                       foreignSealed := reference.foreignSealed || sealForeign }
      { counted with phase := beginPhase counted.phase,
                     foreignWord := if sealForeign = true then limit else counted.foreignWord } := by
  constructor
  · exact congrArg beginPhase related.phase
  · exact related.episodes
  · cases sealForeign <;> cases sealed : reference.foreignSealed <;>
      simp [sealed, related.foreignWord]
  · exact related.joins
  · exact related.checkpoint
  · exact related.episodeBound
  · exact related.foreignBound
  · intro sealed
    have alternatives : reference.foreignSealed = true ∨ sealForeign = true := by
      simpa only [Bool.or_eq_true] using sealed
    exact alternatives.elim related.sealedEmpty allowed.2.2
  · intro _
    exact allowed.2.1
  · intro finalized
    by_cases wasJoined : reference.phase = .joined
    · exact related.joinedEmpty wasJoined
    · simp [beginPhase, wasJoined] at finalized

/-- After the atomic closure boundary, both forms of reentrant episode
admission are refused. No join or finalizer needs the admission lock. -/
theorem begin_closes_episode_admission (phase : Phase) :
    beginPhase phase ≠ .open := by
  cases phase <;> decide

def referenceEnter (limit : Nat) (owner : Lease)
    (state : Reference Lease Checkpoint) : Option (Reference Lease Checkpoint) :=
  if state.phase = .open ∧ owner ∉ state.episodes ∧ state.episodes.card < limit then
    some { state with episodes := insert owner state.episodes }
  else none

def countedEnter (limit : Nat) (state : Counted Checkpoint) :
    Option (Counted Checkpoint) :=
  if state.phase = .open ∧ state.episodes < limit then
    some { state with episodes := state.episodes + 1 }
  else none

theorem enter_refused_iff {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (fresh : owner ∉ reference.episodes) :
    countedEnter limit counted = none ↔ referenceEnter limit owner reference = none := by
  simp [countedEnter, referenceEnter, related.phase, related.episodes, fresh]

theorem enter_corresponds {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (openPhase : reference.phase = .open)
    (fresh : owner ∉ reference.episodes) (capacity : reference.episodes.card < limit) :
    Corresponds limit { reference with episodes := insert owner reference.episodes }
      { counted with episodes := counted.episodes + 1 } := by
  constructor
  · exact related.phase
  · simp [related.episodes, fresh]
  · exact related.foreignWord
  · exact related.joins
  · exact related.checkpoint
  · simp only [Finset.card_insert_of_notMem fresh]
    omega
  · exact related.foreignBound
  · exact related.sealedEmpty
  · intro closed
    exact False.elim (closed openPhase)
  · exact related.joinedEmpty

theorem closed_enter_refused (limit : Nat) (owner : Lease)
    (reference : Reference Lease Checkpoint) (counted : Counted Checkpoint)
    (referenceClosed : reference.phase ≠ .open) (countedClosed : counted.phase ≠ .open) :
    referenceEnter limit owner reference = none ∧ countedEnter limit counted = none := by
  simp [referenceEnter, countedEnter, referenceClosed, countedClosed]

/-- A release consumes an existing owner receipt, not just a positive count. -/
theorem leave_corresponds {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (owns : owner ∈ reference.episodes) :
    Corresponds limit { reference with episodes := reference.episodes.erase owner }
      { counted with episodes := counted.episodes - 1 } := by
  constructor
  · exact related.phase
  · simp [related.episodes, Finset.card_erase_of_mem owns]
  · exact related.foreignWord
  · exact related.joins
  · exact related.checkpoint
  · have decrease : (reference.episodes.erase owner).card ≤ reference.episodes.card :=
      Finset.card_erase_le
    exact decrease.trans related.episodeBound
  · exact related.foreignBound
  · exact related.sealedEmpty
  · intro closed
    simp [related.closedEmpty closed]
  · exact related.joinedEmpty

/-- A foreign reservation commits only against its current observed count.
`wins = false` represents a weak-CAS failure; it commits no owner. -/
def referenceReserve (limit observed : Nat) (wins : Bool) (owner : Lease)
    (state : Reference Lease Checkpoint) : Option (Reference Lease Checkpoint) :=
  if state.foreignSealed = false ∧ owner ∉ state.foreignOwners ∧
      state.foreignOwners.card < limit - 1 ∧ state.foreignOwners.card = observed ∧
      wins = true then
    some { state with foreignOwners := insert owner state.foreignOwners }
  else none

def countedReserve (limit observed : Nat) (wins : Bool) (state : Counted Checkpoint) :
    Option (Counted Checkpoint) :=
  if state.foreignWord < limit - 1 ∧ state.foreignWord = observed ∧ wins = true then
    some { state with foreignWord := state.foreignWord + 1 }
  else none

theorem reserve_refused_iff {limit : Nat} (observed : Nat) (wins : Bool) (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted)
    (fresh : owner ∉ reference.foreignOwners) :
    countedReserve limit observed wins counted = none ↔
      referenceReserve limit observed wins owner reference = none := by
  by_cases sealed : reference.foreignSealed = true
  · have sealedWord : counted.foreignWord = limit := by simp [related.foreignWord, sealed]
    have bound : ¬ limit < limit - 1 := by omega
    simp [countedReserve, referenceReserve, sealed, sealedWord, bound]
  · simp [countedReserve, referenceReserve, related.foreignWord, sealed, fresh]

theorem reserve_corresponds {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted)
    (unsealed : reference.foreignSealed = false) (fresh : owner ∉ reference.foreignOwners)
    (capacity : reference.foreignOwners.card < limit - 1) :
    Corresponds limit { reference with foreignOwners := insert owner reference.foreignOwners }
      { counted with foreignWord := counted.foreignWord + 1 } := by
  constructor
  · exact related.phase
  · exact related.episodes
  · simp [related.foreignWord, unsealed, fresh]
  · exact related.joins
  · exact related.checkpoint
  · exact related.episodeBound
  · simp only [Finset.card_insert_of_notMem fresh]
    omega
  · intro sealed
    simp [unsealed] at sealed
  · exact related.closedEmpty
  · exact related.joinedEmpty

theorem release_foreign_corresponds {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted)
    (owns : owner ∈ reference.foreignOwners) :
    Corresponds limit { reference with foreignOwners := reference.foreignOwners.erase owner }
      { counted with foreignWord := counted.foreignWord - 1 } := by
  have unsealed : reference.foreignSealed = false := by
    apply Bool.eq_false_iff.mpr
    intro sealed
    have empty := related.sealedEmpty sealed
    simp [empty] at owns
  constructor
  · exact related.phase
  · exact related.episodes
  · simp [related.foreignWord, unsealed, Finset.card_erase_of_mem owns]
  · exact related.joins
  · exact related.checkpoint
  · exact related.episodeBound
  · exact lt_of_le_of_lt Finset.card_erase_le related.foreignBound
  · intro sealed
    simp [unsealed] at sealed
  · exact related.closedEmpty
  · exact related.joinedEmpty

omit [DecidableEq Lease] in
/-- Successful thread joins consume distinct pending slots. The actual
thread-join service must establish the consumed-slot receipt. -/
theorem joined_slot_corresponds {limit : Nat} (slot : Nat)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (pending : slot ∈ reference.unjoined) :
    Corresponds limit { reference with unjoined := reference.unjoined.erase slot }
      { counted with remainingJoins := counted.remainingJoins - 1 } := by
  constructor
  · exact related.phase
  · exact related.episodes
  · exact related.foreignWord
  · simp [related.joins, Finset.card_erase_of_mem pending]
  · exact related.checkpoint
  · exact related.episodeBound
  · exact related.foreignBound
  · exact related.sealedEmpty
  · exact related.closedEmpty
  · intro finalized
    simp [related.joinedEmpty finalized]

def referenceFinish (success : Bool) (state : Reference Lease Checkpoint) :
    Option (Reference Lease Checkpoint) :=
  if state.phase = .joining ∧ (success = true → state.unjoined = ∅) then
    some { state with phase := if success = true then .joined else .retry }
  else none

def countedFinish (success : Bool) (state : Counted Checkpoint) :
    Option (Counted Checkpoint) :=
  if state.phase = .joining ∧ (success = true → state.remainingJoins = 0) then
    some { state with phase := if success = true then .joined else .retry }
  else none

omit [DecidableEq Lease] in
theorem finish_refused_iff {limit : Nat} (success : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    countedFinish success counted = none ↔ referenceFinish success reference = none := by
  simp [countedFinish, referenceFinish, related.phase, related.joins, Finset.card_eq_zero]

omit [DecidableEq Lease] in
theorem finish_corresponds {limit : Nat} (success : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (joining : reference.phase = .joining)
    (complete : success = true → reference.unjoined = ∅) :
    Corresponds limit
      { reference with phase := if success = true then .joined else .retry }
      { counted with phase := if success = true then .joined else .retry } := by
  constructor
  · rfl
  · exact related.episodes
  · exact related.foreignWord
  · exact related.joins
  · exact related.checkpoint
  · exact related.episodeBound
  · exact related.foreignBound
  · exact related.sealedEmpty
  · intro _
    exact related.closedEmpty (by simp [joining])
  · intro finalized
    by_cases succeeded : success = true
    · exact complete succeeded
    · simp [succeeded] at finalized

/-- Commit/refusal as seen by the caller. A refusal returns its entire
original checkpoint and leases, rather than a reconstructed residual. -/
def retainOnRefusal {State : Type*} (original : State) (result : Option State) : State :=
  result.getD original

theorem busy_begin_preserves_reference (sealForeign : Bool)
    (state : Reference Lease Checkpoint)
    (busy : state.episodes ≠ ∅ ∨ state.phase = .joining ∨
      (sealForeign = true ∧ state.foreignOwners ≠ ∅)) :
    retainOnRefusal state (referenceBegin sealForeign state) = state := by
  have refused : ¬ referenceMayBegin sealForeign state := by
    intro allowed
    rcases busy with episodes | joining | ⟨sealing, foreign⟩
    · exact episodes allowed.2.1
    · exact allowed.1 joining
    · exact foreign (allowed.2.2 sealing)
  simp [retainOnRefusal, referenceBegin, refused]

def referenceLeave (owner : Lease) (state : Reference Lease Checkpoint) :
    Option (Reference Lease Checkpoint) :=
  if owner ∈ state.episodes then
    some { state with episodes := state.episodes.erase owner }
  else none

def countedLeave (state : Counted Checkpoint) : Option (Counted Checkpoint) :=
  if state.episodes > 0 then some { state with episodes := state.episodes - 1 }
  else none

def referenceReleaseForeign (owner : Lease) (state : Reference Lease Checkpoint) :
    Option (Reference Lease Checkpoint) :=
  if owner ∈ state.foreignOwners then
    some { state with foreignOwners := state.foreignOwners.erase owner }
  else none

def countedReleaseForeign (limit : Nat) (state : Counted Checkpoint) :
    Option (Counted Checkpoint) :=
  if state.foreignWord > 0 ∧ state.foreignWord < limit then
    some { state with foreignWord := state.foreignWord - 1 }
  else none

def referenceJoinSlot (slot : Nat) (state : Reference Lease Checkpoint) :
    Option (Reference Lease Checkpoint) :=
  if state.phase = .joining ∧ slot ∈ state.unjoined then
    some { state with unjoined := state.unjoined.erase slot }
  else none

def countedJoinSlot (state : Counted Checkpoint) : Option (Counted Checkpoint) :=
  if state.phase = .joining ∧ state.remainingJoins > 0 then
    some { state with remainingJoins := state.remainingJoins - 1 }
  else none

/-- Complete operation results agree, including refusals. -/
theorem begin_result_correspondence {limit : Nat} (sealForeign : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    Option.Rel (Corresponds limit)
      (referenceBegin sealForeign reference) (countedBegin limit sealForeign counted) := by
  by_cases allowed : referenceMayBegin sealForeign reference
  · have countedAllowed := (may_begin_iff sealForeign related).mpr allowed
    unfold referenceBegin countedBegin
    rw [if_pos allowed, if_pos countedAllowed]
    exact .some (begin_corresponds sealForeign related allowed)
  · have countedRefused := mt (may_begin_iff sealForeign related).mp allowed
    unfold referenceBegin countedBegin
    rw [if_neg allowed, if_neg countedRefused]
    exact .none

theorem enter_result_correspondence {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (fresh : owner ∉ reference.episodes) :
    Option.Rel (Corresponds limit)
      (referenceEnter limit owner reference) (countedEnter limit counted) := by
  by_cases allowed : reference.phase = .open ∧ reference.episodes.card < limit
  · have countedAllowed : counted.phase = .open ∧ counted.episodes < limit := by
      simpa only [related.phase, related.episodes] using allowed
    unfold referenceEnter countedEnter
    rw [if_pos ⟨allowed.1, fresh, allowed.2⟩, if_pos countedAllowed]
    exact .some (enter_corresponds owner related allowed.1 fresh allowed.2)
  · have referenceRefused : ¬ (reference.phase = .open ∧ owner ∉ reference.episodes ∧
        reference.episodes.card < limit) := fun hypothesis => allowed ⟨hypothesis.1, hypothesis.2.2⟩
    have countedRefused : ¬ (counted.phase = .open ∧ counted.episodes < limit) := by
      simpa only [related.phase, related.episodes] using allowed
    unfold referenceEnter countedEnter
    rw [if_neg referenceRefused, if_neg countedRefused]
    exact .none

theorem leave_result_correspondence {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (owns : owner ∈ reference.episodes) :
    Option.Rel (Corresponds limit) (referenceLeave owner reference) (countedLeave counted) := by
  have live : counted.episodes > 0 := by
    rw [related.episodes]
    exact Finset.card_pos.mpr ⟨owner, owns⟩
  unfold referenceLeave countedLeave
  rw [if_pos owns, if_pos live]
  exact .some (leave_corresponds owner related owns)

theorem reserve_result_correspondence {limit : Nat} (observed : Nat) (wins : Bool)
    (owner : Lease) {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (fresh : owner ∉ reference.foreignOwners) :
    Option.Rel (Corresponds limit) (referenceReserve limit observed wins owner reference)
      (countedReserve limit observed wins counted) := by
  by_cases allowed : reference.foreignSealed = false ∧ owner ∉ reference.foreignOwners ∧
      reference.foreignOwners.card < limit - 1 ∧ reference.foreignOwners.card = observed ∧
      wins = true
  · have countedAllowed : counted.foreignWord < limit - 1 ∧
        counted.foreignWord = observed ∧ wins = true := by
      simpa only [related.foreignWord, allowed.1, Bool.false_eq_true, ↓reduceIte] using allowed.2.2
    unfold referenceReserve countedReserve
    rw [if_pos allowed, if_pos countedAllowed]
    exact .some (reserve_corresponds owner related allowed.1 fresh allowed.2.2.1)
  · have referenceRefused : referenceReserve limit observed wins owner reference = none := by
      unfold referenceReserve
      rw [if_neg allowed]
    have countedRefused := (reserve_refused_iff observed wins owner related fresh).mpr referenceRefused
    rw [referenceRefused, countedRefused]
    exact .none

theorem release_foreign_result_correspondence {limit : Nat} (owner : Lease)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (owns : owner ∈ reference.foreignOwners) :
    Option.Rel (Corresponds limit) (referenceReleaseForeign owner reference)
      (countedReleaseForeign limit counted) := by
  have unsealed : reference.foreignSealed = false := by
    apply Bool.eq_false_iff.mpr
    intro sealed
    have empty := related.sealedEmpty sealed
    simp [empty] at owns
  have word : counted.foreignWord = reference.foreignOwners.card := by
    simp [related.foreignWord, unsealed]
  have live : counted.foreignWord > 0 ∧ counted.foreignWord < limit := by
    rw [word]
    exact ⟨Finset.card_pos.mpr ⟨owner, owns⟩, related.foreignBound⟩
  unfold referenceReleaseForeign countedReleaseForeign
  rw [if_pos owns, if_pos live]
  exact .some (release_foreign_corresponds owner related owns)

omit [DecidableEq Lease] in
theorem join_result_correspondence {limit : Nat} (slot : Nat)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (pending : slot ∈ reference.unjoined) :
    Option.Rel (Corresponds limit) (referenceJoinSlot slot reference) (countedJoinSlot counted) := by
  have live : counted.remainingJoins > 0 := by
    rw [related.joins]
    exact Finset.card_pos.mpr ⟨slot, pending⟩
  by_cases joining : reference.phase = .joining
  · have countedJoining : counted.phase = .joining := related.phase.trans joining
    unfold referenceJoinSlot countedJoinSlot
    rw [if_pos ⟨joining, pending⟩, if_pos ⟨countedJoining, live⟩]
    exact .some (joined_slot_corresponds slot related pending)
  · simp only [referenceJoinSlot, countedJoinSlot, related.phase, joining,
      false_and, ↓reduceIte]
    exact .none

omit [DecidableEq Lease] in
theorem finish_result_correspondence {limit : Nat} (success : Bool)
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) :
    Option.Rel (Corresponds limit) (referenceFinish success reference) (countedFinish success counted) := by
  by_cases allowed : reference.phase = .joining ∧ (success = true → reference.unjoined = ∅)
  · have countedAllowed : counted.phase = .joining ∧ (success = true → counted.remainingJoins = 0) := by
      simpa only [related.phase, related.joins, Finset.card_eq_zero] using allowed
    unfold referenceFinish countedFinish
    rw [if_pos allowed, if_pos countedAllowed]
    exact .some (finish_corresponds success related allowed.1 allowed.2)
  · have referenceRefused : referenceFinish success reference = none := by
      unfold referenceFinish
      rw [if_neg allowed]
    have countedRefused := (finish_refused_iff success related).mpr referenceRefused
    rw [referenceRefused, countedRefused]
    exact .none

inductive Action (Lease : Type uLease) where
  | enter (owner : Lease)
  | leave (owner : Lease)
  | reserve (owner : Lease) (observed : Nat) (wins : Bool)
  | releaseForeign (owner : Lease)
  | begin (sealForeign : Bool)
  | joinSlot (slot : Nat)
  | finish (success : Bool)
deriving DecidableEq, Repr

/-- Aggregate counters do not manufacture ownership. These receipts are the
caller's independently established lease/worker obligations. -/
inductive Authorized (state : Reference Lease Checkpoint) : Action Lease → Prop where
  | enter (owner : Lease) (fresh : owner ∉ state.episodes) : Authorized state (.enter owner)
  | leave (owner : Lease) (owns : owner ∈ state.episodes) : Authorized state (.leave owner)
  | reserve (owner : Lease) (observed : Nat) (wins : Bool)
      (fresh : owner ∉ state.foreignOwners) : Authorized state (.reserve owner observed wins)
  | releaseForeign (owner : Lease) (owns : owner ∈ state.foreignOwners) :
      Authorized state (.releaseForeign owner)
  | begin (sealForeign : Bool) : Authorized state (.begin sealForeign)
  | joinSlot (slot : Nat) (pending : slot ∈ state.unjoined) : Authorized state (.joinSlot slot)
  | finish (success : Bool) : Authorized state (.finish success)

def referenceStep (limit : Nat) (state : Reference Lease Checkpoint) :
    Action Lease → Option (Reference Lease Checkpoint)
  | .enter owner => referenceEnter limit owner state
  | .leave owner => referenceLeave owner state
  | .reserve owner observed wins => referenceReserve limit observed wins owner state
  | .releaseForeign owner => referenceReleaseForeign owner state
  | .begin sealForeign => referenceBegin sealForeign state
  | .joinSlot slot => referenceJoinSlot slot state
  | .finish success => referenceFinish success state

def countedStep (limit : Nat) (state : Counted Checkpoint) : Action Lease → Option (Counted Checkpoint)
  | .enter _ => countedEnter limit state
  | .leave _ => countedLeave state
  | .reserve _ observed wins => countedReserve limit observed wins state
  | .releaseForeign _ => countedReleaseForeign limit state
  | .begin sealForeign => countedBegin limit sealForeign state
  | .joinSlot _ => countedJoinSlot state
  | .finish success => countedFinish success state

/-- Admission, refusal and every committed protocol update are reflected
under actual owner receipts, including lost/spurious reservation attempts. -/
theorem step_correspondence {limit : Nat} {action : Action Lease}
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (authority : Authorized reference action) :
    Option.Rel (Corresponds limit) (referenceStep limit reference action)
      (countedStep limit counted action) := by
  cases authority with
  | enter owner fresh => exact enter_result_correspondence owner related fresh
  | leave owner owns => exact leave_result_correspondence owner related owns
  | reserve owner observed wins fresh => exact reserve_result_correspondence observed wins owner related fresh
  | releaseForeign owner owns => exact release_foreign_result_correspondence owner related owns
  | begin sealForeign => exact begin_result_correspondence sealForeign related
  | joinSlot slot pending => exact join_result_correspondence slot related pending
  | finish success => exact finish_result_correspondence success related

/-- Preservation is derived from the independent operation results. -/
theorem step_preserved {limit : Nat} {action : Action Lease}
    {reference next : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted) (authority : Authorized reference action)
    (accepted : referenceStep limit reference action = some next) :
    ∃ countedNext, countedStep limit counted action = some countedNext ∧
      Corresponds limit next countedNext := by
  have results := step_correspondence related authority
  rw [accepted] at results
  generalize returned : countedStep limit counted action = result at results
  cases results with
  | some nextRelated => exact ⟨_, rfl, nextRelated⟩

/-- Under the same owner receipts, a counted protocol transition cannot
invent an accepted reference operation. -/
theorem step_reflected {limit : Nat} {action : Action Lease}
    {reference : Reference Lease Checkpoint} {counted next : Counted Checkpoint}
    (related : Corresponds limit reference counted) (authority : Authorized reference action)
    (accepted : countedStep limit counted action = some next) :
    ∃ referenceNext, referenceStep limit reference action = some referenceNext ∧
      Corresponds limit referenceNext next := by
  have results := step_correspondence related authority
  rw [accepted] at results
  generalize returned : referenceStep limit reference action = result at results
  cases results with
  | some nextRelated => exact ⟨_, rfl, nextRelated⟩

abbrev OwnedStep (limit : Nat) (before after : Reference Lease Checkpoint) : Prop :=
  ∃ action, Authorized before action ∧ referenceStep limit before action = some after

abbrev CountedStep (limit : Nat) (before after : Counted Checkpoint) : Prop :=
  ∃ action : Action Lease, countedStep limit before action = some after

/-- Reuse the ordinary reflexive/transitive closure: this is reachability
refinement, not a replacement event-history or replay construction. -/
theorem owned_runs_preserved {limit : Nat} {before after : Reference Lease Checkpoint}
    (run : Relation.ReflTransGen (OwnedStep limit) before after)
    {counted : Counted Checkpoint} (related : Corresponds limit before counted) :
    ∃ countedAfter,
      Relation.ReflTransGen (CountedStep (Lease := Lease) limit) counted countedAfter ∧
      Corresponds limit after countedAfter := by
  induction run generalizing counted with
  | refl => exact ⟨counted, .refl, related⟩
  | tail prior step ih =>
      obtain ⟨middle, countedPrior, middleRelated⟩ := ih related
      obtain ⟨action, authority, accepted⟩ := step
      obtain ⟨last, countedAccepted, lastRelated⟩ := step_preserved middleRelated authority accepted
      exact ⟨last, countedPrior.tail ⟨action, countedAccepted⟩, lastRelated⟩

theorem step_preserves_checkpoint {limit : Nat} {action : Action Lease}
    {before after : Reference Lease Checkpoint}
    (accepted : referenceStep limit before action = some after) :
    after.checkpoint = before.checkpoint := by
  cases action <;>
    simp only [referenceStep, referenceEnter, referenceLeave, referenceReserve,
      referenceReleaseForeign, referenceBegin, referenceJoinSlot, referenceFinish] at accepted
  all_goals split at accepted
  all_goals try { exact (congrArg Reference.checkpoint (Option.some.inj accepted)).symm }
  all_goals cases accepted

theorem step_never_reopens {limit : Nat} {action : Action Lease}
    {before after : Reference Lease Checkpoint} (closed : before.phase ≠ .open)
    (accepted : referenceStep limit before action = some after) :
    after.phase ≠ .open := by
  cases action <;>
    simp only [referenceStep, referenceEnter, referenceLeave, referenceReserve,
      referenceReleaseForeign, referenceBegin, referenceJoinSlot, referenceFinish] at accepted
  all_goals split at accepted
  all_goals first | rw [Option.some.injEq] at accepted | cases accepted
  all_goals rw [← accepted]
  all_goals first
    | exact closed
    | exact begin_closes_episode_admission _
    | split <;> simp

/-- Once committed, closure remains closed through release, joins, failure
and retry. No accepted later episode can race reclamation. -/
theorem owned_run_never_reopens {limit : Nat}
    {before after : Reference Lease Checkpoint} (closed : before.phase ≠ .open)
    (run : Relation.ReflTransGen (OwnedStep limit) before after) : after.phase ≠ .open := by
  induction run with
  | refl => exact closed
  | tail prior step ih =>
      obtain ⟨action, _, accepted⟩ := step
      exact step_never_reopens ih accepted

theorem owned_run_preserves_checkpoint {limit : Nat}
    {before after : Reference Lease Checkpoint}
    (run : Relation.ReflTransGen (OwnedStep limit) before after) :
    after.checkpoint = before.checkpoint := by
  induction run with
  | refl => rfl
  | tail prior step ih =>
      obtain ⟨action, _, accepted⟩ := step
      exact (step_preserves_checkpoint accepted).trans ih

omit [DecidableEq Lease] in
/-- Completion and foreign sealing jointly establish absence of every
tracked owner and pending join. This does not assert that an external join
service has succeeded unless its consumed-slot receipts were supplied. -/
theorem joined_sealed_is_quiescent {limit : Nat}
    {reference : Reference Lease Checkpoint} {counted : Counted Checkpoint}
    (related : Corresponds limit reference counted)
    (joined : reference.phase = .joined) (sealed : reference.foreignSealed = true) :
    reference.episodes = ∅ ∧ reference.foreignOwners = ∅ ∧ reference.unjoined = ∅ ∧
      counted.episodes = 0 ∧ counted.foreignWord = limit ∧ counted.remainingJoins = 0 := by
  have episodesEmpty := related.closedEmpty (by simp [joined])
  have foreignEmpty := related.sealedEmpty sealed
  have joinsEmpty := related.joinedEmpty joined
  refine ⟨episodesEmpty, foreignEmpty, joinsEmpty, ?_, ?_, ?_⟩
  · simp [related.episodes, episodesEmpty]
  · simp [related.foreignWord, sealed]
  · simp [related.joins, joinsEmpty]

end Quiescence

namespace Quiescence.Controls

abbrev Checkpoint := List Nat × List Nat

/-- Committed duplicates and pending alternatives are intentionally distinct
from the aggregate lifecycle counters. -/
def checkpoint : Checkpoint := ([4, 4], [9, 16])

def idle : Reference Nat Checkpoint :=
  ⟨.open, ∅, ∅, false, {0, 1}, checkpoint⟩

def idleCounted : Counted Checkpoint := ⟨.open, 0, 0, 2, ([4, 4], [9, 16])⟩

def closing : Reference Nat Checkpoint := { idle with phase := .joining, foreignSealed := true }
def closingCounted : Counted Checkpoint := { idleCounted with phase := .joining, foreignWord := 8 }
def partiallyJoined : Reference Nat Checkpoint := { closing with unjoined := {1} }
def partialCounted : Counted Checkpoint := { closingCounted with remainingJoins := 1 }
def retry : Reference Nat Checkpoint := { partiallyJoined with phase := .retry }
def retryCounted : Counted Checkpoint := { partialCounted with phase := .retry }
def busy : Reference Nat Checkpoint := { idle with episodes := {11} }
def foreignBusy : Reference Nat Checkpoint := { idle with foreignOwners := {17} }
def foreignBusyCounted : Counted Checkpoint := { idleCounted with foreignWord := 1 }

theorem idle_corresponds : Corresponds 8 idle idleCounted := by
  constructor <;> decide

theorem closure_is_atomic_and_corresponding :
    referenceBegin true idle = some closing ∧
      countedBegin 8 true idleCounted = some closingCounted ∧
      Corresponds 8 closing closingCounted := by
  refine ⟨by decide, by decide, ?_⟩
  exact begin_corresponds true idle_corresponds (by decide)

theorem partial_join_and_retry :
    referenceJoinSlot 0 closing = some partiallyJoined ∧
      countedJoinSlot closingCounted = some partialCounted ∧
      referenceFinish false partiallyJoined = some retry ∧
      countedFinish false partialCounted = some retryCounted ∧
      referenceEnter 8 21 retry = none ∧ countedEnter 8 retryCounted = none ∧
      retry.checkpoint = ([4, 4], [9, 16]) := by
  decide

theorem remaining_worker_prevents_completion :
    referenceFinish true partiallyJoined = none ∧ countedFinish true partialCounted = none := by
  decide

/-- Positive: a failed join retains the remaining slot, which a later
successful retry consumes before completion. The checkpoint is unchanged. -/
theorem retry_consumes_remaining_worker_before_completion :
    referenceBegin true retry = some { retry with phase := .joining } ∧
      countedBegin 8 true retryCounted = some { retryCounted with phase := .joining } ∧
      referenceJoinSlot 1 { retry with phase := .joining } =
        some { closing with unjoined := ∅ } ∧
      countedJoinSlot { retryCounted with phase := .joining } =
        some { closingCounted with remainingJoins := 0 } ∧
      referenceFinish true { closing with unjoined := ∅ } =
        some { closing with phase := .joined, unjoined := ∅ } ∧
      countedFinish true { closingCounted with remainingJoins := 0 } =
        some { closingCounted with phase := .joined, remainingJoins := 0 } ∧
      Corresponds 8 { closing with phase := .joined, unjoined := ∅ }
        { closingCounted with phase := .joined, remainingJoins := 0 } := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  constructor <;> decide

theorem busy_refusal_retains_complete_checkpoint :
    retainOnRefusal busy (referenceBegin true busy) = busy ∧
      (retainOnRefusal busy (referenceBegin true busy)).checkpoint = ([4, 4], [9, 16]) := by
  decide

theorem foreign_owner_refuses_sealing :
    referenceBegin true foreignBusy = none ∧
      countedBegin 8 true foreignBusyCounted = none := by
  decide

/-- Negative: omitting episode registration makes a counter-only shutdown
accept a boundary that the independently tracked live owner forbids. -/
theorem omitted_episode_registration_discriminated :
    referenceBegin true busy = none ∧ countedBegin 8 true idleCounted = some closingCounted ∧
      ¬ Corresponds 8 busy idleCounted := by
  refine ⟨by decide, by decide, ?_⟩
  intro related
  have impossible := related.episodes
  simp [busy, idle, idleCounted] at impossible

/-- The episode counter may reach its limit, while the foreign-owner counter
must reserve the sentinel. Neither can wrap into a quiescent state. -/
theorem saturated_admission_refuses_without_wrapping :
    Corresponds 2 { idle with episodes := {11, 12}, foreignOwners := {17} }
      { idleCounted with episodes := 2, foreignWord := 1 } ∧
      referenceEnter 2 13 { idle with episodes := {11, 12} } = none ∧
      countedEnter 2 { idleCounted with episodes := 2 } = none ∧
      referenceReserve 2 1 true 18 foreignBusy = none ∧
      countedReserve 2 1 true foreignBusyCounted = none := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  constructor <;> decide

theorem worker_only_closure_does_not_seal_foreign_owners :
    referenceBegin false foreignBusy = some { foreignBusy with phase := .joining } ∧
      countedBegin 8 false foreignBusyCounted = some { foreignBusyCounted with phase := .joining } ∧
      (referenceReserve 8 1 true 18 { foreignBusy with phase := .joining }).map
        (fun state => state.foreignOwners.card) = some 2 := by
  decide

theorem sealed_reservation_and_reentrant_entry_refused :
    referenceReserve 8 0 true 17 closing = none ∧
      countedReserve 8 0 true closingCounted = none ∧
      referenceEnter 8 21 closing = none ∧ countedEnter 8 closingCounted = none := by
  decide

theorem weak_failure_retains_no_foreign_owner :
    retainOnRefusal idle (referenceReserve 8 0 false 17 idle) = idle ∧
      retainOnRefusal idleCounted (countedReserve 8 0 false idleCounted) = idleCounted := by
  decide

theorem stale_reservation_loses_after_another_owner :
    referenceReserve 8 0 true 18 foreignBusy = none ∧
      countedReserve 8 0 true foreignBusyCounted = none := by
  decide

/-- Negative: checking an old quiescent snapshot then closing the current
state admits a live owner into the reclamation boundary. -/
def staleClose (observed current : Counted Checkpoint) : Option (Counted Checkpoint) :=
  if countedMayBegin 8 true observed then
    some { current with phase := .joining, foreignWord := 8 }
  else none

theorem stale_close_discriminated :
    staleClose idleCounted foreignBusyCounted = some
        { foreignBusyCounted with phase := .joining, foreignWord := 8 } ∧
      countedBegin 8 true foreignBusyCounted = none ∧
      ¬ Corresponds 8 { foreignBusy with phase := .joining, foreignSealed := true }
          { foreignBusyCounted with phase := .joining, foreignWord := 8 } := by
  refine ⟨by decide, by decide, ?_⟩
  intro related
  have impossible := related.sealedEmpty rfl
  simp [foreignBusy, idle] at impossible

/-- Negative: a positive aggregate count cannot identify the owner to be
released. The caller's owner receipt is necessary. -/
theorem wrong_owner_is_not_a_counter_certificate :
    referenceReleaseForeign 18 foreignBusy = none ∧
      countedReleaseForeign 8 foreignBusyCounted = some
        { foreignBusyCounted with foreignWord := 0 } ∧
      ¬ Authorized foreignBusy (.releaseForeign 18) := by
  refine ⟨by decide, by decide, ?_⟩
  intro authority
  cases authority with
  | releaseForeign owner owns => simp [foreignBusy, idle] at owns

end Quiescence.Controls

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
