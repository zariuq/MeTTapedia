import Mettapedia.Logic.InformationFlow.ObservationalSecurity
import Mathlib.Data.List.Count
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!
# Reserved-slot scheduling and logical-time noninterference

A public finite schedule selects isolated tasks. A task transition reads only
that task's local state, updates only that state, and may emit a value at the
task's fixed policy label. Every selected slot consumes one logical tick,
including idle and completed tasks. Visible observations retain task states,
total ticks, event timestamps, event order, and event multiplicity.

The two-run proof derives the step invariant from this executable transition;
it does not assume that the whole scheduler is already noninterfering.

Logical slots are not a wall-clock C theorem. Realizing a slot requires bounded
or preemptible local work, deadline padding, and suitable isolation of shared
hardware and runtime resources. The model has no shared mutable task state,
secret-dependent scheduling policy, dynamic task creation, or cross-task
messages. Such features require further refinement and policy proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InformationFlow.TimedSchedule

universe uTask uLocal uValue uLabel

variable {Task : Type uTask} {Local : Type uLocal} {Value : Type uValue}
variable {Label : Type uLabel}

structure Event (Task : Type uTask) (Value : Type uValue) where
  time : Nat
  task : Task
  value : Value
deriving DecidableEq, Repr

structure State (Task : Type uTask) (Local : Type uLocal) (Value : Type uValue) where
  tasks : Task → Local
  ticks : Nat
  events : List (Event Task Value)

/-- A task's code sees its identity and its own state only. The optional
output is labeled by the scheduler, never by the task. -/
abbrev Transition (Task : Type uTask) (Local : Type uLocal) (Value : Type uValue) :=
  Task → Local → Local × Option Value

def emittedEvents (task : Task) (time : Nat) (output : Option Value) :
    List (Event Task Value) :=
  output.toList.map fun value => ⟨time, task, value⟩

/-- Reserve a tick even when the selected task emits nothing or is already
done. Other task states are unchanged. -/
def step [DecidableEq Task] (transition : Transition Task Local Value)
    (selected : Task) (state : State Task Local Value) : State Task Local Value :=
  let result := transition selected (state.tasks selected)
  { tasks := Function.update state.tasks selected result.1
    ticks := state.ticks + 1
    events := state.events ++ emittedEvents selected state.ticks result.2 }

def run [DecidableEq Task] (transition : Transition Task Local Value) :
    List Task → State Task Local Value → State Task Local Value
  | [], state => state
  | selected :: schedule, state => run transition schedule (step transition selected state)

def initial (tasks : Task → Local) : State Task Local Value := ⟨tasks, 0, []⟩

/-- The fixed task policy controls both state and output visibility. -/
def visibleEvents [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (events : List (Event Task Value)) : List (Event Task Value) :=
  events.filter fun event => decide (policy event.task ≤ clearance)

def visibleTasks [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label) (tasks : Task → Local) :
    Task → Option Local :=
  fun task => if policy task ≤ clearance then some (tasks task) else none

def observe [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label) (state : State Task Local Value) :
    (Task → Option Local) × Nat × List (Event Task Value) :=
  (visibleTasks policy clearance state.tasks,
    state.ticks, visibleEvents policy clearance state.events)

structure LowEquivalent [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (left right : State Task Local Value) : Prop where
  tasks : ∀ task, policy task ≤ clearance → left.tasks task = right.tasks task
  ticks : left.ticks = right.ticks
  events : visibleEvents policy clearance left.events =
    visibleEvents policy clearance right.events

theorem LowEquivalent.observe_eq [Preorder Label] [DecidableLE Label]
    {policy : Task → Label} {clearance : Label}
    {left right : State Task Local Value}
    (related : LowEquivalent policy clearance left right) :
    observe policy clearance left = observe policy clearance right := by
  have states : visibleTasks policy clearance left.tasks =
      visibleTasks policy clearance right.tasks := by
    funext task
    by_cases visible : policy task ≤ clearance
    · simp [visibleTasks, visible, related.tasks task visible]
    · simp [visibleTasks, visible]
  exact Prod.ext states (Prod.ext related.ticks related.events)

@[simp] theorem step_ticks [DecidableEq Task]
    (transition : Transition Task Local Value) (selected : Task)
    (state : State Task Local Value) :
    (step transition selected state).ticks = state.ticks + 1 := rfl

@[simp] theorem step_selected [DecidableEq Task]
    (transition : Transition Task Local Value) (selected : Task)
    (state : State Task Local Value) :
    (step transition selected state).tasks selected =
      (transition selected (state.tasks selected)).1 := by
  simp [step]

theorem step_other [DecidableEq Task]
    (transition : Transition Task Local Value) {selected other : Task}
    (different : other ≠ selected) (state : State Task Local Value) :
    (step transition selected state).tasks other = state.tasks other := by
  simp [step, Function.update_of_ne different]

theorem visibleEvents_append [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (left right : List (Event Task Value)) :
    visibleEvents policy clearance (left ++ right) =
      visibleEvents policy clearance left ++ visibleEvents policy clearance right := by
  exact List.filter_append left right

theorem visibleEvents_emitted [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label) (task : Task) (time : Nat)
    (output : Option Value) :
    visibleEvents policy clearance (emittedEvents task time output) =
      if policy task ≤ clearance then emittedEvents task time output else [] := by
  cases output <;> by_cases visible : policy task ≤ clearance <;>
    simp [visibleEvents, emittedEvents, visible]

/-- Locality and the unconditional reserved tick establish the complete
two-run step invariant, including timestamps of published events. -/
theorem step_noninterference [DecidableEq Task]
    [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (transition : Transition Task Local Value) (selected : Task)
    {left right : State Task Local Value}
    (related : LowEquivalent policy clearance left right) :
    LowEquivalent policy clearance
      (step transition selected left) (step transition selected right) := by
  constructor
  · intro task visible
    by_cases same : task = selected
    · subst task
      simp only [step_selected, related.tasks selected visible]
    · rw [step_other transition same, step_other transition same]
      exact related.tasks task visible
  · simp [related.ticks]
  · change visibleEvents policy clearance
        (left.events ++ emittedEvents selected left.ticks
          (transition selected (left.tasks selected)).2) =
      visibleEvents policy clearance
        (right.events ++ emittedEvents selected right.ticks
          (transition selected (right.tasks selected)).2)
    rw [visibleEvents_append, visibleEvents_append, related.events,
      visibleEvents_emitted, visibleEvents_emitted]
    by_cases visible : policy selected ≤ clearance
    · simp [visible, related.ticks, related.tasks selected visible]
    · simp [visible]

theorem run_noninterference [DecidableEq Task]
    [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (transition : Transition Task Local Value) (schedule : List Task)
    {left right : State Task Local Value}
    (related : LowEquivalent policy clearance left right) :
    LowEquivalent policy clearance
      (run transition schedule left) (run transition schedule right) := by
  induction schedule generalizing left right with
  | nil => exact related
  | cons selected schedule ih =>
    exact ih (step_noninterference policy clearance transition selected related)

/-- For a fixed public schedule, agreement of the initial visible local
states suffices. No equality of secret local states is required. -/
theorem schedule_noninterference [DecidableEq Task]
    [Preorder Label] [DecidableLE Label]
    (policy : Task → Label) (clearance : Label)
    (transition : Transition Task Local Value) (schedule : List Task) :
    Mettapedia.Logic.InformationFlow.ObservationalSecurity.Noninterference
      (fun left right : Task → Local =>
        ∀ task, policy task ≤ clearance → left task = right task)
      { observe := observe policy clearance }
      (fun tasks => run transition schedule (initial tasks)) := by
  intro left right related
  apply LowEquivalent.observe_eq
  apply run_noninterference policy clearance transition schedule
  exact ⟨related, rfl, rfl⟩

/-- Logical elapsed time depends solely on the public schedule length. -/
theorem run_ticks [DecidableEq Task]
    (transition : Transition Task Local Value) (schedule : List Task)
    (state : State Task Local Value) :
    (run transition schedule state).ticks = state.ticks + schedule.length := by
  induction schedule generalizing state with
  | nil => simp [run]
  | cons selected schedule ih =>
    simp only [run, ih, step_ticks, List.length_cons]
    omega

/-- A task makes exactly as many local transitions as the public schedule
contains selections of that task. Selections of other tasks do not consume
or alter its local computation. -/
theorem run_task_eq_iterate [DecidableEq Task]
    (transition : Transition Task Local Value) (schedule : List Task)
    (task : Task) (state : State Task Local Value) :
    (run transition schedule state).tasks task =
      (fun localState => (transition task localState).1)^[schedule.count task]
        (state.tasks task) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons selected schedule ih =>
    simp only [run, ih]
    by_cases same : selected = task
    · subst selected
      simp only [List.count_cons_self, Function.iterate_succ_apply, step_selected]
    · rw [List.count_cons_of_ne same, step_other transition (Ne.symm same)]

/-- Fixed cyclic rounds are determined by public task identities only. -/
def cyclicSchedule (round : List Task) : Nat → List Task
  | 0 => []
  | rounds + 1 => round ++ cyclicSchedule round rounds

theorem cyclicSchedule_length (round : List Task) (rounds : Nat) :
    (cyclicSchedule round rounds).length = rounds * round.length := by
  induction rounds with
  | zero => simp [cyclicSchedule]
  | succ rounds ih => simp [cyclicSchedule, ih, Nat.succ_mul, Nat.add_comm]

theorem cyclicSchedule_count [DecidableEq Task]
    (round : List Task) (rounds : Nat) (task : Task) :
    (cyclicSchedule round rounds).count task = rounds * round.count task := by
  induction rounds with
  | zero => simp [cyclicSchedule]
  | succ rounds ih => simp [cyclicSchedule, ih, Nat.succ_mul, Nat.add_comm]

/-- Every listed task receives at least one selection per fixed round, by a
deadline depending only on the public round length. The count is exact even
if a task appears several times in a round. This is service, not a claim that
an arbitrary local computation finishes within one selection. -/
theorem cyclic_service_bound [DecidableEq Task]
    (transition : Transition Task Local Value) (round : List Task)
    (rounds : Nat) (task : Task) (member : task ∈ round)
    (state : State Task Local Value) :
    (run transition (cyclicSchedule round rounds) state).ticks =
      state.ticks + rounds * round.length ∧
    rounds ≤ (cyclicSchedule round rounds).count task ∧
    (run transition (cyclicSchedule round rounds) state).tasks task =
      (fun localState => (transition task localState).1)^[rounds * round.count task]
        (state.tasks task) := by
  constructor
  · rw [run_ticks, cyclicSchedule_length]
  constructor
  · rw [cyclicSchedule_count]
    have positive : 1 ≤ round.count task := List.count_pos_iff.mpr member
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left rounds positive
  · rw [run_task_eq_iterate, cyclicSchedule_count]

namespace Examples

structure Work where
  remaining : Nat
  accumulated : Nat
deriving DecidableEq, Repr

/-- Each active selection adds the remaining amount, then counts down. The
last selection emits the accumulated result; completed tasks remain idle. -/
def countdown (_task : Bool) (work : Work) : Work × Option Nat :=
  match work.remaining with
  | 0 => (work, none)
  | remaining + 1 =>
    let total := work.accumulated + remaining + 1
    (⟨remaining, total⟩, if remaining = 0 then some total else none)

def policy (task : Bool) : Bool := task

def tasks (secret : Work) : Bool → Work :=
  fun task => if task then secret else ⟨3, 10⟩

def publicSchedule : List Bool := cyclicSchedule [true, false] 3

def execute (secret : Work) : State Bool Work Nat :=
  run countdown publicSchedule (initial (tasks secret))

theorem visible_inputs_agree (left right : Work) :
    ∀ task, policy task ≤ false → tasks left task = tasks right task := by
  intro task visible
  cases task
  · rfl
  · exact False.elim ((by decide : ¬ (true : Bool) ≤ false) visible)

/-- The security theorem applies to every secret countdown and accumulator,
not just the finite concrete controls below. -/
theorem countdown_schedule_noninterference (left right : Work) :
    observe policy false (execute left) = observe policy false (execute right) := by
  exact schedule_noninterference policy false countdown publicSchedule
    (tasks left) (tasks right) (visible_inputs_agree left right)

/-- Both worlds compute `10 + 3 + 2 + 1 = 16`. Secret work differs, but
the public result is always emitted at slot 5 and completion takes six ticks. -/
theorem reserved_slots_compute_at_fixed_public_time :
    (execute ⟨0, 100⟩).tasks false = ⟨0, 16⟩ ∧
    (execute ⟨3, 100⟩).tasks false = ⟨0, 16⟩ ∧
    (execute ⟨0, 100⟩).ticks = 6 ∧
    (execute ⟨3, 100⟩).ticks = 6 ∧
    visibleEvents policy false (execute ⟨0, 100⟩).events = [⟨5, false, 16⟩] ∧
    visibleEvents policy false (execute ⟨3, 100⟩).events = [⟨5, false, 16⟩] := by
  decide

/-- The same task code performs different public arithmetic on different
public inputs; the secure observation is not a constant-output machine. -/
theorem public_input_changes_public_result :
    visibleEvents policy false
      (run countdown [false] (initial fun _ => (⟨1, 10⟩ : Work))).events =
        [⟨0, false, 11⟩] ∧
    visibleEvents policy false
      (run countdown [false] (initial fun _ => (⟨1, 20⟩ : Work))).events =
        [⟨0, false, 21⟩] := by
  decide

/-- An unsafe scheduler elides slots when the selected task is done. It uses
the same public task order and the same local transition as the secure one. -/
def runSkippingIdle : List Bool → State Bool Work Nat → State Bool Work Nat
  | [], state => state
  | selected :: schedule, state =>
    if (state.tasks selected).remaining = 0 then
      runSkippingIdle schedule state
    else runSkippingIdle schedule (step countdown selected state)

def executeSkippingIdle (secret : Work) : State Bool Work Nat :=
  runSkippingIdle publicSchedule (initial (tasks secret))

/-- Values, order, and multiplicity are identical, but public emission time
is 2 versus 5. Checking only payloads or bags misses this timing channel. -/
theorem skipping_secret_idle_slots_leaks_time :
    (visibleEvents policy false (executeSkippingIdle ⟨0, 100⟩).events).map Event.value =
      (visibleEvents policy false (executeSkippingIdle ⟨3, 100⟩).events).map Event.value ∧
    (visibleEvents policy false (executeSkippingIdle ⟨0, 100⟩).events).map Event.time = [2] ∧
    (visibleEvents policy false (executeSkippingIdle ⟨3, 100⟩).events).map Event.time = [5] ∧
    (executeSkippingIdle ⟨0, 100⟩).ticks = 3 ∧
    (executeSkippingIdle ⟨3, 100⟩).ticks = 6 := by
  decide

end Examples

end Mettapedia.Machines.InformationFlow.TimedSchedule
