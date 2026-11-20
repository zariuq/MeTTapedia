import Mettapedia.Machines.Kernel.InvocationContext

/-!
# Task-local IPC v2 waiting

Authority to submit comes from the current run and a held object grant.
Here one already accepted wait owns its outbox and result until collection
or task exit. Dispatch alone may deliver a parked result, and only to
the task that parked. A spurious wake keeps the wait available for retry.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.IpcTaskWait

open InvocationContext (ExecutionClass Selection Task)

structure Ticket where
  owner : Task
  object : Nat
  generation : Nat
  deriving DecidableEq, Repr

def Ticket.fromSelection (selection : Selection) (domain run object generation : Nat) :
    Option Ticket :=
  (selection.context domain run).map fun context =>
    ⟨context.task, object, generation⟩

inductive Slot (Value : Type) where
  | idle
  | pending (ticket : Ticket) (parked : Bool)
  | ready (ticket : Ticket) (parked : Bool) (value : Value)
  deriving DecidableEq, Repr

inductive WaitResult (Value : Type) where
  | again
  | park (execution : ExecutionClass)
  | delivered (value : Value)
  deriving DecidableEq, Repr

variable {Value : Type}

def wait (slot : Slot Value) (current : Task) (wakeAlreadyPending : Bool) :
    Slot Value × WaitResult Value :=
  match slot with
  | .idle => (.idle, .again)
  | .pending ticket _ =>
      if ticket.owner = current ∧ wakeAlreadyPending = false then
        (.pending ticket true, .park current.execution)
      else (slot, .again)
  | .ready ticket _ value =>
      if ticket.owner = current then (.idle, .delivered value) else (slot, .again)

def complete (slot : Slot Value) (receipt : Ticket) (value : Value) :
    Slot Value × Option Task :=
  match slot with
  | .pending ticket parked =>
      if ticket = receipt then
        (.ready ticket parked value, if parked then some ticket.owner else none)
      else (slot, none)
  | _ => (slot, none)

def dispatch (slot : Slot Value) (current : Task) : Slot Value × Option Value :=
  match slot with
  | .pending ticket true =>
      if ticket.owner = current then (.pending ticket false, none) else (slot, none)
  | .ready ticket true value =>
      if ticket.owner = current then (.idle, some value) else (slot, none)
  | _ => (slot, none)

def exit (slot : Slot Value) (task : Task) : Slot Value :=
  match slot with
  | .pending ticket _ | .ready ticket _ _ =>
      if ticket.owner = task then .idle else slot
  | .idle => .idle

theorem stale_selection_cannot_issue (domain run selected task oldRun object generation : Nat)
    (stale : oldRun ≠ run) :
    Ticket.fromSelection (.worker selected task oldRun true) domain run object generation = none := by
  simp [Ticket.fromSelection, InvocationContext.Selection.context, stale]

theorem pending_wait_uses_task_class (ticket : Ticket) (parked : Bool) :
    wait (.pending ticket parked : Slot Value) ticket.owner false =
      (.pending ticket true, .park ticket.owner.execution) := by
  simp [wait]

theorem wrong_receipt_preserves (ticket receipt : Ticket) (parked : Bool) (value : Value)
    (wrong : ticket ≠ receipt) :
    complete (.pending ticket parked) receipt value = (.pending ticket parked, none) := by
  simp [complete, wrong]

theorem duplicate_preserves_first (ticket : Ticket) (parked : Bool) (value second : Value) :
    complete (complete (.pending ticket parked) ticket value).1 ticket second =
      (.ready ticket parked value, none) := by
  simp [complete]

theorem completion_of_parked_wait_targets_owner (ticket : Ticket) (value : Value) :
    complete (.pending ticket true) ticket value =
      (.ready ticket true value, some ticket.owner) := by
  simp [complete]

theorem parked_completion_delivered_on_dispatch (ticket : Ticket) (value : Value) :
    dispatch (complete (.pending ticket true) ticket value).1 ticket.owner = (.idle, some value) := by
  simp [complete, dispatch]

theorem spurious_dispatch_retains_wait (ticket : Ticket) (value : Value) :
    let resumed := dispatch (.pending ticket true : Slot Value) ticket.owner
    resumed.2 = none ∧
      complete resumed.1 ticket value = (.ready ticket false value, none) ∧
      wait (complete resumed.1 ticket value).1 ticket.owner false = (.idle, .delivered value) := by
  simp [dispatch, complete, wait]

theorem unrelated_dispatch_preserves (ticket : Ticket) (task : Task) (value : Value)
    (different : ticket.owner ≠ task) :
    dispatch (.ready ticket true value) task = (.ready ticket true value, none) := by
  simp [dispatch, different]

theorem unrelated_exit_preserves (ticket : Ticket) (task : Task) (slot : Slot Value)
    (different : ticket.owner ≠ task)
    (held : (∃ parked, slot = .pending ticket parked) ∨
            (∃ parked value, slot = .ready ticket parked value)) :
    exit slot task = slot := by
  rcases held with ⟨parked, rfl⟩ | ⟨parked, value, rfl⟩ <;> simp [exit, different]

/-- An interleaving of other continuations cannot steal an already posted result,
even for tasks that share the same run's authority. -/
theorem other_dispatches_preserve_result (ticket : Ticket) (value : Value) (tasks : List Task)
    (different : ∀ task ∈ tasks, ticket.owner ≠ task) :
    tasks.foldl (fun slot task => (dispatch slot task).1) (.ready ticket true value) =
      .ready ticket true value := by
  induction tasks with
  | nil => rfl
  | cons task rest ih =>
      simp only [List.foldl_cons]
      rw [unrelated_dispatch_preserves ticket task value (different task (by simp))]
      exact ih (fun other member => different other (by simp [member]))

inductive Event (Value : Type) where
  | signal (receipt : Ticket) (value : Value)
  | resume (task : Task)
  | poll (task : Task) (wakeAlreadyPending : Bool)
  | retire (task : Task)

def step (slot : Slot Value) : Event Value → Slot Value × Option Value
  | .signal receipt value => ((complete slot receipt value).1, none)
  | .resume task => dispatch slot task
  | .poll task pending =>
      let (next, result) := wait slot task pending
      match result with
      | .delivered value => (next, some value)
      | _ => (next, none)
  | .retire task => (exit slot task, none)

def run (slot : Slot Value) : List (Event Value) → Slot Value × List Value
  | [] => (slot, [])
  | event :: events =>
      let (next, value) := step slot event
      let (last, values) := run next events
      (last, value.toList ++ values)

theorem idle_stays_idle (events : List (Event Value)) :
    run .idle events = (.idle, []) := by
  induction events with
  | nil => rfl
  | cons event events ih => cases event <;> simp [run, step, wait, complete, dispatch, exit, ih]

theorem delivered_step_consumes (slot : Slot Value) (event : Event Value) (value : Value)
    (delivered : (step slot event).2 = some value) :
    (step slot event).1 = .idle := by
  cases event with
  | signal | retire => simp [step] at delivered
  | resume task =>
      cases slot with
      | idle => simp [step, dispatch] at delivered
      | pending ticket parked =>
          cases parked <;> by_cases same : ticket.owner = task <;>
            simp [step, dispatch, same] at delivered
      | ready ticket parked result =>
          cases parked <;> by_cases same : ticket.owner = task <;>
            simp_all [step, dispatch]
  | poll task pending =>
      cases slot with
      | idle => simp [step, wait] at delivered
      | pending ticket parked =>
          by_cases canPark : ticket.owner = task ∧ pending = false <;>
            simp [step, wait, canPark] at delivered
      | ready ticket parked result =>
          by_cases same : ticket.owner = task <;> simp_all [step, wait]

theorem single_wait_delivers_at_most_once (slot : Slot Value) (events : List (Event Value)) :
    (run slot events).2.length ≤ 1 := by
  induction events generalizing slot with
  | nil => simp [run]
  | cons event events ih =>
      cases delivered : (step slot event).2 with
      | none => simpa [run, delivered] using ih (step slot event).1
      | some value =>
          have idle := delivered_step_consumes slot event value delivered
          simp [run, delivered, idle, idle_stays_idle]

private def worker : Task := ⟨1073741824, 7, .worker⟩
private def main : Task := ⟨7, 7, .main⟩
private def held : Ticket := ⟨worker, 3, 5⟩

example : wait (.pending held false : Slot Nat) worker false =
    (.pending held true, .park .worker) := by decide

example : run (.pending held true : Slot Nat)
    [.signal held 42, .resume main, .retire main, .resume worker, .poll worker false] =
    (.idle, [42]) := by decide

example : run (.pending held true : Slot Nat)
    [.signal { held with generation := 4 } 42, .resume worker, .poll main false] =
    (.pending held false, []) := by decide

example : run (.pending held true : Slot Nat)
    [.retire worker, .signal held 42, .resume worker] = (.idle, []) := by decide

#print axioms pending_wait_uses_task_class
#print axioms other_dispatches_preserve_result
#print axioms single_wait_delivers_at_most_once

end Mettapedia.Machines.Kernel.IpcTaskWait
