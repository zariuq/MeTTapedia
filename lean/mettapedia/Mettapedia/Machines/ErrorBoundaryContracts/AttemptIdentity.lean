import Mettapedia.Machines.ErrorBoundaryContracts.Supervision

/-!
# Task and attempt identity at a supervision boundary

The core supervisor consumes already-admitted completion events. This wrapper
binds each reply to a stable task identifier and a durable generation, incremented
only when a new reservation grants an attempt. Delayed, duplicated, and misrouted
replies cannot affect a later generation or another task. Restart preserves the
generation and core uncertainty handling remains authoritative.

The identifiers establish correlation, not authentication. Task identifiers must
not be recycled with reset generations while old replies may remain in flight.
Generation persistence, unbounded mathematical counters, and atomic transitions
are modeled; storage durability, bounded-counter rollover, concurrent dispatch,
and physical exactly-once execution are separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity

open RunContracts.ScopedOutcome

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

structure State (Id : Type w) (α : Type u) (ε : Type v) where
  owner : Id
  generation : Nat
  task : Supervision.Task α ε
  deriving DecidableEq, Repr

inductive Control where
  | reserve
  | restart
  | abandonUncertain
  | acknowledge
  | idle
  deriving DecidableEq, Repr

def Control.core : Control → Supervision.Event α ε
  | .reserve => .reserve
  | .restart => .restart
  | .abandonUncertain => .abandonUncertain
  | .acknowledge => .acknowledge
  | .idle => .idle

inductive ReplyKind where
  | complete
  | reconcile
  deriving DecidableEq, Repr

structure Reply (Id : Type w) (α : Type u) (ε : Type v) where
  owner : Id
  generation : Nat
  kind : ReplyKind
  outcome : Outcome α ε
  retryAuthorized : Bool
  deriving DecidableEq, Repr

def Reply.core (reply : Reply Id α ε) : Supervision.Event α ε :=
  match reply.kind with
  | .complete => .complete reply.outcome reply.retryAuthorized
  | .reconcile => .reconcile reply.outcome reply.retryAuthorized

inductive Event (Id : Type w) (α : Type u) (ε : Type v) where
  | control (request : Control)
  | reply (message : Reply Id α ε)
  deriving DecidableEq, Repr

def charge (state : State Id α ε) : Event Id α ε → Nat
  | .control request => Supervision.charge state.task request.core
  | .reply _ => 0

def step [DecidableEq Id] (state : State Id α ε) : Event Id α ε → State Id α ε
  | .control request =>
      ⟨state.owner,
        state.generation + Supervision.charge state.task request.core,
        Supervision.step state.task request.core⟩
  | .reply message =>
      if message.owner = state.owner ∧ message.generation = state.generation then
        { state with task := Supervision.step state.task message.core }
      else state

def run [DecidableEq Id] (state : State Id α ε) : List (Event Id α ε) → State Id α ε
  | [] => state
  | event :: rest => run (step state event) rest

def charges [DecidableEq Id] (state : State Id α ε) : List (Event Id α ε) → Nat
  | [] => 0
  | event :: rest => charge state event + charges (step state event) rest

theorem stale_reply_noop [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (stale : message.generation ≠ state.generation) :
    step state (.reply message) = state := by
  simp [step, stale]

theorem wrong_task_reply_noop [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (wrongTask : message.owner ≠ state.owner) :
    step state (.reply message) = state := by
  simp [step, wrongTask]

/-- Correlation admits an event; the core phase check can still reject it. -/
theorem matching_reply_refines_core [DecidableEq Id] (state : State Id α ε)
    (message : Reply Id α ε) (sameTask : message.owner = state.owner)
    (sameAttempt : message.generation = state.generation) :
    step state (.reply message) =
      { state with task := Supervision.step state.task message.core } := by
  simp [step, sameTask, sameAttempt]

theorem step_owner [DecidableEq Id] (state : State Id α ε) (event : Event Id α ε) :
    (step state event).owner = state.owner := by
  cases event with
  | control request => rfl
  | reply message => simp only [step]; split <;> rfl

theorem step_generation [DecidableEq Id] (state : State Id α ε) (event : Event Id α ε) :
    (step state event).generation = state.generation + charge state event := by
  cases event with
  | control request => rfl
  | reply message => simp only [step, charge, Nat.add_zero]; split <;> rfl

theorem run_owner [DecidableEq Id] (state : State Id α ε) (events : List (Event Id α ε)) :
    (run state events).owner = state.owner := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih => simp only [run, ih, step_owner]

theorem run_generation [DecidableEq Id] (state : State Id α ε) (events : List (Event Id α ε)) :
    (run state events).generation = state.generation + charges state events := by
  induction events generalizing state with
  | nil => simp [run, charges]
  | cons event rest ih => simp [run, charges, ih, step_generation, Nat.add_assoc]

theorem generation_monotone [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    state.generation ≤ (run state events).generation := by
  rw [run_generation]
  omega

theorem restart_keeps_generation [DecidableEq Id] (state : State Id α ε) :
    (step state (.control .restart)).generation = state.generation := by
  simp [step, Control.core, Supervision.charge]

/-- The wrapper preserves the core's exact permit budget even for rejected replies. -/
theorem step_permit_accounting [DecidableEq Id] (state : State Id α ε)
    (event : Event Id α ε) :
    (step state event).task.remaining + charge state event = state.task.remaining := by
  cases event with
  | control request => exact Supervision.step_accounting state.task request.core
  | reply message =>
      simp only [step, charge, Nat.add_zero]
      split
      · have core := Supervision.step_accounting state.task message.core
        cases kindEq : message.kind <;>
          simpa [Reply.core, kindEq, Supervision.charge] using core
      · rfl

theorem run_permit_accounting [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    (run state events).task.remaining + charges state events = state.task.remaining := by
  induction events generalizing state with
  | nil => simp [run, charges]
  | cons event rest ih =>
      have next := ih (step state event)
      have one := step_permit_accounting state event
      simp only [run, charges]
      omega

/-- Generations can advance only as often as the durable permit budget allows. -/
theorem generation_budget [DecidableEq Id] (state : State Id α ε)
    (events : List (Event Id α ε)) :
    (run state events).generation ≤ state.generation + state.task.remaining := by
  rw [run_generation]
  have h := run_permit_accounting state events
  omega

/-! ## Delayed and misrouted reply controls -/

def testInitial : State Nat Nat String := ⟨7, 0, Supervision.initial 2⟩

def attemptTwo : State Nat Nat String :=
  run testInitial
    [.control .reserve, .reply ⟨7, 1, .complete, .raised "retryable", true⟩,
      .control .reserve]

theorem second_attempt_has_new_generation :
    attemptTwo = ⟨7, 2, ⟨0, .active, false⟩⟩ := rfl

theorem old_reply_does_not_settle_new_attempt :
    step attemptTwo (.reply ⟨7, 1, .complete, .value 42, false⟩) = attemptTwo := by decide

theorem current_reply_settles_new_attempt :
    (step attemptTwo (.reply ⟨7, 2, .complete, .value 9, false⟩)).task.phase =
      .terminal (.completed (.value 9)) := by decide

theorem another_task_reply_does_not_settle :
    step attemptTwo (.reply ⟨8, 2, .complete, .value 42, false⟩) = attemptTwo := by decide

/-- The unwrapped core demonstrates the bug that task/attempt correlation prevents. -/
theorem uncorrelated_old_reply_would_settle :
    (Supervision.step attemptTwo.task (.complete (.value 42) false)).phase =
      .terminal (.completed (.value 42)) := rfl

/-- Resetting both identity and generation makes an old reply current again (ABA).
A durable task incarnation or never-reset generation is therefore necessary. -/
theorem recycled_identity_accepts_old_reply :
    (step (step testInitial (.control .reserve))
      (.reply ⟨7, 1, .complete, .value 42, false⟩)).task.phase =
      .terminal (.completed (.value 42)) := by decide

/-- Correlation alone does not turn an uncertain operation into a completed one. -/
theorem ordinary_reply_after_restart_waits_for_reconciliation :
    step (step attemptTwo (.control .restart))
      (.reply ⟨7, 2, .complete, .value 9, false⟩) =
      step attemptTwo (.control .restart) := by decide

theorem current_reconciliation_settles_uncertainty :
    (step (step attemptTwo (.control .restart))
      (.reply ⟨7, 2, .reconcile, .value 9, false⟩)).task.phase =
      .terminal (.completed (.value 9)) := by decide

end Mettapedia.Machines.ErrorBoundaryContracts.AttemptIdentity
