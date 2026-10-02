import Mettapedia.Machines.RunContracts.ScopedOutcome

/-!
# Durable task permits, receipts, and supervision boundaries

Each attempt consumes a persisted permit before an external operation may start.
A completed failure can be retried only with an explicit retry authorization
and while permits remain. A crash during an
attempt instead leaves an uncertain task: it cannot silently consume another
permit and repeat an operation whose effects may already have happened.
Reconciliation must supply a justified outcome, or the service may record an
unresolved dead letter. The latter is terminal accounting, not proof that the
external operation failed. Completed replies reuse `ScopedOutcome.Outcome`.

A task is admitted with a positive initial budget. `initial 0` is intentionally
not admitted by the progress result and grants no operation; an outer service
must reject that configuration rather than enqueue it. An external operation may
start only on a newly committed reservation (`charge = 1`), never merely because
a polled ledger still has phase `active`. The bound counts grants; bounding
physical invocations additionally requires native dispatch at most once per grant.
Completed and reconciled events here must already be admitted for the current
task and attempt. `AttemptIdentity` supplies that separate token-checking layer;
without it, an old reply could incorrectly settle a later active attempt.

The machine proves finite permit accounting, terminal stability, receipt-before-
acknowledgement, and queue advancement past terminal tasks. Conditional progress
is proved for completed failing attempts; unrestricted eventual response is
refuted by a stalled attempt. This finite pure protocol assumes each transition
of the durable ledger is atomic and survives restart. It proves neither physical
storage durability nor exactly-once external effects. The crash-window examples
show why the ledger alone cannot establish the latter.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ErrorBoundaryContracts.Supervision

open RunContracts.ScopedOutcome

universe u v w
variable {α : Type u} {ε : Type v} {Id : Type w}

/-- `unresolved` records an uncertain external effect; it is not a returned fault. -/
inductive Receipt (α : Type u) (ε : Type v) where
  | completed (outcome : Outcome α ε)
  | unresolved
  deriving DecidableEq, Repr

inductive Phase (α : Type u) (ε : Type v) where
  | ready
  | active
  | uncertain
  | terminal (receipt : Receipt α ε)
  deriving DecidableEq, Repr

structure Task (α : Type u) (ε : Type v) where
  remaining : Nat
  phase : Phase α ε
  acknowledged : Bool
  deriving DecidableEq, Repr

def initial (budget : Nat) : Task α ε := ⟨budget, .ready, false⟩

def terminal (task : Task α ε) : Bool :=
  match task.phase with
  | .terminal _ => true
  | _ => false

/-- Persist the consumed permit and active state before invoking an external effect. -/
def reserve (task : Task α ε) : Task α ε :=
  match task.phase, task.remaining with
  | .ready, n + 1 => ⟨n, .active, false⟩
  | _, _ => task

/-- Commit a completed outcome. Only authorized failures with remaining permits
become ready; a raised outcome alone never confers replay authorization. -/
def record (task : Task α ε) (outcome : Outcome α ε) (retryAuthorized : Bool) : Task α ε :=
  match outcome with
  | .value _ => ⟨task.remaining, .terminal (.completed outcome), false⟩
  | .raised _ =>
      if task.remaining = 0 ∨ retryAuthorized = false then
        ⟨task.remaining, .terminal (.completed outcome), false⟩
      else ⟨task.remaining, .ready, false⟩

inductive Event (α : Type u) (ε : Type v) where
  | reserve
  | complete (outcome : Outcome α ε) (retryAuthorized : Bool)
  | restart
  | reconcile (justifiedOutcome : Outcome α ε) (retryAuthorized : Bool)
  | abandonUncertain
  | acknowledge
  | idle
  deriving DecidableEq, Repr

/-- Reconciliation and retry authorization are external service obligations:
this machine infers neither a real outcome from a missing receipt nor replay
safety from an exception. Authorizing retry requires a separate idempotency or
confirmed-no-effect contract. -/
def step (task : Task α ε) : Event α ε → Task α ε
  | .reserve => reserve task
  | .complete outcome retryAuthorized =>
      match task.phase with
      | .active => record task outcome retryAuthorized
      | _ => task
  | .restart =>
      match task.phase with
      | .active => { task with phase := .uncertain }
      | _ => task
  | .reconcile outcome retryAuthorized =>
      match task.phase with
      | .uncertain => record task outcome retryAuthorized
      | _ => task
  | .abandonUncertain =>
      match task.phase with
      | .uncertain => ⟨task.remaining, .terminal .unresolved, false⟩
      | _ => task
  | .acknowledge =>
      if terminal task then { task with acknowledged := true } else task
  | .idle => task

def run (task : Task α ε) : List (Event α ε) → Task α ε
  | [] => task
  | event :: rest => run (step task event) rest

/-- Number of permits actually consumed by a transition, not merely requests. -/
def charge (task : Task α ε) : Event α ε → Nat
  | .reserve =>
      match task.phase, task.remaining with
      | .ready, _ + 1 => 1
      | _, _ => 0
  | _ => 0

/-- The grant is edge-triggered: an already active task grants no new operation. -/
theorem reservation_grant_iff (task : Task α ε) :
    charge task .reserve = 1 ↔ task.phase = .ready ∧ 0 < task.remaining := by
  cases task with
  | mk remaining phase acknowledged =>
      cases phase <;> cases remaining <;> simp [charge]

theorem active_is_not_launch_permission (remaining : Nat) (acknowledged : Bool) :
    charge (⟨remaining, .active, acknowledged⟩ : Task α ε) .reserve = 0 := rfl

def charges (task : Task α ε) : List (Event α ε) → Nat
  | [] => 0
  | event :: rest => charge task event + charges (step task event) rest

@[simp] theorem record_remaining (task : Task α ε) (outcome : Outcome α ε) (retryAuthorized : Bool) :
    (record task outcome retryAuthorized).remaining = task.remaining := by
  cases outcome <;> simp [record]
  split <;> rfl

theorem step_accounting (task : Task α ε) (event : Event α ε) :
    (step task event).remaining + charge task event = task.remaining := by
  cases task with
  | mk remaining phase acknowledged =>
    cases event <;> cases phase <;> cases remaining <;>
      simp [step, reserve, charge, terminal, record_remaining]

theorem run_accounting (task : Task α ε) (events : List (Event α ε)) :
    (run task events).remaining + charges task events = task.remaining := by
  induction events generalizing task with
  | nil => simp [run, charges]
  | cons event rest ih =>
      have next := ih (step task event)
      have one := step_accounting task event
      simp only [run, charges]
      omega

theorem reservations_bounded (budget : Nat) (events : List (Event α ε)) :
    charges (initial budget) events ≤ budget := by
  have h := run_accounting (initial (α := α) (ε := ε) budget) events
  change (run (initial budget) events).remaining + charges (initial budget) events = budget at h
  omega

/-- A restart retains the permit count; active operations become uncertain. -/
theorem restart_preserves_budget (task : Task α ε) :
    (step task .restart).remaining = task.remaining := by
  cases h : task.phase <;> simp [step, h]

/-- No new external operation is authorized while the last effect is uncertain. -/
theorem uncertain_cannot_reserve (remaining : Nat) (acknowledged : Bool) :
    reserve (⟨remaining, .uncertain, acknowledged⟩ : Task α ε) =
      ⟨remaining, .uncertain, acknowledged⟩ := rfl

/-- Terminal receipts are absorbing even when later events request retries. -/
theorem terminal_receipt_stable (remaining : Nat) (receipt : Receipt α ε)
    (acknowledged : Bool) (event : Event α ε) :
    (step ⟨remaining, .terminal receipt, acknowledged⟩ event).phase = .terminal receipt := by
  cases event <;> rfl

theorem terminal_run_stable (task : Task α ε) (receipt : Receipt α ε)
    (isTerminal : task.phase = .terminal receipt) (events : List (Event α ε)) :
    (run task events).phase = .terminal receipt := by
  induction events generalizing task with
  | nil => exact isTerminal
  | cons event rest ih =>
      apply ih
      cases task with
      | mk remaining phase acknowledged =>
          cases isTerminal
          exact terminal_receipt_stable remaining receipt acknowledged event

/-- Acknowledgement requires a committed terminal receipt. -/
def ReceiptBeforeAck (task : Task α ε) : Prop :=
  task.acknowledged = true → terminal task = true

@[simp] theorem record_acknowledged (task : Task α ε) (outcome : Outcome α ε) (retryAuthorized : Bool) :
    (record task outcome retryAuthorized).acknowledged = false := by
  cases outcome <;> simp [record]
  split <;> rfl

theorem step_receipt_before_ack (task : Task α ε) (event : Event α ε)
    (valid : ReceiptBeforeAck task) : ReceiptBeforeAck (step task event) := by
  cases task with
  | mk remaining phase acknowledged =>
    cases event <;> cases phase <;> cases remaining <;>
      simp_all [ReceiptBeforeAck, step, reserve, terminal]

theorem run_receipt_before_ack (budget : Nat) (events : List (Event α ε)) :
    ReceiptBeforeAck (run (initial budget) events) := by
  have general : ∀ (task : Task α ε), ReceiptBeforeAck task →
      ReceiptBeforeAck (run task events) := by
    induction events with
    | nil => intro task h; exact h
    | cons event rest ih =>
        intro task h
        exact ih _ (step_receipt_before_ack task event h)
  exact general _ (by simp [ReceiptBeforeAck, initial])

/-- One completed attempt. The two durable transitions enclose the external call. This helper supplies
an explicit retry authorization for its completed-failure experiment. -/
def completedAttempt (task : Task α ε) (outcome : Outcome α ε) : Task α ε :=
  step (step task .reserve) (.complete outcome true)

def failures (fault : ε) : Nat → Task α ε → Task α ε
  | 0, task => task
  | n + 1, task => failures fault n (completedAttempt task (.raised fault))

/-- Conditional progress: `budget` completed failing attempts exhaust the budget.
A non-returning or interrupted call does not count as a completed attempt. -/
theorem completed_failures_settle (fault : ε) (n : Nat) :
    failures fault (n + 1) (initial (n + 1) : Task α ε) =
      ⟨0, .terminal (.completed (.raised fault)), false⟩ := by
  induction n with
  | zero => simp [failures, completedAttempt, step, reserve, record, initial]
  | succ n ih =>
      change failures fault (n + 1)
        (if n + 1 = 0 ∨ true = false then ⟨0, .terminal (.completed (.raised fault)), false⟩
         else initial (n + 1) : Task α ε) = _
      simpa only [Nat.succ_ne_zero, Bool.true_eq_false, or_self, ↓reduceIte] using ih

theorem completed_success_settles (value : α) (n : Nat) :
    completedAttempt (initial (n + 1) : Task α ε) (.value value) =
      ⟨n, .terminal (.completed (.value value)), false⟩ := rfl

/-- A fault without explicit retry authorization settles even with spare permits. -/
theorem unauthorized_failure_settles (fault : ε) (n : Nat) :
    step (reserve (initial (n + 1) : Task α ε)) (.complete (.raised fault) false) =
      ⟨n, .terminal (.completed (.raised fault)), false⟩ := by
  simp [step, reserve, initial, record]

/-- A finite sequence of completed calls; external time and interruption are absent. -/
def completedTrace (task : Task α ε) : List (Outcome α ε) → Task α ε
  | [] => task
  | outcome :: rest => completedTrace (completedAttempt task outcome) rest

theorem completedTrace_preserves_terminal (task : Task α ε) (receipt : Receipt α ε)
    (isTerminal : task.phase = .terminal receipt) (outcomes : List (Outcome α ε)) :
    (completedTrace task outcomes).phase = .terminal receipt := by
  induction outcomes generalizing task with
  | nil => exact isTerminal
  | cons outcome rest ih =>
      apply ih
      cases task with
      | mk remaining phase acknowledged =>
          cases isTerminal
          rfl

/-- Arbitrary success/failure sequences settle once enough attempts have completed.
There is no premise about the outcome values or about selecting a first fault. -/
theorem enough_completed_attempts_settle (n : Nat) (outcomes : List (Outcome α ε))
    (enough : n + 1 ≤ outcomes.length) :
    terminal (completedTrace (initial (n + 1)) outcomes) = true := by
  induction n generalizing outcomes with
  | zero =>
      cases outcomes with
      | nil => simp at enough
      | cons outcome rest =>
          have settled :
              (completedTrace
                (completedAttempt (initial 1 : Task α ε) outcome) rest).phase =
                .terminal (.completed outcome) := by
            apply completedTrace_preserves_terminal
            cases outcome <;> simp [completedAttempt, step, reserve, initial, record]
          exact (by simp [completedTrace, terminal, settled])
  | succ n ih =>
      cases outcomes with
      | nil => simp at enough
      | cons outcome rest =>
          cases outcome with
          | value value =>
              have settled := completedTrace_preserves_terminal
                (completedAttempt (initial (n + 2)) (.value value : Outcome α ε))
                (.completed (.value value)) (by rfl) rest
              simp only [completedTrace, terminal, settled]
          | raised fault =>
              have tailEnough : n + 1 ≤ rest.length := by simp only [List.length_cons] at enough; omega
              have tailSettles := ih rest tailEnough
              change terminal (completedTrace
                (completedAttempt (initial (n + 2)) (.raised fault)) rest) = true
              simpa only [completedAttempt, step, reserve, initial, record,
                Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Bool.true_eq_false,
                or_self, ↓reduceIte] using tailSettles

/-- FIFO among nonterminal tasks. Terminal poison tasks are skipped, including
those with unresolved effects; no global first-error rule is imposed. -/
def nextTask : List (Id × Task α ε) → Option Id
  | [] => none
  | (id, task) :: rest => if terminal task then nextTask rest else some id

theorem nextTask_skips_terminal_prefix (earlier rest : List (Id × Task α ε))
    (settled : ∀ item ∈ earlier, terminal item.2 = true) :
    nextTask (earlier ++ rest) = nextTask rest := by
  induction earlier with
  | nil => rfl
  | cons item earlier ih =>
      simp only [List.cons_append, nextTask, settled item (by simp), ↓reduceIte]
      apply ih
      intro child mem
      exact settled child (by simp [mem])

theorem settled_head_does_not_block (first second : Id) (done next : Task α ε)
    (isDone : terminal done = true) (isNext : terminal next = false) :
    nextTask [(first, done), (second, next)] = some second := by
  simp [nextTask, isDone, isNext]

/-! ## Positive and negative controls -/

/-- A completed poison task is recorded before acknowledgement, then skipped. -/
theorem poison_task_advances :
    nextTask [(0, step (failures "poison" 3 (initial 3 : Task Nat String)) .acknowledge),
      (1, initial 2)] = some 1 := by decide

/-- An interrupted attempt consumes its permit and blocks unqualified replay. -/
theorem crash_does_not_reset_or_retry :
    run (initial 3 : Task Nat String) [.reserve, .restart, .reserve] =
      ⟨2, .uncertain, false⟩ := rfl

/-- A service can acknowledge an unresolved dead letter without claiming success. -/
theorem unresolved_is_accounted_not_success :
    run (initial 3 : Task Nat String)
      [.reserve, .restart, .abandonUncertain, .acknowledge] =
      ⟨2, .terminal .unresolved, true⟩ := rfl

/-- Idle external work refutes unconditional eventual settlement. -/
theorem stalled_attempt_remains_active (n : Nat) :
    run (reserve (initial 1 : Task Nat String)) (List.replicate n .idle) =
      ⟨0, .active, false⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, run, step] using ih

/-- Terminal skipping is not general fairness: a permanently active first task
can still block later tasks in this explicitly FIFO service. -/
theorem stalled_head_blocks :
    nextTask [(0, reserve (initial 1 : Task Nat String)), (1, initial 2)] = some 0 := rfl

/-- Acknowledging before any receipt is ineffective. -/
theorem early_ack_is_refused :
    run (initial 2 : Task Nat String) [.acknowledge, .reserve, .acknowledge] =
      ⟨1, .active, false⟩ := rfl

/-- Zero budget is an inadmissible service configuration, not an uncertain effect. -/
theorem zero_budget_does_not_progress :
    charge (initial 0 : Task Nat String) .reserve = 0 ∧
      terminal (completedAttempt (initial 0 : Task Nat String) (.value 7)) = false := by decide

/-- An incorrect implementation that resets to its initial ledger after restart
can authorize arbitrarily many external attempts with a one-attempt budget. -/
def resetLoop : Nat → Task Nat String × Nat
  | 0 => (initial 1, 0)
  | n + 1 =>
      let previous := resetLoop n
      (initial 1, previous.2 + charge previous.1 .reserve)

theorem reset_loop_unbounded (n : Nat) : resetLoop n = (initial 1, n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [resetLoop, ih, charge, initial]

/-- Executed effects are external to the durable receipt ledger. -/
structure EffectWorld where
  effects : Nat
  ledger : Task Nat String
  deriving DecidableEq, Repr

def perform (world : EffectWorld) : EffectWorld :=
  match world.ledger.phase with
  | .active => { world with effects := world.effects + 1 }
  | _ => world

def crashed (world : EffectWorld) : EffectWorld :=
  { world with ledger := step world.ledger .restart }

def beforeEffect : EffectWorld := ⟨0, reserve (initial 2)⟩

/-- The same recovered ledger is compatible with zero or one committed effect. -/
theorem crash_window_indistinguishable :
    (crashed beforeEffect).ledger = (crashed (perform beforeEffect)).ledger ∧
      (crashed beforeEffect).effects ≠ (crashed (perform beforeEffect)).effects := by decide

/-- No function of this ledger alone can reconstruct whether the effect happened. -/
theorem ledger_cannot_decide_effect :
    ¬ ∃ readEffects : Task Nat String → Nat,
      readEffects (crashed beforeEffect).ledger = (crashed beforeEffect).effects ∧
      readEffects (crashed (perform beforeEffect)).ledger =
        (crashed (perform beforeEffect)).effects := by
  rintro ⟨readEffects, noEffect, didEffect⟩
  have same := crash_window_indistinguishable.1
  rw [← same] at didEffect
  have different := crash_window_indistinguishable.2
  exact different (noEffect.symm.trans didEffect)

/-- Blindly resetting and replaying a completed but unrecorded increment doubles it. -/
theorem blind_replay_duplicates_effect :
    (perform { crashed (perform beforeEffect) with ledger := reserve (initial 2) }).effects = 2 := rfl

/-- A receiver atomically commits the idempotency key together with the effect.
Splitting those two writes would reintroduce the same crash window. -/
structure IdempotentReceiver (Id : Type w) where
  committed : Finset Id
  effects : Nat
  deriving DecidableEq

def applyOnce [DecidableEq Id] (key : Id) (receiver : IdempotentReceiver Id) :
    IdempotentReceiver Id :=
  if key ∈ receiver.committed then receiver
  else ⟨insert key receiver.committed, receiver.effects + 1⟩

/-- Both the key set and the observable effect counter are invariant under replay. -/
theorem idempotent_effect_replay [DecidableEq Id] (key : Id)
    (receiver : IdempotentReceiver Id) :
    applyOnce key (applyOnce key receiver) = applyOnce key receiver := by
  by_cases found : key ∈ receiver.committed <;> simp [applyOnce, found]

/-- Distinct keys still carry distinct effects; the safe receiver is not a no-op. -/
theorem distinct_keys_two_effects :
    (applyOnce 2 (applyOnce 1 (⟨∅, 0⟩ : IdempotentReceiver Nat))).effects = 2 := by decide

end Mettapedia.Machines.ErrorBoundaryContracts.Supervision
