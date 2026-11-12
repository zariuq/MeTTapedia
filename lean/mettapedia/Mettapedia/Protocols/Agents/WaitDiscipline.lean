import Mathlib.Data.Finset.Basic

/-!
# Observation, readiness and explicit waiting

A supervisor's status observation is different from a new reason to deliberate.
This is a contract for an explicitly parked waiting episode, not a policy that
forbids an active agent from using its remaining budget for other work.

Completion evidence is keyed by both task and run. It remains available whether
it arrives before or after the decision to wait. A genuine input or deadline
also admits a wake. Observation events do not consume that evidence, grant a
budget, acknowledge input or start a replacement worker.

An observation here is genuinely read-only. A status command that also reaps a
dead worker or retries report delivery must expose those transitions as
`finished` or `input`, rather than hiding them inside `observe`. Ticket identity
is freshness data; this model does not turn a copied identifier into authority.

The clock is abstracted as a separate deadline event: erasing observations does
not erase elapsed time or a deadline discovered during an observation. Liveness
below is conditional on the supervisor executing `pump`; it does not assume
that a stopped process, failed mail delivery or unfair scheduler progresses.

The final countermodel describes continuation calls that spend one budget unit
per status-only turn. It exhibits the linear cost that an explicit wait avoids.
These are protocol-level results, not a refinement proof of the agent runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.WaitDiscipline

structure Ticket (Task Run : Type) where
  task : Task
  run : Run
  deriving DecidableEq

variable {Task Run : Type} [DecidableEq Task] [DecidableEq Run]

structure Gate (Task Run : Type) [DecidableEq Task] [DecidableEq Run] where
  completed : Finset (Ticket Task Run)
  waiting : Option (Ticket Task Run)
  inputPending : Bool
  deadlinePending : Bool
  parked : Bool
  admissions : Nat

def Gate.empty : Gate Task Run := ⟨∅, none, false, false, true, 0⟩

def ready (s : Gate Task Run) : Bool :=
  s.inputPending || s.deadlinePending ||
    s.waiting.any (fun t => decide (t ∈ s.completed))

def await (s : Gate Task Run) (t : Ticket Task Run) : Gate Task Run :=
  { s with waiting := some t, parked := true }

def complete (s : Gate Task Run) (t : Ticket Task Run) : Gate Task Run :=
  { s with completed := insert t s.completed }

def pump (s : Gate Task Run) : Gate Task Run :=
  if s.parked && ready s then
    { s with
      waiting := none
      inputPending := false
      deadlinePending := false
      parked := false
      admissions := s.admissions + 1 }
  else s

inductive Event (Task Run Observation : Type) where
  | observe (value : Observation)
  | waitFor (ticket : Ticket Task Run)
  | finished (ticket : Ticket Task Run)
  | input
  | deadline
  | pump

variable {Observation : Type}

def step (s : Gate Task Run) : Event Task Run Observation → Gate Task Run
  | .observe _ => s
  | .waitFor t => await s t
  | .finished t => complete s t
  | .input => { s with inputPending := true }
  | .deadline => { s with deadlinePending := true }
  | .pump => pump s

def run (s : Gate Task Run) (events : List (Event Task Run Observation)) : Gate Task Run :=
  events.foldl step s

def meaningful : Event Task Run Observation → Bool
  | .observe _ => false
  | _ => true

/-- Arbitrary status payloads can be omitted without changing the gate, pending
evidence or admission count. Real input, completion and deadline events remain. -/
theorem erase_observations (s : Gate Task Run) (events : List (Event Task Run Observation)) :
    run s (events.filter meaningful) = run s events := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases e <;>
      simp only [List.filter_cons, meaningful, Bool.false_eq_true,
        ite_false, ite_true, run, List.foldl_cons, step] <;> apply ih

theorem await_complete_commute (s : Gate Task Run) (t : Ticket Task Run) :
    await (complete s t) t = complete (await s t) t := by
  rfl

/-- Completion before registration is just as usable as completion afterwards. -/
theorem completion_wakes_in_either_order (s : Gate Task Run) (t : Ticket Task Run) :
    (pump (complete (await s t) t)).admissions = s.admissions + 1 ∧
    (pump (await (complete s t) t)).admissions = s.admissions + 1 := by
  simp [pump, ready, await, complete]

/-- A wake ends this waiting episode; repeatedly observing the same ready state
does not admit the episode a second time. A new wait is an explicit new action. -/
theorem pump_idempotent (s : Gate Task Run) : pump (pump s) = pump s := by
  unfold pump
  split <;> simp_all [ready]

theorem completion_replay_idempotent (s : Gate Task Run) (t : Ticket Task Run) :
    complete (complete s t) t = complete s t := by
  simp [complete]

/-- The completion set is retained when an input wakes a waiter. No status read
or wake acknowledges or deletes its durable completion evidence. -/
theorem pump_preserves_completion (s : Gate Task Run) :
    (pump s).completed = s.completed := by
  unfold pump
  split <;> rfl

theorem input_wakes (s : Gate Task Run) (t : Ticket Task Run) :
    (pump { await s t with inputPending := true }).admissions = s.admissions + 1 := by
  simp [pump, ready, await]

theorem deadline_wakes (s : Gate Task Run) (t : Ticket Task Run) :
    (pump { await s t with deadlinePending := true }).admissions = s.admissions + 1 := by
  simp [pump, ready, await]

/-- Another run's ending does not stand in for the run being awaited. -/
theorem stale_completion_does_not_wake (wanted other : Ticket Task Run)
    (different : wanted ≠ other) :
    (pump (complete (await Gate.empty wanted) other)).admissions = 0 := by
  simp [pump, ready, await, complete, Gate.empty, different]

/-- An unready waiter survives any number of observation/pump cycles. -/
theorem unready_observation_cycle (t : Ticket Task Run) (view : Observation) (n : Nat) :
    run (await Gate.empty t)
      (List.replicate n [Event.observe view, Event.pump]).flatten = await Gate.empty t := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    simpa [run, step, pump, ready, await, Gate.empty, List.replicate_succ,
      List.foldl_append] using ih

def pumpCount : List (Event Task Run Observation) → Nat
  | [] => 0
  | .pump :: es => 1 + pumpCount es
  | _ :: es => pumpCount es

lemma step_admissions_le (s : Gate Task Run) (e : Event Task Run Observation) :
    (step s e).admissions ≤ s.admissions + pumpCount [e] := by
  cases e <;> simp [step, await, complete, pumpCount, pump]
  split <;> simp_all

/-- Only explicit readiness pumps can admit cognition. Observation volume is
absent from the bound, even when completion/input/deadline events interleave. -/
theorem admissions_bound (s : Gate Task Run) (events : List (Event Task Run Observation)) :
    (run s events).admissions ≤ s.admissions + pumpCount events := by
  induction events generalizing s with
  | nil => simp [run, pumpCount]
  | cons e es ih =>
    calc
      (run s (e :: es)).admissions = (run (step s e) es).admissions := rfl
      _ ≤ (step s e).admissions + pumpCount es := ih (step s e)
      _ ≤ (s.admissions + pumpCount [e]) + pumpCount es :=
        Nat.add_le_add_right (step_admissions_le s e) _
      _ = s.admissions + pumpCount (e :: es) := by
        cases e <;> simp [pumpCount, Nat.add_assoc]

structure PollBudget where
  fuel : Nat
  calls : Nat
  deriving DecidableEq, Repr

/-- The old scheduling pattern: each continuation asks the model for another
status decision while fuel remains, even with no new external evidence. -/
def periodicPoll (s : PollBudget) : PollBudget :=
  if s.fuel = 0 then s else ⟨s.fuel - 1, s.calls + 1⟩

def pollRun : Nat → PollBudget → PollBudget
  | 0, s => s
  | n + 1, s => pollRun n (periodicPoll s)

theorem periodic_poll_spends_entire_budget (n calls : Nat) :
    pollRun n ⟨n, calls⟩ = ⟨0, calls + n⟩ := by
  induction n generalizing calls with
  | zero => simp [pollRun]
  | succ n ih =>
    simpa [pollRun, periodicPoll, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (calls + 1)

#print axioms erase_observations
#print axioms completion_wakes_in_either_order
#print axioms admissions_bound
#print axioms periodic_poll_spends_entire_budget

end Mettapedia.Protocols.Agents.WaitDiscipline
