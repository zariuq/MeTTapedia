import SequentialTools

/-!
# Steering a running batch: run every call, or skip the unstarted tail

When a message arrives while a batch of tool calls runs, a dispatcher can
treat it in two ways.

* **All-call** (`SequentialTools.dispatch`, the current contract). The
  message never changes the batch. Every emitted call runs, and only the
  operator's stop latch prevents execution. The model sees the message at
  its next decision, after the whole batch.
* **Steer** (OpenClaw's default sequential `steer` mode). After each call
  returns, a waiting message ends the batch. The unstarted tail gets
  synthetic `skipped` receipts, and the model sees the message at once. A
  started call is never interrupted.

Here the arrival is part of the state: the environment sets `pending` inside
`execute`, so a message that arrives during a call is seen when that call
returns. The stop latch behaves identically in both dispatchers.

Results:
* Both keep every emitted call paired with exactly one receipt, in order
  (`steer_order`, `steer_receipt_count`; `SequentialTools.command_order`).
* With no message, steering is exactly all-call dispatch
  (`steer_without_message`). So a hybrid that steers only on an explicitly
  marked operator message keeps the all-call contract until such a message
  arrives (`hybrid_without_marked_message`).
* A skipped call has no effect. The final state is the state after running
  only the calls that ran (`skipped_never_ran`), so re-issuing a skipped call
  cannot double an effect. Steering adds no uncertain outcome
  (`steer_adds_no_uncertainty`), unlike an interrupt that kills a running
  call.
* On a three-call batch whose message arrives during the first call,
  all-call runs all three and the message waits behind two calls
  (`all_call_runs_all_three`). Steer runs one and skips two
  (`steer_runs_one_skips_two`).
* The trade-off cannot be escaped. When a message arrives before the last
  call, no receipt list is both complete (every call ran) and responsive
  (nothing after the arrival call ran) (`complete_and_responsive_conflict`).

Scope: one sequential batch. OpenClaw's parallel batches never skip and are
outside the model. So are the model's later re-planning, debounce and
queue modes.
-/

namespace PettaClaw.SteeringComparison

open PettaClaw.SequentialTools

/-- A steering receipt: the call ran, with the outcome all-call dispatch
records, or it was skipped unstarted to process an incoming message. -/
inductive Mark (Value : Type) where
  | ran (outcome : Outcome Value)
  | skipped
  deriving Repr, DecidableEq

/-- Sequential steer dispatch. The first call always runs, and steering is
checked after each call returns. -/
def steer {State Command Value : Type}
    (pending : State → Bool) (isStopped : State → Bool)
    (execute : State → Command → State × Outcome Value) :
    State → List Command → State × List (Command × Mark Value)
  | state, [] => (state, [])
  | state, command :: rest =>
    if isStopped state then
      let tail := steer pending isStopped execute state rest
      (tail.1, (command, Mark.ran Outcome.stopped) :: tail.2)
    else
      let step := execute state command
      if pending step.1 then
        (step.1, (command, Mark.ran step.2) :: rest.map (fun c => (c, Mark.skipped)))
      else
        let tail := steer pending isStopped execute step.1 rest
        (tail.1, (command, Mark.ran step.2) :: tail.2)

/-- Every emitted call keeps its position and gets exactly one receipt. -/
theorem steer_order {State Command Value : Type}
    (pending stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) :
    (steer pending stop execute state commands).2.map Prod.fst = commands := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    by_cases hs : stop state = true
    · simp [steer, hs, ih]
    · by_cases hp : pending (execute state command).1 = true
      · simp [steer, hs, hp, List.map_map, Function.comp_def]
      · simp [steer, hs, hp, ih]

theorem steer_receipt_count {State Command Value : Type}
    (pending stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) :
    (steer pending stop execute state commands).2.length = commands.length := by
  have h := congrArg List.length (steer_order pending stop execute state commands)
  simpa using h

/-- With no message, steering is exactly all-call dispatch. -/
theorem steer_without_message {State Command Value : Type}
    (pending stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (quiet : ∀ s, pending s = false) (state : State) (commands : List Command) :
    steer pending stop execute state commands =
      ((dispatch stop execute state commands).1,
       (dispatch stop execute state commands).2.map
         (fun r => (r.command, Mark.ran r.outcome))) := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    by_cases hs : stop state = true
    · simp [steer, dispatch, hs, ih]
    · simp [steer, dispatch, hs, quiet, ih]

/-- The hybrid steers only on an explicitly marked operator message. -/
def hybrid {State Command Value : Type}
    (markedSteer : State → Bool) (isStopped : State → Bool)
    (execute : State → Command → State × Outcome Value) :
    State → List Command → State × List (Command × Mark Value) :=
  steer markedSteer isStopped execute

theorem hybrid_without_marked_message {State Command Value : Type}
    (marked stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (none_marked : ∀ s, marked s = false) (state : State) (commands : List Command) :
    hybrid marked stop execute state commands =
      ((dispatch stop execute state commands).1,
       (dispatch stop execute state commands).2.map
         (fun r => (r.command, Mark.ran r.outcome))) :=
  steer_without_message marked stop execute none_marked state commands

/-- The calls that ran, in order. -/
def ranCommands {Command Value : Type} :
    List (Command × Mark Value) → List Command
  | [] => []
  | (command, Mark.ran _) :: rest => command :: ranCommands rest
  | (_, Mark.skipped) :: rest => ranCommands rest

theorem ranCommands_skipped {Command Value : Type} (rest : List Command) :
    ranCommands (rest.map (fun c => (c, (Mark.skipped : Mark Value)))) = [] := by
  induction rest with
  | nil => rfl
  | cons c rest ih => simpa [ranCommands] using ih

/-- A skipped call has no effect: steering ends in the state reached by
running only the calls that ran. -/
theorem skipped_never_ran {State Command Value : Type}
    (pending stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (state : State) (commands : List Command) :
    (steer pending stop execute state commands).1 =
      (dispatch stop execute state
        (ranCommands (steer pending stop execute state commands).2)).1 := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    by_cases hs : stop state = true
    · simp [steer, dispatch, ranCommands, hs, ih]
    · by_cases hp : pending (execute state command).1 = true
      · simp [steer, dispatch, ranCommands, hs, hp, ranCommands_skipped]
      · simp [steer, dispatch, ranCommands, hs, hp, ih]

/-- Steering adds no uncertain outcome: when no call returns `unknown` and
no stop is raised, no receipt says `unknown`. -/
theorem steer_adds_no_uncertainty {State Command Value : Type}
    (pending stop : State → Bool) (execute : State → Command → State × Outcome Value)
    (running : ∀ s, stop s = false)
    (certain : ∀ s c, (execute s c).2 ≠ Outcome.unknown)
    (state : State) (commands : List Command) :
    ∀ x ∈ (steer pending stop execute state commands).2,
      x.2 ≠ Mark.ran Outcome.unknown := by
  induction commands generalizing state with
  | nil => simp [steer]
  | cons command rest ih =>
    intro x hx
    by_cases hp : pending (execute state command).1 = true
    · simp [steer, running, hp] at hx
      rcases hx with hx | ⟨c, _, hx⟩
      · subst hx; simpa using certain state command
      · subst hx; simp
    · simp [steer, running, hp] at hx
      rcases hx with hx | hx
      · subst hx; simpa using certain state command
      · exact ih _ x hx

/-! ## A concrete batch

The state counts the calls run and records whether a message waits. Three
calls run; the message arrives during the first. -/

abbrev World := Nat × Bool

def run3 (s : World) (c : Nat) : World × Outcome Nat :=
  ((s.1 + 1, s.2 || c == 0), Outcome.returned c)

def never (_ : World) : Bool := false

/-- All-call dispatch runs all three calls; the message waits behind two. -/
theorem all_call_runs_all_three :
    dispatch never run3 (0, false) [0, 1, 2] =
      ((3, true), [⟨0, .returned 0⟩, ⟨1, .returned 1⟩, ⟨2, .returned 2⟩]) := by
  decide

/-- Steer runs the first call and skips the other two. -/
theorem steer_runs_one_skips_two :
    steer (fun s : World => s.2) never run3 (0, false) [0, 1, 2] =
      ((1, true), [(0, Mark.ran (.returned 0)), (1, Mark.skipped), (2, Mark.skipped)]) := by
  decide

/-- When a message arrives during call `i` of a batch of `n > i + 1`
calls, no receipt list is both complete (no call skipped) and responsive
(every call after `i` skipped). -/
theorem complete_and_responsive_conflict {Value : Type}
    (marks : List (Mark Value)) (i : Nat) (later : i + 1 < marks.length)
    (complete : ∀ m ∈ marks, m ≠ Mark.skipped)
    (responsive : ∀ j (h : j < marks.length), i < j → marks[j] = Mark.skipped) :
    False :=
  complete marks[i + 1] (List.getElem_mem later) (responsive (i + 1) later (Nat.lt_succ_self i))

#print axioms steer_order
#print axioms steer_receipt_count
#print axioms steer_without_message
#print axioms hybrid_without_marked_message
#print axioms skipped_never_ran
#print axioms steer_adds_no_uncertainty
#print axioms all_call_runs_all_three
#print axioms steer_runs_one_skips_two
#print axioms complete_and_responsive_conflict

end PettaClaw.SteeringComparison
