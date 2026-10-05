import Mettapedia.GSLT.Distinction.BlockTransport
import Mettapedia.GSLT.Dynamics.OrderedDemand

/-!
# Productive blocks, exact residuals and relation-level transport

`BlockTransport` reads a target's primitive steps as administrative or
completing, but it does not observe administrative divergence or deadlock.
This module adds what finite fuel, suspension, cancellation and late fallback
need, for a deterministic machine whose transitions publish ordered events.

* **Machines and finite runs** (`Machine`, `Machine.run`).  A transition is
  administrative (silent), publishes events and continues, finishes with a
  verdict, fails with fault events, calls out with a saved continuation, or
  does not exist (a stuck state).  A finite run returns its published events
  and its outcome: finished, faulted, suspended (with the request and the saved
  continuation), stuck, or exhausted (with the exact residual state).  Its
  observation (`Machine.observe`) carries the explicit `OrderedDemand.Status`.
* **Exact residuals** (`Machine.run_add`, `Machine.established_and_pending`).
  Running longer is resuming the saved residual: the events already published
  stay, and the residual's own run supplies exactly the pending ones.  A
  fallback that resumes its residual never restarts; restarting re-delivers
  and re-commits (the controls).  Finite observations grow by prefixes, and a
  final status is never revised (`Machine.observe_prefix`).
* **Progress** (`Machine.Productive`, `Machine.Productive.settles`).  A rank
  that decreases on administrative steps bounds administrative work, and a
  machine without stuck states then reaches a visible transition within the
  rank.  Without such a premise nothing completes: a stuck state and a silent
  region never acquire a final status (`Machine.stuck_incomplete`,
  `Machine.silent_region_incomplete`), and a silent region admits no rank
  (`Machine.not_productive_of_silent_region`).
* **Accounts** (`Machine.spent`, `Machine.spent_add`, `Machine.spent_le`).
  Instruction and allocation accounts are separate price functions with an
  explicit pointwise bound between them; resumption adds accounts exactly.
* **Foreign callbacks** (`Callback`, `Machine.close`).  A call publishes its
  request event, the events of the callback's own execution (reentrant calls
  and effects included), and a visible reply event (return, fault or
  cancellation), then continues the saved owned continuation
  (`Machine.close_run_of_suspended`), and productivity survives closing
  (`Machine.Productive.closed`).  The theorems hold for callbacks of this
  shape, which report their events and reply once; they are not claimed for
  arbitrary callbacks.  Classifying a callback as external would erase its
  events from the blocks (a control).
* **Blocks** (`Machine.reading`, `Machine.block_run`).  The machine's own steps
  form a GSLT with a block reading; every block is realized by the run with
  its exact events, blocks are unique (`Machine.block_unique`), and
  productivity says that administrative work between them is bounded.
* **Compiled blocks** (`CompiledBlocks.prefix_settles`).  With bounded
  administrative work, `prefixReflection` makes every primitive protocol prefix
  of a compiled program a source run followed by a bounded administrative
  residual.
* **Relation-level transport** (`CostSimulation`,
  `CostSimulation.observe_prefix`).  A relation between the actual states of two
  machines, in which every source transition is matched by at most `cost`
  target transitions publishing the same events, carrying finishing, faults and
  suspensions with related saved continuations.  The relation need not be a
  function; a source run's observation is a prefix of the target's at `cost`
  times the fuel.  With a simulation in each direction, final observations
  coincide and a source that never completes has a target that never completes
  (`CostSimulation.final_eq`, `CostSimulation.never_completes`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation)

/-- One primitive transition of a deterministic machine. -/
inductive Transition (State Event Verdict Request : Type) where
  /-- Administrative work, silent to the observer. -/
  | silent (next : State)
  /-- Publish events in order and continue. -/
  | publish (events : List Event) (next : State)
  /-- Finish with a verdict. -/
  | finish (verdict : Verdict)
  /-- Fail, publishing the fault events. -/
  | fail (events : List Event)
  /-- Call out, saving the continuation that the reply resumes. -/
  | call (request : Request) (saved : State)

/-- Whether a transition is administrative. -/
def Transition.administrative {State Event Verdict Request : Type} :
    Transition State Event Verdict Request → Bool
  | .silent _ => true
  | _ => false

/-- A deterministic machine; a state without a transition is stuck. -/
structure Machine (State Event Verdict Request : Type) where
  step : State → Option (Transition State Event Verdict Request)

/-- The outcome of a finite run. -/
inductive Outcome (State Verdict Request : Type) where
  | finished (verdict : Verdict)
  | faulted
  | suspended (request : Request) (saved : State)
  | stuck (state : State)
  | exhausted (residual : State)

namespace Outcome

variable {State Verdict Request : Type}

/-- The observed status: stuck and exhausted runs are incomplete. -/
def status : Outcome State Verdict Request → Status Verdict
  | .finished verdict => .finished verdict
  | .faulted => .faulted
  | .suspended _ _ => .suspended
  | .stuck _ => .incomplete
  | .exhausted _ => .incomplete

end Outcome

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)

/-- A finite run: the events it published and its outcome. -/
def run : ℕ → State → List Event × Outcome State Verdict Request
  | 0, state => ([], .exhausted state)
  | fuel + 1, state =>
      match machine.step state with
      | none => ([], .stuck state)
      | some (.silent next) => run fuel next
      | some (.publish events next) =>
          (events ++ (run fuel next).1, (run fuel next).2)
      | some (.finish verdict) => ([], .finished verdict)
      | some (.fail events) => (events, .faulted)
      | some (.call request saved) => ([], .suspended request saved)

theorem run_succ_stuck {fuel : ℕ} {state : State} (stepped : machine.step state = none) :
    machine.run (fuel + 1) state = ([], .stuck state) := by
  simp only [run, stepped]

theorem run_succ_silent {fuel : ℕ} {state next : State}
    (stepped : machine.step state = some (.silent next)) :
    machine.run (fuel + 1) state = machine.run fuel next := by
  simp only [run, stepped]

theorem run_succ_publish {fuel : ℕ} {state next : State} {events : List Event}
    (stepped : machine.step state = some (.publish events next)) :
    machine.run (fuel + 1) state = (events ++ (machine.run fuel next).1, (machine.run fuel next).2) := by
  simp only [run, stepped]

theorem run_succ_finish {fuel : ℕ} {state : State} {verdict : Verdict}
    (stepped : machine.step state = some (.finish verdict)) :
    machine.run (fuel + 1) state = ([], .finished verdict) := by
  simp only [run, stepped]

theorem run_succ_fail {fuel : ℕ} {state : State} {events : List Event}
    (stepped : machine.step state = some (.fail events)) :
    machine.run (fuel + 1) state = (events, .faulted) := by
  simp only [run, stepped]

theorem run_succ_call {fuel : ℕ} {state saved : State} {request : Request}
    (stepped : machine.step state = some (.call request saved)) :
    machine.run (fuel + 1) state = ([], .suspended request saved) := by
  simp only [run, stepped]

/-- The observation of a finite run. -/
def observe (fuel : ℕ) (state : State) : Observation Event Verdict :=
  ⟨(machine.run fuel state).1, (machine.run fuel state).2.status⟩

/-- Continue a finite run from its exhausted residual; every other outcome
already ends the run. -/
def continueRun (second : ℕ) :
    List Event × Outcome State Verdict Request → List Event × Outcome State Verdict Request
  | (events, .exhausted residual) =>
      (events ++ (machine.run second residual).1, (machine.run second residual).2)
  | result => result

theorem continueRun_prepend (second : ℕ) (events : List Event)
    (result : List Event × Outcome State Verdict Request) :
    machine.continueRun second (events ++ result.1, result.2) =
      (events ++ (machine.continueRun second result).1, (machine.continueRun second result).2) := by
  rcases result with ⟨published, outcome⟩
  cases outcome <;> simp [continueRun, List.append_assoc]

/-- **Exact residuals: running longer is resuming the saved residual.** -/
theorem run_add (first second : ℕ) (state : State) :
    machine.run (first + second) state = machine.continueRun second (machine.run first state) := by
  induction first generalizing state with
  | zero => simp [run, continueRun]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases found : machine.step state with
      | none => simp [run, found, continueRun]
      | some transition =>
          cases transition with
          | silent next => simp only [run, found, ih next]
          | publish events next =>
              simp only [run, found, ih next]
              exact (machine.continueRun_prepend second events (machine.run first next)).symm
          | finish verdict => simp [run, found, continueRun]
          | fail events => simp [run, found, continueRun]
          | call request saved => simp [run, found, continueRun]

/-- **A finite prefix keeps its established events, and its residual keeps
exactly the pending ones.** -/
theorem established_and_pending (first second : ℕ) (state residual : State)
    (events : List Event) (paused : machine.run first state = (events, .exhausted residual)) :
    machine.run (first + second) state =
      (events ++ (machine.run second residual).1, (machine.run second residual).2) := by
  rw [run_add, paused]
  rfl

/-- A run that did not exhaust its fuel is not changed by more fuel. -/
theorem run_stable (first second : ℕ) (state : State)
    (ended : ∀ residual, (machine.run first state).2 ≠ .exhausted residual) :
    machine.run (first + second) state = machine.run first state := by
  rw [run_add]
  rcases outcome : machine.run first state with ⟨events, result⟩
  rw [outcome] at ended
  cases result with
  | exhausted residual => exact absurd rfl (ended residual)
  | _ => rfl

/-- **Finite observations grow by prefixes; a final status is never revised.** -/
theorem observe_prefix (first second : ℕ) (state : State) :
    (machine.observe first state).Prefix (machine.observe (first + second) state) := by
  simp only [observe, run_add]
  rcases machine.run first state with ⟨events, result⟩
  cases result with
  | exhausted residual =>
      exact ⟨List.prefix_append _ _, fun final => final.elim⟩
  | _ => exact Observation.Prefix.refl _

theorem observe_prefix_of_le {first second : ℕ} (le : first ≤ second) (state : State) :
    (machine.observe first state).Prefix (machine.observe second state) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  exact machine.observe_prefix first extra state

/-! ## Progress -/

/-- **A productive machine**: administrative work is bounded by a rank that
every administrative step decreases, and no state is stuck. -/
structure Productive where
  rank : State → ℕ
  silent_decreases : ∀ {state next : State}, machine.step state = some (.silent next) →
    rank next < rank state
  moves : ∀ state, machine.step state ≠ none

/-- **Administrative work ends within the rank** at a visible transition. -/
theorem Productive.settles {machine : Machine State Event Verdict Request}
    (productive : machine.Productive) (state : State) :
    ∃ k ≤ productive.rank state, ∃ settled transition,
      machine.run k state = ([], .exhausted settled) ∧ machine.step settled = some transition ∧
        transition.administrative = false := by
  induction h : productive.rank state using Nat.strong_induction_on generalizing state with
  | _ n ih =>
      cases found : machine.step state with
      | none => exact absurd found (productive.moves state)
      | some transition =>
          cases administrative : transition.administrative with
          | false => exact ⟨0, Nat.zero_le _, state, transition, rfl, found, administrative⟩
          | true =>
              cases transition with
              | silent next =>
                  have smaller := productive.silent_decreases found
                  obtain ⟨k, bound, settled, final, ran, stepped, visible⟩ :=
                    ih (productive.rank next) (h ▸ smaller) next rfl
                  refine ⟨k + 1, by omega, settled, final, ?_, stepped, visible⟩
                  simp only [run, found, ran]
              | _ => simp [Transition.administrative] at administrative

/-- **A stuck state never acquires completion.** -/
theorem stuck_incomplete (state : State) (stuck : machine.step state = none) (fuel : ℕ) :
    machine.observe fuel state = ⟨[], .incomplete⟩ := by
  cases fuel <;> simp [observe, run, stuck, Outcome.status]

/-- **A silent region never acquires completion**: states that only step
silently to states of the region publish nothing and stay incomplete. -/
theorem silent_region_incomplete (region : State → Prop)
    (closed : ∀ state, region state → ∃ next, machine.step state = some (.silent next) ∧ region next)
    (fuel : ℕ) (state : State) (inside : region state) :
    machine.observe fuel state = ⟨[], .incomplete⟩ := by
  induction fuel generalizing state with
  | zero => simp [observe, run, Outcome.status]
  | succ fuel ih =>
      obtain ⟨next, stepped, nextInside⟩ := closed state inside
      have later := ih next nextInside
      simp only [observe] at later ⊢
      simpa only [run, stepped] using later

/-- A silent region admits no rank: such a machine is not productive. -/
theorem not_productive_of_silent_region (region : State → Prop)
    (closed : ∀ state, region state → ∃ next, machine.step state = some (.silent next) ∧ region next)
    (state : State) (inside : region state) : IsEmpty machine.Productive := by
  refine ⟨fun productive => ?_⟩
  have descent : ∀ n, ∀ state, productive.rank state = n → ¬ region state := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro state ranked inRegion
        obtain ⟨next, stepped, nextInside⟩ := closed state inRegion
        exact ih _ (ranked ▸ productive.silent_decreases stepped) next rfl nextInside
  exact descent _ state rfl inside

/-! ## Accounts -/

/-- The account of a finite run under a price for each transition taken. -/
def spent (price : State → ℕ) : ℕ → State → ℕ
  | 0, _ => 0
  | fuel + 1, state =>
      match machine.step state with
      | none => 0
      | some (.silent next) => price state + spent price fuel next
      | some (.publish _ next) => price state + spent price fuel next
      | some _ => price state

/-- The account still to be charged from a finite run's outcome. -/
def spentAfter (price : State → ℕ) (second : ℕ) : Outcome State Verdict Request → ℕ
  | .exhausted residual => machine.spent price second residual
  | _ => 0

/-- **Resumption adds accounts exactly.** -/
theorem spent_add (price : State → ℕ) (first second : ℕ) (state : State) :
    machine.spent price (first + second) state =
      machine.spent price first state + machine.spentAfter price second (machine.run first state).2 := by
  induction first generalizing state with
  | zero => simp [spent, run, spentAfter]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      cases found : machine.step state with
      | none => simp [spent, run, found, spentAfter]
      | some transition =>
          cases transition with
          | silent next => simp only [spent, run, found, ih next, Nat.add_assoc]
          | publish events next => simp only [spent, run, found, ih next, Nat.add_assoc]
          | finish verdict => simp [spent, run, found, spentAfter]
          | fail events => simp [spent, run, found, spentAfter]
          | call request saved => simp [spent, run, found, spentAfter]

/-- **An explicit pointwise bound between two accounts bounds their totals.** -/
theorem spent_le (instructions allocations : State → ℕ) (factor : ℕ)
    (bound : ∀ state, allocations state ≤ factor * instructions state) (fuel : ℕ) (state : State) :
    machine.spent allocations fuel state ≤ factor * machine.spent instructions fuel state := by
  induction fuel generalizing state with
  | zero => simp [spent]
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp [spent, found]
      | some transition =>
          cases transition with
          | silent next =>
              simp only [spent, found, Nat.mul_add]
              exact Nat.add_le_add (bound state) (ih next)
          | publish events next =>
              simp only [spent, found, Nat.mul_add]
              exact Nat.add_le_add (bound state) (ih next)
          | finish verdict => simpa [spent, found] using bound state
          | fail events => simpa [spent, found] using bound state
          | call request saved => simpa [spent, found] using bound state

/-! ## Foreign callbacks -/

end Machine

/-- A callback's visible reply. -/
inductive Reply (Value Failure : Type) where
  | returned (value : Value)
  | faulted (failure : Failure)
  | cancelled

/-- **The callback protocol**: a visible call event, a visible reply event, and
the resumption of the saved owned continuation by the reply. -/
structure Callback (State Event Request Value Failure : Type) where
  callEvent : Request → Event
  replyEvent : Reply Value Failure → Event
  resume : State → Reply Value Failure → State

/-- An environment answers a call with the events of its own execution,
reentrant calls and effects included, and one reply. -/
abbrev Environment (Request Event Value Failure : Type) :=
  Request → List Event × Reply Value Failure

namespace Machine

variable {State Event Verdict Request : Type} (machine : Machine State Event Verdict Request)
variable {Value Failure : Type}

/-- The events a call publishes under the protocol. -/
def callEvents (callback : Callback State Event Request Value Failure)
    (environment : Environment Request Event Value Failure) (request : Request) : List Event :=
  callback.callEvent request :: (environment request).1 ++ [callback.replyEvent (environment request).2]

/-- **Close a machine under a callback protocol and an environment**: every
call publishes its call, callback and reply events and resumes the saved
continuation. -/
def close (callback : Callback State Event Request Value Failure)
    (environment : Environment Request Event Value Failure) : Machine State Event Verdict Empty where
  step state := (machine.step state).map fun
    | .silent next => .silent next
    | .publish events next => .publish events next
    | .finish verdict => .finish verdict
    | .fail events => .fail events
    | .call request saved =>
        .publish (callEvents callback environment request)
          (callback.resume saved (environment request).2)

variable (callback : Callback State Event Request Value Failure)
  (environment : Environment Request Event Value Failure)

/-- **A suspended run, closed under the protocol, publishes the call, the
callback's own events and the reply, then continues from the resumed saved
continuation.** -/
theorem close_run_of_suspended (fuel : ℕ) (state : State) (events : List Event)
    (request : Request) (saved : State)
    (suspended : machine.run fuel state = (events, .suspended request saved)) :
    ∃ k ≤ fuel, (machine.close callback environment).run k state =
      (events ++ callEvents callback environment request,
        .exhausted (callback.resume saved (environment request).2)) := by
  induction fuel generalizing state events with
  | zero => simp [run] at suspended
  | succ fuel ih =>
      cases found : machine.step state with
      | none => simp [run, found] at suspended
      | some transition =>
          cases transition with
          | silent next =>
              simp only [run, found] at suspended
              obtain ⟨k, bound, ran⟩ := ih next events suspended
              refine ⟨k + 1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state = some (.silent next) := by
                simp [Machine.close, found]
              simp only [run, closed, ran]
          | publish published next =>
              simp only [run, found, Prod.mk.injEq] at suspended
              obtain ⟨eventsEq, outcomeEq⟩ := suspended
              obtain ⟨k, bound, ran⟩ := ih next (machine.run fuel next).1
                (Prod.ext rfl outcomeEq)
              refine ⟨k + 1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state =
                  some (.publish published next) := by
                simp [Machine.close, found]
              simp only [run, closed, ran, ← eventsEq, List.append_assoc]
          | finish verdict => simp [run, found] at suspended
          | fail failed => simp [run, found] at suspended
          | call called savedHere =>
              simp only [run, found, Prod.mk.injEq, Outcome.suspended.injEq] at suspended
              obtain ⟨rfl, rfl, rfl⟩ := suspended
              refine ⟨1, by omega, ?_⟩
              have closed : (machine.close callback environment).step state =
                  some (.publish (callEvents callback environment called)
                    (callback.resume savedHere (environment called).2)) := by
                simp [Machine.close, found]
              simp [run, closed]

/-- A productive machine stays productive when closed under any callback of the
protocol: a call becomes a visible transition. -/
def Productive.closed {machine : Machine State Event Verdict Request}
    (productive : machine.Productive) : (machine.close callback environment).Productive where
  rank := productive.rank
  silent_decreases := by
    intro state next stepped
    cases found : machine.step state with
    | none => simp [Machine.close, found] at stepped
    | some transition =>
        cases transition <;> simp [Machine.close, found] at stepped
        subst stepped
        exact productive.silent_decreases found
  moves state := by
    have moving := productive.moves state
    simpa [Machine.close] using moving

/-! ## The block reading of a machine -/

/-- The machine's own steps, read as a GSLT with equality as its equations. -/
abbrev gslt : GSLT.{0} where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites state next := machine.step state = some (.silent next) ∨
    ∃ events, machine.step state = some (.publish events next)
  rewrites_resp_left := by
    intro _ _ target equal stepped
    exact ⟨target, equal ▸ stepped, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ stepped equal
    exact equal ▸ stepped

/-- **The block reading**: administrative steps are silent, and a publishing
step completes a block labelled by its events. -/
def reading : BlockReading machine.gslt (List Event) where
  silent state next := machine.step state = some (.silent next)
  complete events state next := machine.step state = some (.publish events next)
  external _ _ := False
  silent_step := Or.inl
  complete_step := fun completes => Or.inr ⟨_, completes⟩
  external_step := fun never => never.elim
  classify := by
    rintro _ _ (silences | ⟨events, completes⟩)
    · exact Or.inl silences
    · exact Or.inr (Or.inl ⟨events, completes⟩)
  silent_resp_left := by
    intro _ _ next equal silences
    exact ⟨next, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ next equal completes
    exact ⟨next, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- Administrative steps are realized by the run without output. -/
theorem silent_run {state middle : State}
    (administrative : Relation.ReflTransGen machine.reading.silent state middle) :
    ∃ k, ∀ fuel, machine.run (k + fuel) state = machine.run fuel middle := by
  induction administrative using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun fuel => by simp⟩
  | head silences _ ih =>
      obtain ⟨k, ran⟩ := ih
      refine ⟨k + 1, fun fuel => ?_⟩
      rw [show k + 1 + fuel = (k + fuel) + 1 by omega]
      simp only [run]
      rw [show machine.step _ = _ from silences]
      exact ran fuel

/-- **Every block is realized by the run**, with its exact events. -/
theorem block_run {events : List Event} {state next : State}
    (block : machine.reading.Block events state next) :
    ∃ k, ∀ fuel, machine.run (k + 1 + fuel) state =
      (events ++ (machine.run fuel next).1, (machine.run fuel next).2) := by
  obtain ⟨middle, administrative, completes⟩ := block
  obtain ⟨k, ran⟩ := machine.silent_run administrative
  refine ⟨k, fun fuel => ?_⟩
  rw [show k + 1 + fuel = k + (fuel + 1) by omega, ran]
  simp only [run]
  rw [show machine.step middle = _ from completes]

/-- A block reading that classifies the publishing steps of the states in
`outside` as external interactions.  Their events then belong to no block:
the classification limits a theorem's scope, and the controls show that it
erases a callback's events from the block observations. -/
def readingOutside (outside : State → Prop) : BlockReading machine.gslt (List Event) where
  silent state next := machine.step state = some (.silent next)
  complete events state next := machine.step state = some (.publish events next) ∧ ¬ outside state
  external state next := (∃ events, machine.step state = some (.publish events next)) ∧ outside state
  silent_step := Or.inl
  complete_step := fun completes => Or.inr ⟨_, completes.1⟩
  external_step := fun interaction => Or.inr interaction.1
  classify := by
    rintro state _ (silences | ⟨events, completes⟩)
    · exact Or.inl silences
    · by_cases out : outside state
      · exact Or.inr (Or.inr ⟨⟨events, completes⟩, out⟩)
      · exact Or.inr (Or.inl ⟨events, completes, out⟩)
  silent_resp_left := by
    intro _ _ next equal silences
    exact ⟨next, equal ▸ silences, rfl⟩
  complete_resp_left := by
    intro _ _ _ next equal completes
    exact ⟨next, equal ▸ completes, rfl⟩
  complete_resp_right := by
    intro _ _ _ _ completes equal
    exact equal ▸ completes

/-- **Blocks with the status as crisp atoms**: the labelled system of blocks,
observing at each state the status after one transition.  Under finite
branching and a positive discount its graded zero kernel is crisp
bisimilarity (`GradedSystem.logicalDistance_ofSystem_eq_zero_iff`). -/
def statusSystem : HennessyMilner.System machine.gslt where
  Atom := Status Verdict
  observes atom state := (machine.observe 1 state).status = atom
  observes_resp atom := by
    intro _ _ equal
    change _ = _ at equal
    rw [equal]
  Label := List Event
  act := machine.reading.Block
  act_resp_left := by
    intro _ _ _ target equal block
    change _ = _ at equal
    exact ⟨target, equal ▸ block, rfl⟩
  act_resp_right := by
    intro _ _ _ _ block equal
    change _ = _ at equal
    exact equal ▸ block

/-- Administrative runs of a deterministic machine that stop at states without
an administrative step stop at the same state. -/
theorem settled_unique {start first second : State}
    (left : Relation.ReflTransGen machine.reading.silent start first)
    (right : Relation.ReflTransGen machine.reading.silent start second)
    (stopFirst : ∀ next, ¬ machine.reading.silent first next)
    (stopSecond : ∀ next, ¬ machine.reading.silent second next) : first = second := by
  induction left using Relation.ReflTransGen.head_induction_on generalizing second with
  | refl =>
      cases right using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head silences _ => exact absurd silences (stopFirst _)
  | head silences rest ih =>
      cases right using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd silences (stopSecond _)
      | head silences' rest' =>
          change machine.step _ = _ at silences silences'
          rw [silences] at silences'
          cases silences'
          exact ih rest' stopSecond

/-- **Blocks of a deterministic machine are unique.** -/
theorem block_unique {first second : List Event} {state next next' : State}
    (one : machine.reading.Block first state next) (two : machine.reading.Block second state next') :
    first = second ∧ next = next' := by
  obtain ⟨middle, administrative, completes⟩ := one
  obtain ⟨middle', administrative', completes'⟩ := two
  have stops : ∀ {middle : State} {events : List Event} {after : State},
      machine.step middle = some (.publish events after) →
        ∀ next, ¬ machine.reading.silent middle next := by
    intro middle events after visible next silences
    change machine.step _ = _ at silences
    rw [visible] at silences
    cases silences
  have same := machine.settled_unique administrative administrative' (stops completes)
    (stops completes')
  subst same
  change machine.step _ = _ at completes completes'
  rw [completes] at completes'
  cases completes'
  exact ⟨rfl, rfl⟩

end Machine

/-! ## Productive compiled blocks -/

/-- **Bounded administrative work** on a block reading: a rank that every
administrative step decreases. -/
structure AdministrativeRank {T : GSLT.{0}} {Label : Type} (B : BlockReading T Label) where
  rank : T.Term → ℕ
  decreases : ∀ {term term' : T.Term}, B.silent term term' → rank term' < rank term

theorem AdministrativeRank.rank_le {T : GSLT.{0}} {Label : Type} {B : BlockReading T Label}
    (ranked : AdministrativeRank B) {term term' : T.Term}
    (administrative : Relation.ReflTransGen B.silent term term') : ranked.rank term' ≤ ranked.rank term := by
  induction administrative with
  | refl => exact le_rfl
  | tail _ last ih => exact (ranked.decreases last).le.trans ih

/-- **Every primitive protocol prefix of a compiled program is a source run
followed by a bounded administrative residual**: `prefixReflection` supplies
the source run, and the rank bounds the administrative work since its compiled
endpoint. -/
theorem _root_.Mettapedia.GSLT.Distinction.CompiledBlocks.prefix_settles {S T : GSLT.{0}}
    {B : BlockReading T Unit}
    (compiled : CompiledBlocks S T B) (ranked : AdministrativeRank B) {term : S.Term}
    {target' : T.Term}
    (protocol : Relation.ReflTransGen B.ProtocolStep (compiled.realization.mapTerm term) target') :
    ∃ target, Relation.ReflTransGen S.Step term target ∧
      ∃ settled, T.Equiv (compiled.realization.mapTerm target) settled ∧
        Relation.ReflTransGen B.silent settled target' ∧ ranked.rank target' ≤ ranked.rank settled := by
  obtain ⟨target, run, settled, equivalent, administrative⟩ := compiled.prefixReflection protocol
  exact ⟨target, run, settled, equivalent, administrative, ranked.rank_le administrative⟩

/-! ## Relation-level transport with a cost bound -/

/-- **A cost-bounded simulation between the actual states of two machines.**
Every source transition from related states is matched by at most `cost`
target transitions that publish the same events and end in related states, or
reach the same verdict, the same faults, or the same request with related
saved continuations.  The relation need not be a function. -/
structure CostSimulation {Source Target Event Verdict Request : Type}
    (source : Machine Source Event Verdict Request) (target : Machine Target Event Verdict Request)
    (related : Source → Target → Prop) (cost : ℕ) : Prop where
  silent : ∀ {state state' next}, related state state' → source.step state = some (.silent next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = ([], .exhausted next') ∧ related next next'
  publish : ∀ {state state' events next}, related state state' →
    source.step state = some (.publish events next) →
    ∃ k ≤ cost, ∃ next', target.run k state' = (events, .exhausted next') ∧ related next next'
  finish : ∀ {state state' verdict}, related state state' →
    source.step state = some (.finish verdict) →
    ∃ k ≤ cost, target.run k state' = ([], .finished verdict)
  fail : ∀ {state state' events}, related state state' → source.step state = some (.fail events) →
    ∃ k ≤ cost, target.run k state' = (events, .faulted)
  call : ∀ {state state' request saved}, related state state' →
    source.step state = some (.call request saved) →
    ∃ k ≤ cost, ∃ saved', target.run k state' = ([], .suspended request saved') ∧ related saved saved'

namespace CostSimulation

variable {Source Target Event Verdict Request : Type}
  {source : Machine Source Event Verdict Request} {target : Machine Target Event Verdict Request}
  {related : Source → Target → Prop} {cost : ℕ}

private theorem prefix_prepend {events : List Event} {first second : Observation Event Verdict}
    (prefixed : first.Prefix second) :
    (⟨events ++ first.events, first.status⟩ : Observation Event Verdict).Prefix
      ⟨events ++ second.events, second.status⟩ := by
  refine ⟨List.prefix_append_right_inj events |>.mpr prefixed.1, fun final => ?_⟩
  have same := prefixed.2 final
  rw [same]

/-- **Relation-level transport**: a source run's observation is a prefix of the
related target run's observation at `cost` times the fuel; when the source run
is final, the target run is the same final observation. -/
theorem observe_prefix (simulation : CostSimulation source target related cost) (fuel : ℕ)
    {state : Source} {state' : Target} (relatedStates : related state state') :
    (source.observe fuel state).Prefix (target.observe (cost * fuel) state') := by
  induction fuel generalizing state state' with
  | zero => exact ⟨List.nil_prefix, fun final => final.elim⟩
  | succ fuel ih =>
      have budget : ∀ k ≤ cost, ∃ rest, cost * (fuel + 1) = k + rest ∧ cost * fuel ≤ rest := by
        intro k bound
        exact ⟨cost * (fuel + 1) - k, by rw [Nat.mul_succ]; omega, by rw [Nat.mul_succ]; omega⟩
      cases found : source.step state with
      | none =>
          rw [source.stuck_incomplete state found]
          exact ⟨List.nil_prefix, fun final => final.elim⟩
      | some transition =>
          cases transition with
          | silent next =>
              obtain ⟨k, bound, next', ran, relatedNext⟩ := simulation.silent relatedStates found
              obtain ⟨rest, split, enough⟩ := budget k bound
              have later := (ih relatedNext).trans (target.observe_prefix_of_le enough next')
              have targetRun : target.observe (cost * (fuel + 1)) state' = target.observe rest next' := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  List.nil_append]
              rw [targetRun]
              simpa only [Machine.observe, Machine.run, found] using later
          | publish events next =>
              obtain ⟨k, bound, next', ran, relatedNext⟩ := simulation.publish relatedStates found
              obtain ⟨rest, split, enough⟩ := budget k bound
              have later := (ih relatedNext).trans (target.observe_prefix_of_le enough next')
              have targetRun : target.observe (cost * (fuel + 1)) state' =
                  ⟨events ++ (target.observe rest next').events, (target.observe rest next').status⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun]
              rw [targetRun]
              have sourceRun : source.observe (fuel + 1) state =
                  ⟨events ++ (source.observe fuel next).events, (source.observe fuel next).status⟩ := by
                simp only [Machine.observe, Machine.run, found]
              rw [sourceRun]
              exact prefix_prepend later
          | finish verdict =>
              obtain ⟨k, bound, ran⟩ := simulation.finish relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨[], .finished verdict⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _
          | fail events =>
              obtain ⟨k, bound, ran⟩ := simulation.fail relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨events, .faulted⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _
          | call request saved =>
              obtain ⟨k, bound, saved', ran, _⟩ := simulation.call relatedStates found
              obtain ⟨rest, split, _⟩ := budget k bound
              have targetRun : target.observe (cost * (fuel + 1)) state' = ⟨[], .suspended⟩ := by
                simp only [Machine.observe, split, target.run_add, ran, Machine.continueRun,
                  Outcome.status]
              rw [targetRun]
              simp only [Machine.observe, Machine.run, found, Outcome.status]
              exact Observation.Prefix.refl _

/-- **With a simulation each way, final observations coincide.** -/
theorem final_eq (forward : CostSimulation source target related cost)
    {cost' : ℕ} (backward : CostSimulation target source (fun state' state => related state state') cost')
    {state : Source} {state' : Target} (relatedStates : related state state')
    {fuel fuel' : ℕ} (final : (source.observe fuel state).status.Final)
    (final' : (target.observe fuel' state').status.Final) :
    source.observe fuel state = target.observe fuel' state' := by
  have there := forward.observe_prefix fuel relatedStates
  have back := backward.observe_prefix fuel' relatedStates
  have one := there.2 final
  have two := back.2 final'
  have sameAtTarget : target.observe (cost * fuel) state' = target.observe fuel' state' := by
    rcases le_total (cost * fuel) fuel' with le | le
    · have grown := (target.observe_prefix_of_le le state').2 (one ▸ final)
      exact grown
    · exact ((target.observe_prefix_of_le le state').2 final').symm
  exact one.trans sameAtTarget

/-- **A source state that never completes has related target states that never
complete**, given the backward simulation. -/
theorem never_completes {cost' : ℕ}
    (backward : CostSimulation target source (fun state' state => related state state') cost')
    {state : Source} {state' : Target} (relatedStates : related state state')
    (never : ∀ fuel, ¬ (source.observe fuel state).status.Final) (fuel : ℕ) :
    ¬ (target.observe fuel state').status.Final := by
  intro final
  have back := backward.observe_prefix fuel relatedStates
  have same := back.2 final
  apply never (cost' * fuel)
  rw [← same]
  exact final

end CostSimulation

end Mettapedia.GSLT.Distinction.ProductiveBlocks
