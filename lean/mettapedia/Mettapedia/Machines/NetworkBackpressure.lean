import Mathlib.Tactic
import Mettapedia.Machines.ScheduledRun.Core

/-!
# Durability eligibility and receive-window progress

A byte-stream receiver shares a scheduler with journal producers and a journal
drainer. At the batch threshold only journal actors are eligible. Preparation
of a read, window credit or timer turn is distinct from scheduler permission.

The counterexample completes arbitrarily many journal entries while an equally
fast producer keeps the gate closed. It is weakly fair even for individual
admitted actions, yet never consumes queued bytes or services network timers.
It works with arbitrary receive capacity and a nonzero advertised window.

The positive results require work justice, not merely rotation among actors.
An eventually quiet journal drains under that justice; a continuously open
gate then permits pending reads, returned window credit and timer turns.

Arrival suppression excludes the sustained-arrival witness. A second witness
obeys suppression and reopens the gate repeatedly, but weak justice still
permits starvation between openings. Strong action justice excludes that
second witness. These are sufficient abstract justice predicates, not proofs
that a particular scheduler supplies them.

This is an abstract service model, not a model of all TCP states, TLS records,
NIC custody, or the SexOS implementation. Its window is receiver credit;
packet loss and delayed window advertisements are outside this abstraction.
In particular it assumes no indivisible TLS record or minimum TCP segment.
The three-part buffer account follows RFC 9293 section 3.8.6.2.2; it does not
implement that section's window-update thresholds or the sender's SWS policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NetworkBackpressure

inductive Actor | files | drive | network | browser
  deriving DecidableEq, Repr

structure State where
  backlog : Nat
  queued : Nat
  uncredited : Nat
  window : Nat
  delivered : Nat
  committed : Nat
  timers : Nat
  deriving DecidableEq, Repr

inductive Action
  | append
  | commit
  | receive (bytes : Nat)
  | read (bytes : Nat)
  | credit
  | timer
  deriving DecidableEq, Repr

def Action.actor : Action → Actor
  | .append => .files
  | .commit => .drive
  | .receive _ | .credit | .timer => .network
  | .read _ => .browser

def Eligible (batch : Nat) (s : State) : Actor → Prop
  | .files | .drive => True
  | .network | .browser => s.backlog < batch

instance (batch : Nat) (s : State) (actor : Actor) :
    Decidable (Eligible batch s actor) := by
  cases actor <;> unfold Eligible <;> infer_instance

def Prepared (s : State) : Action → Prop
  | .append | .timer => True
  | .commit => 0 < s.backlog
  | .receive n => 0 < n ∧ n ≤ s.window
  | .read n => 0 < n ∧ n ≤ s.queued
  | .credit => 0 < s.uncredited

instance (s : State) (a : Action) : Decidable (Prepared s a) := by
  cases a <;> unfold Prepared <;> infer_instance

def Permitted (batch : Nat) (s : State) (a : Action) : Prop :=
  Eligible batch s a.actor

instance (batch : Nat) (s : State) (a : Action) : Decidable (Permitted batch s a) :=
  inferInstanceAs (Decidable (Eligible batch s a.actor))

def Admitted (batch : Nat) (s : State) (a : Action) : Prop :=
  Prepared s a ∧ Permitted batch s a

instance (batch : Nat) (s : State) (a : Action) : Decidable (Admitted batch s a) :=
  inferInstanceAs (Decidable (Prepared s a ∧ Eligible batch s a.actor))

/-- Effects apply only with preparation; saturating subtraction is never
used to authorize a read, receive or commit. -/
def apply (a : Action) (s : State) : State :=
  match a with
  | .append => { s with backlog := s.backlog + 1 }
  | .commit => { s with backlog := s.backlog - 1, committed := s.committed + 1 }
  | .receive n => { s with queued := s.queued + n, window := s.window - n }
  | .read n => { s with
      queued := s.queued - n
      uncredited := s.uncredited + n
      delivered := s.delivered + n }
  | .credit => { s with window := s.window + s.uncredited, uncredited := 0 }
  | .timer => { s with timers := s.timers + 1 }

def Valid (capacity : Nat) (s : State) : Prop :=
  s.queued + s.uncredited + s.window = capacity

theorem apply_valid {capacity : Nat} {s : State} {a : Action}
    (valid : Valid capacity s) (ready : Prepared s a) :
    Valid capacity (apply a s) := by
  cases a <;> simp_all [Valid, Prepared, apply] <;> omega

theorem delivered_mono (a : Action) (s : State) :
    s.delivered ≤ (apply a s).delivered := by
  cases a <;> simp [apply]

theorem queued_delivered_mono {s : State} {a : Action} (ready : Prepared s a) :
    s.queued + s.delivered ≤ (apply a s).queued + (apply a s).delivered := by
  cases a
  all_goals simp_all [Prepared, apply]
  all_goals omega

theorem backlog_le_without_append {s : State} {a : Action} (quiet : a ≠ .append) :
    (apply a s).backlog ≤ s.backlog := by
  cases a <;> simp_all [apply]

/-- A positive offered byte count can always be split to fit positive receiver
credit. No claim about the peer's eventual choice or packet delivery follows. -/
theorem positive_window_admits_prefix (s : State) (offered : Nat)
    (space : 0 < s.window) (data : 0 < offered) :
    Prepared s (.receive (min offered s.window)) ∧
      min offered s.window + (offered - min offered s.window) = offered := by
  simp only [Prepared]
  omega

structure Run (batch : Nat) where
  state : Nat → State
  action : Nat → Action
  admitted : ∀ t, Admitted batch (state t) (action t)
  next : ∀ t, state (t + 1) = apply (action t) (state t)

namespace Run

variable {batch : Nat} (r : Run batch)

/-- Weak fairness of eligible actors says nothing about an actor permanently
excluded by the gate. It also does not choose work within an actor. -/
def ActorFair : Prop :=
  ∀ actor start, (∀ t, start ≤ t → Eligible batch (r.state t) actor) →
    ∃ t, start ≤ t ∧ (r.action t).actor = actor

/-- Weak action justice: each continuously admitted fixed action eventually
fires. Reads of one byte suffice for the progress theorem; no atomic record
size or minimum peer segment is stipulated. -/
def Fair : Prop :=
  ∀ a start, (∀ t, start ≤ t → Admitted batch (r.state t) a) →
    ∃ t, start ≤ t ∧ r.action t = a

/-- Recurrent admission needs strong work justice: an action enabled
arbitrarily late must eventually fire, even if its gate keeps closing. -/
def StrongFair : Prop :=
  ∀ a start, (∀ after, start ≤ after → ∃ t, after ≤ t ∧ Admitted batch (r.state t) a) →
    ∃ t, start ≤ t ∧ r.action t = a

/-- Abstract the internal journal exemption: no new recorded arrival while
the debt gate is closed. This omits the separate flush-active gate. -/
def SuppressedArrivals : Prop :=
  ∀ t, r.action t = .append → (r.state t).backlog < batch

def QuietFrom (start : Nat) : Prop :=
  ∀ t, start ≤ t → r.action t ≠ .append

def GateOpenFrom (start : Nat) : Prop :=
  ∀ t, start ≤ t → (r.state t).backlog < batch

theorem StrongFair.weak {r : Run batch} (fair : r.StrongFair) : r.Fair := by
  intro a start ready
  exact fair a start (fun after later => ⟨after, le_rfl, ready after later⟩)

theorem valid {capacity : Nat} (initial : Valid capacity (r.state 0)) (t : Nat) :
    Valid capacity (r.state t) := by
  induction t with
  | zero => exact initial
  | succ t ih => rw [r.next]; exact apply_valid ih (r.admitted t).1

theorem delivered_le {start t : Nat} (after : start ≤ t) :
    (r.state start).delivered ≤ (r.state t).delivered := by
  induction t, after using Nat.le_induction with
  | base => rfl
  | succ t _ ih =>
      rw [r.next]
      exact ih.trans (delivered_mono _ _)

theorem queued_delivered_le {start t : Nat} (after : start ≤ t) :
    (r.state start).queued + (r.state start).delivered ≤
      (r.state t).queued + (r.state t).delivered := by
  induction t, after using Nat.le_induction with
  | base => rfl
  | succ t _ ih =>
      rw [r.next]
      exact ih.trans (queued_delivered_mono (r.admitted t).1)

theorem backlog_le {start t : Nat} (quiet : r.QuietFrom start) (after : start ≤ t) :
    (r.state t).backlog ≤ (r.state start).backlog := by
  induction t, after using Nat.le_induction with
  | base => rfl
  | succ t after ih =>
      rw [r.next]
      exact (backlog_le_without_append (quiet t after)).trans ih

/-- Under quiescent arrivals, justice for the permitted drainer discharges
the finite backlog. Drain throughput alone is insufficient with new arrivals. -/
theorem eventually_drained (fair : r.Fair) {start : Nat} (quiet : r.QuietFrom start) :
    ∃ t, start ≤ t ∧ (r.state t).backlog = 0 := by
  suffices drain : ∀ debt s, start ≤ s → (r.state s).backlog ≤ debt →
      ∃ t, s ≤ t ∧ (r.state t).backlog = 0 from drain _ start le_rfl le_rfl
  intro debt
  induction debt with
  | zero =>
      intro s _ bound
      exact ⟨s, le_rfl, by omega⟩
  | succ debt ih =>
      intro s after bound
      by_cases done : ∃ t, s ≤ t ∧ (r.state t).backlog = 0
      · exact done
      have pending : ∀ t, s ≤ t → 0 < (r.state t).backlog := by
        intro t later
        by_contra no
        exact done ⟨t, later, by omega⟩
      obtain ⟨t, later, commit⟩ := fair .commit s (by
        intro t later
        exact ⟨pending t later, trivial⟩)
      have atMost : (r.state t).backlog ≤ debt + 1 :=
        (r.backlog_le (fun k le => quiet k (after.trans le)) later).trans bound
      have smaller : (r.state (t + 1)).backlog ≤ debt := by
        rw [r.next, commit]
        simp only [apply]
        omega
      obtain ⟨finish, finishAfter, empty⟩ := ih (t + 1) (by omega) smaller
      exact ⟨finish, by omega, empty⟩

theorem eventually_gate_open (positive : 0 < batch) (fair : r.Fair)
    {start : Nat} (quiet : r.QuietFrom start) :
    ∃ t, start ≤ t ∧ r.GateOpenFrom t := by
  obtain ⟨t, after, empty⟩ := r.eventually_drained fair quiet
  refine ⟨t, after, ?_⟩
  intro k later
  have debt := r.backlog_le (fun k le => quiet k (after.trans le)) later
  omega

/-- Suppression excludes permanent debt gating under drain justice, but
does not imply that a repeatedly admitted network action gets a turn. -/
theorem recurrent_gate_open (positive : 0 < batch) (fair : r.Fair)
    (suppressed : r.SuppressedArrivals) (start : Nat) :
    ∃ t, start ≤ t ∧ (r.state t).backlog < batch := by
  by_contra never
  have quiet : r.QuietFrom start := by
    intro t later arrival
    exact never ⟨t, later, suppressed t arrival⟩
  obtain ⟨t, later, openGate⟩ := r.eventually_gate_open positive fair quiet
  exact never ⟨t, later, openGate t le_rfl⟩

/-- Already queued bytes are eventually consumed if the gate stays open and
read work is just. This does not promise any future packet from the peer. -/
theorem eventually_delivered (fair : r.Fair) {start : Nat}
    (openGate : r.GateOpenFrom start) (queued : 0 < (r.state start).queued) :
    ∃ t, start ≤ t ∧ (r.state start).delivered < (r.state t).delivered := by
  by_contra never
  have unchanged : ∀ t, start ≤ t →
      (r.state t).delivered ≤ (r.state start).delivered := by
    intro t later
    by_contra no
    exact never ⟨t, later, by omega⟩
  obtain ⟨t, later, read⟩ := fair (.read 1) start (by
    intro t later
    have account := r.queued_delivered_le later
    have same := unchanged t later
    exact ⟨⟨by omega, by omega⟩, openGate t later⟩)
  have prior := r.delivered_le later
  have more : (r.state start).delivered < (r.state (t + 1)).delivered := by
    rw [r.next, read]
    simp only [apply]
    omega
  exact never ⟨t + 1, by omega, more⟩

theorem recurrently_open_delivered (fair : r.StrongFair) {start : Nat}
    (opens : ∀ after, start ≤ after → ∃ t, after ≤ t ∧ (r.state t).backlog < batch)
    (queued : 0 < (r.state start).queued) :
    ∃ t, start ≤ t ∧ (r.state start).delivered < (r.state t).delivered := by
  by_contra never
  have unchanged : ∀ t, start ≤ t →
      (r.state t).delivered ≤ (r.state start).delivered := by
    intro t later
    by_contra no
    exact never ⟨t, later, by omega⟩
  obtain ⟨t, later, read⟩ := fair (.read 1) start (by
    intro after later
    obtain ⟨t, afterTime, openGate⟩ := opens after later
    have time := later.trans afterTime
    have account := r.queued_delivered_le time
    have same := unchanged t time
    exact ⟨t, afterTime, ⟨⟨by omega, by omega⟩, openGate⟩⟩)
  have prior := r.delivered_le later
  have more : (r.state start).delivered < (r.state (t + 1)).delivered := by
    rw [r.next, read]
    simp only [apply]
    omega
  exact never ⟨t + 1, by omega, more⟩

theorem suppressed_strongFair_delivered (positive : 0 < batch) (fair : r.StrongFair)
    (suppressed : r.SuppressedArrivals) {start : Nat}
    (queued : 0 < (r.state start).queued) :
    ∃ t, start ≤ t ∧ (r.state start).delivered < (r.state t).delivered :=
  r.recurrently_open_delivered fair
    (fun after _ => r.recurrent_gate_open positive fair.weak suppressed after) queued

/-- Window credit must itself receive service. Merely freeing application
buffer space is not a window update. Incoming bytes may refill it afterward. -/
theorem eventually_credited (fair : r.Fair) {start : Nat}
    (openGate : r.GateOpenFrom start) (pending : 0 < (r.state start).uncredited) :
    ∃ t, start ≤ t ∧ r.action t = .credit ∧
      (r.state t).window < (r.state (t + 1)).window := by
  have occurs : ∃ t, start ≤ t ∧ r.action t = .credit := by
    by_contra never
    have retained : ∀ t, start ≤ t →
        (r.state start).uncredited ≤ (r.state t).uncredited := by
      intro t later
      induction t, later using Nat.le_induction with
      | base => rfl
      | succ t later ih =>
          have noCredit : r.action t ≠ .credit := fun eq => never ⟨t, later, eq⟩
          rw [r.next]
          cases act : r.action t
          all_goals simp_all [apply]
          all_goals omega
    exact never (fair .credit start (by
      intro t later
      refine ⟨?_, openGate t later⟩
      change 0 < (r.state t).uncredited
      have := retained t later
      omega))
  obtain ⟨t, later, credit⟩ := occurs
  refine ⟨t, later, credit, ?_⟩
  have ready := (r.admitted t).1
  rw [credit] at ready
  rw [r.next, credit]
  simp only [Prepared] at ready
  simp only [apply]
  omega

theorem eventually_timer (fair : r.Fair) {start : Nat}
    (openGate : r.GateOpenFrom start) :
    ∃ t, start ≤ t ∧ r.action t = .timer ∧
      (r.state (t + 1)).timers = (r.state t).timers + 1 := by
  obtain ⟨t, later, timer⟩ := fair .timer start (fun t later =>
    ⟨trivial, openGate t later⟩)
  exact ⟨t, later, timer, by rw [r.next, timer]; rfl⟩

/-- Combining the rank argument with byte conservation gives end-to-end
consumption of already queued data after arrivals become quiet. -/
theorem quiet_eventually_delivered (positive : 0 < batch) (fair : r.Fair)
    {start : Nat} (quiet : r.QuietFrom start) (queued : 0 < (r.state start).queued) :
    ∃ t, start ≤ t ∧ (r.state start).delivered < (r.state t).delivered := by
  obtain ⟨openAt, after, openGate⟩ := r.eventually_gate_open positive fair quiet
  by_cases already : (r.state start).delivered < (r.state openAt).delivered
  · exact ⟨openAt, after, already⟩
  have account := r.queued_delivered_le after
  have pending : 0 < (r.state openAt).queued := by omega
  obtain ⟨t, later, delivered⟩ := r.eventually_delivered fair openGate pending
  have before := r.delivered_le after
  exact ⟨t, after.trans later, by omega⟩

end Run

/-! ## A sustained-load counterexample, with real commits and free window -/

def cycleState (batch queued window t : Nat) : State :=
  ⟨batch + t % 2, queued, 0, window, 0, t / 2, 0⟩

def cycleAction (t : Nat) : Action :=
  if t % 2 = 0 then .append else .commit

theorem cycle_admitted (batch queued window t : Nat) :
    Admitted batch (cycleState batch queued window t) (cycleAction t) := by
  unfold cycleAction
  split <;> simp_all [Admitted, Prepared, Permitted, Action.actor, Eligible, cycleState]

theorem cycle_next (batch queued window t : Nat) :
    cycleState batch queued window (t + 1) =
      apply (cycleAction t) (cycleState batch queued window t) := by
  unfold cycleAction
  split
  next even =>
    have quotient : (t + 1) / 2 = t / 2 := by
      rw [Nat.add_div]
      · simp [even]
      · decide
    simp only [apply, cycleState, State.mk.injEq, and_true, true_and]
    exact ⟨by omega, quotient⟩
  next odd =>
    have remainder : t % 2 = 1 := by omega
    have quotient : (t + 1) / 2 = t / 2 + 1 := by
      rw [Nat.add_div]
      · simp [remainder]
      · decide
    simp only [apply, cycleState, State.mk.injEq, and_true, true_and]
    exact ⟨by omega, quotient⟩

def starvation (batch queued window : Nat) : Run batch where
  state := cycleState batch queued window
  action := cycleAction
  admitted := cycle_admitted batch queued window
  next := cycle_next batch queued window

theorem starvation_actor_fair (batch queued window : Nat) :
    (starvation batch queued window).ActorFair := by
  intro actor start eligible
  cases actor with
  | files =>
      exact ⟨2 * start, by omega, by simp [starvation, cycleAction, Action.actor]⟩
  | drive =>
      exact ⟨2 * start + 1, by omega, by simp [starvation, cycleAction, Action.actor]⟩
  | network | browser =>
      have no := eligible start le_rfl
      simp only [starvation, cycleState, Eligible] at no
      omega

/-- Even justice for every continuously admitted action does not repair a
permanently excluded work class. Both journal actions fire infinitely often. -/
theorem starvation_fair (batch queued window : Nat) :
    (starvation batch queued window).Fair := by
  intro a start admitted
  cases a with
  | append => exact ⟨2 * start, by omega, by simp [starvation, cycleAction]⟩
  | commit => exact ⟨2 * start + 1, by omega, by simp [starvation, cycleAction]⟩
  | receive n | read n | credit | timer =>
      have no := (admitted start le_rfl).2
      simp only [Permitted, Action.actor, Eligible, starvation, cycleState] at no
      omega

theorem starvation_valid (batch queued window t : Nat) :
    Valid (queued + window) ((starvation batch queued window).state t) := by
  simp [Valid, starvation, cycleState]

theorem starvation_retains_bytes (batch queued window t : Nat) :
    ((starvation batch queued window).state t).queued = queued ∧
    ((starvation batch queued window).state t).window = window ∧
    ((starvation batch queued window).state t).delivered = 0 ∧
    ((starvation batch queued window).state t).timers = 0 := by
  simp [starvation, cycleState]

theorem starvation_commits_unbounded (batch queued window n : Nat) :
    ((starvation batch queued window).state (2 * n)).committed = n := by
  simp [starvation, cycleState]

theorem starvation_bounded_journal (batch queued window t : Nat) :
    batch ≤ ((starvation batch queued window).state t).backlog ∧
    ((starvation batch queued window).state t).backlog ≤ batch + 1 := by
  simp only [starvation, cycleState]
  omega

theorem starvation_violates_suppression (batch queued window : Nat) :
    ¬ (starvation batch queued window).SuppressedArrivals := by
  intro suppressed
  have impossible := suppressed 0 (by simp [starvation, cycleAction])
  simp [starvation, cycleState] at impossible

theorem prepared_read_not_permitted (batch queued window t : Nat) (pending : 0 < queued) :
    Prepared ((starvation batch queued window).state t) (.read 1) ∧
    ¬ Permitted batch ((starvation batch queued window).state t) (.read 1) := by
  simp only [Prepared, Permitted, Action.actor, Eligible, starvation, cycleState]
  omega

/-- Increasing the window cannot by itself establish service progress: for
every capacity split there remains a legal, just, non-draining receive trace. -/
theorem every_window_has_starvation (batch queued window : Nat) (pending : 0 < queued) :
    ∃ r : Run batch, r.Fair ∧ r.ActorFair ∧
      (∀ t, Valid (queued + window) (r.state t)) ∧
      (∀ t, 0 < (r.state t).queued ∧ (r.state t).delivered = 0 ∧
        (r.state t).window = window ∧ (r.state t).timers = 0) ∧
      (∀ n, (r.state (2 * n)).committed = n) := by
  refine ⟨starvation batch queued window, starvation_fair _ _ _,
    starvation_actor_fair _ _ _, starvation_valid _ _ _, ?_, starvation_commits_unbounded _ _ _⟩
  intro t
  simp [starvation, cycleState, pending]

/-! ## Execution by the existing rotating successor scheduler -/

/-- One-byte reads suffice for this service frontier. Incoming bytes are
environmental offers; no incoming packet is needed for the counterexample. -/
def serviceNext (batch : Nat) (s : State) : List State :=
  ([Action.append, .commit, .read 1, .credit, .timer].filter
    (fun a => decide (Admitted batch s a))).map (fun a => apply a s)

theorem serviceNext_cycle {batch : Nat} (positive : 0 < batch) (queued window t : Nat) :
    serviceNext batch (cycleState batch queued window t) =
      [apply .append (cycleState batch queued window t),
       apply .commit (cycleState batch queued window t)] := by
  have blocked : ¬ batch + t % 2 < batch := by omega
  have debt : 0 < batch + t % 2 := by omega
  simp [serviceNext, Admitted, Prepared, Permitted, Eligible, Action.actor, cycleState,
    blocked, debt]

/-- With positive journal threshold the authored rotating scheduler itself
realizes the starving execution, without an adversarial tie-break oracle. -/
theorem rotating_step_cycle {batch : Nat} (positive : 0 < batch) (queued window t : Nat) :
    ScheduledRun.step (serviceNext batch) ScheduledRun.rotating t
      (some (cycleState batch queued window t)) =
        some (cycleState batch queued window (t + 1)) := by
  rw [cycle_next]
  have next := serviceNext_cycle positive queued window t
  rw [ScheduledRun.step_next_congr _
    (fun s => [apply .append s, apply .commit s]) _ _ _ next]
  by_cases even : t % 2 = 0
  · simp [ScheduledRun.step, ScheduledRun.rotating, cycleAction, even]
  · have odd : t % 2 = 1 := by omega
    simp [ScheduledRun.step, ScheduledRun.rotating, cycleAction, odd]

theorem rotating_run_cycle {batch : Nat} (positive : 0 < batch) (queued window t : Nat) :
    ScheduledRun.run (serviceNext batch) ScheduledRun.rotating
      (cycleState batch queued window 0) t = some (cycleState batch queued window t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ScheduledRun.run_succ, ih, rotating_step_cycle positive]

/-! ## Repeated reopening still does not imply weakly just service -/

/-- Drain at the threshold, then append while the gate is open. This obeys
arrival suppression. It is not claimed to be a run of the implementation FIFO. -/
def pulse (batch queued window : Nat) : Run batch where
  state t := cycleState (batch - 1) queued window (t + 1)
  action t := cycleAction (t + 1)
  admitted t := by
    have old := cycle_admitted (batch - 1) queued window (t + 1)
    refine ⟨old.1, ?_⟩
    unfold cycleAction
    split <;> trivial
  next t := cycle_next (batch - 1) queued window (t + 1)

theorem pulse_suppresses {batch : Nat} (positive : 0 < batch) (queued window : Nat) :
    (pulse batch queued window).SuppressedArrivals := by
  intro t arrival
  simp only [pulse, cycleAction] at arrival
  split at arrival
  next even => simp only [pulse, cycleState, even]; omega
  next odd => contradiction

theorem pulse_reopens {batch : Nat} (positive : 0 < batch) (queued window start : Nat) :
    ∃ t, start ≤ t ∧ ((pulse batch queued window).state t).backlog < batch := by
  refine ⟨2 * start + 1, by omega, ?_⟩
  have even : (2 * start + 1 + 1) % 2 = 0 := by omega
  simp only [pulse, cycleState, even]
  omega

theorem pulse_fair {batch : Nat} (positive : 0 < batch) (queued window : Nat) :
    (pulse batch queued window).Fair := by
  intro a start ready
  cases a with
  | append =>
      refine ⟨2 * start + 1, by omega, ?_⟩
      have even : (2 * start + 1 + 1) % 2 = 0 := by omega
      simp [pulse, cycleAction, even]
  | commit =>
      exact ⟨2 * start, by omega, by simp [pulse, cycleAction]⟩
  | receive n | read n | credit | timer =>
      have no := (ready (2 * start) (by omega)).2
      simp [Permitted, Action.actor, Eligible, pulse, cycleState] at no
      omega

theorem pulse_never_delivers (batch queued window t : Nat) :
    ((pulse batch queued window).state t).queued = queued ∧
    ((pulse batch queued window).state t).delivered = 0 ∧
    ((pulse batch queued window).state t).timers = 0 := by
  simp [pulse, cycleState]

theorem pulse_not_strongFair {batch : Nat} (positive : 0 < batch)
    (queued window : Nat) (pending : 0 < queued) :
    ¬ (pulse batch queued window).StrongFair := by
  intro fair
  obtain ⟨t, _, more⟩ := (pulse batch queued window).suppressed_strongFair_delivered
    positive fair (pulse_suppresses positive queued window) (start := 0) pending
  simp [pulse, cycleState] at more

theorem weak_justice_with_reopening_counterexample {batch : Nat} (positive : 0 < batch)
    (queued window : Nat) (pending : 0 < queued) :
    ∃ r : Run batch, r.Fair ∧ r.SuppressedArrivals ∧
      (∀ start, ∃ t, start ≤ t ∧ (r.state t).backlog < batch) ∧
      (∀ t, 0 < (r.state t).queued ∧ (r.state t).delivered = 0 ∧ (r.state t).timers = 0) := by
  refine ⟨pulse batch queued window, pulse_fair positive _ _, pulse_suppresses positive _ _,
    pulse_reopens positive _ _, ?_⟩
  intro t
  simp [pulse, cycleState, pending]

namespace Controls

theorem smaller_receive_fits_window :
    Admitted 64 ⟨0, 2798, 0, 1298, 0, 0, 0⟩ (.receive 778) := by decide

theorem oversized_segment_refused :
    ¬ Prepared ⟨0, 2798, 0, 1298, 0, 0, 0⟩ (.receive 1299) := by decide

theorem read_then_credit_reopens_window :
    (apply .credit (apply (.read 256) ⟨0, 2798, 0, 1298, 0, 0, 0⟩)).window = 1554 := by
  decide

theorem reading_alone_does_not_reopen_window :
    (apply (.read 256) ⟨0, 2798, 0, 1298, 0, 0, 0⟩).window = 1298 := by decide

end Controls

#print axioms every_window_has_starvation
#print axioms Run.eventually_drained
#print axioms Run.eventually_delivered
#print axioms Run.eventually_credited
#print axioms Run.eventually_timer
#print axioms Run.quiet_eventually_delivered
#print axioms rotating_run_cycle
#print axioms pulse_fair
#print axioms pulse_not_strongFair
#print axioms weak_justice_with_reopening_counterexample
#print axioms Run.suppressed_strongFair_delivered
#print axioms apply_valid
#print axioms positive_window_admits_prefix
#print axioms Run.recurrent_gate_open

end Mettapedia.Machines.NetworkBackpressure
