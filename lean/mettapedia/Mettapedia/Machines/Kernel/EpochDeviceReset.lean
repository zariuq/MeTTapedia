import Mathlib.Tactic

/-!
# Kernel-visible device reset epochs

A driver may choose how to rebuild its queues, but reset authority is indexed by
one held device, one interrupt revision and one controller generation.  Begin,
observed quiescence and queue-gated resume each append one causal event.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.EpochDeviceReset

inductive Phase where
  | active
  | resetting
  | quiescent
  | orphaned
  deriving DecidableEq, Repr

inductive Action where
  | query
  | begin (expected produced acknowledged : Nat)
  | acknowledge (expected produced heard : Nat)
  | observeQuiescent (expected produced acknowledged : Nat) (ccEnabled cstsReady : Bool)
  | resume (expected produced acknowledged : Nat) (ccEnabled cstsReady queuesReady : Bool)
  | ownerDead (expected produced acknowledged : Nat)
  deriving DecidableEq, Repr

inductive Status where
  | ok
  | invalid
  | stale
  | interrupted
  | hardware
  | exhausted
  deriving DecidableEq, Repr

structure Event where
  epoch : Nat
  action : Nat
  generation : Nat
  interruptRevision : Nat
  acknowledgedRevision : Nat
  phase : Phase
  ccEnabled : Bool
  cstsReady : Bool
  interruptMasked : Bool
  deriving DecidableEq, Repr

structure State where
  owner : Nat
  device : Nat
  identity : Nat
  vector : Nat
  generation : Nat
  interruptRevision : Nat
  acknowledgedRevision : Nat
  phase : Phase
  interruptMasked : Bool
  ledger : List Event
  generationLimit : Nat
  eventCapacity : Nat
  otherResource : Nat
  deriving DecidableEq, Repr

def record (state : State) (action : Nat)
    (generation interruptRevision acknowledgedRevision : Nat)
    (phase : Phase) (ccEnabled cstsReady interruptMasked : Bool) : State :=
  { state with
    generation := generation
    interruptRevision := interruptRevision
    acknowledgedRevision := acknowledgedRevision
    phase := phase
    interruptMasked := interruptMasked
    ledger := state.ledger ++ [⟨state.ledger.length + 1, action, generation,
      interruptRevision, acknowledgedRevision, phase, ccEnabled, cstsReady,
      interruptMasked⟩] }

def canRecord (state : State) : Bool := state.ledger.length < state.eventCapacity

def ackPermitted (state : State) (produced heard : Nat) : Bool :=
  decide (heard = state.acknowledgedRevision + 1 ∧ heard ≤ produced)

def step (state : State) (action : Action) : State × Status := match action with
  | .query => (state, .ok)
  | .begin expected produced acknowledged =>
      if expected ≠ state.generation then (state, .stale)
      else if state.phase ≠ .active then (state, .invalid)
      else if state.interruptMasked then (state, .invalid)
      else if produced ≠ acknowledged then (state, .interrupted)
      else if state.generation ≥ state.generationLimit ∨ !canRecord state then
        (state, .exhausted)
      else (record state 1 state.generation produced acknowledged .resetting true true true, .ok)
  | .acknowledge expected produced heard =>
      if expected ≠ state.generation then (state, .stale)
      else if state.phase = .orphaned then (state, .invalid)
      else if ¬ackPermitted state produced heard then
        (state, .interrupted)
      else if !canRecord state then (state, .exhausted)
      else (record state 4 state.generation state.interruptRevision heard state.phase
        true true state.interruptMasked, .ok)
  | .observeQuiescent expected produced acknowledged ccEnabled cstsReady =>
      if expected ≠ state.generation then (state, .stale)
      else if state.phase ≠ .resetting then (state, .invalid)
      else if !state.interruptMasked then (state, .invalid)
      else if produced ≠ acknowledged then (state, .interrupted)
      else if ccEnabled ∨ cstsReady then (state, .hardware)
      else if !canRecord state then (state, .exhausted)
      else (record state 2 state.generation produced acknowledged .quiescent
        ccEnabled cstsReady true, .ok)
  | .resume expected produced acknowledged ccEnabled cstsReady queuesReady =>
      if expected ≠ state.generation then (state, .stale)
      else if state.phase ≠ .quiescent ∨ !queuesReady then (state, .invalid)
      else if !state.interruptMasked then (state, .invalid)
      else if produced ≠ acknowledged ∨ produced ≠ state.interruptRevision then
        (state, .interrupted)
      else if !ccEnabled ∨ !cstsReady then (state, .hardware)
      else if state.generation ≥ state.generationLimit ∨ !canRecord state then
        (state, .exhausted)
      else (record state 3 (state.generation + 1) produced acknowledged .active
        ccEnabled cstsReady false, .ok)
  | .ownerDead expected produced acknowledged =>
      if expected ≠ state.generation then (state, .stale)
      else if state.phase = .orphaned then (state, .invalid)
      else if !canRecord state then (state, .exhausted)
      else (record state 5 state.generation produced acknowledged .orphaned false false true, .ok)

theorem record_advances_once (state : State)
    (action generation interruptRevision acknowledgedRevision : Nat)
    (phase : Phase) (ccEnabled cstsReady interruptMasked : Bool) :
    (record state action generation interruptRevision acknowledgedRevision phase
      ccEnabled cstsReady interruptMasked).ledger.length =
      state.ledger.length + 1 := by
  simp [record]

theorem step_preserves_authority (state : State) (action : Action) :
    let next := (step state action).1
    next.owner = state.owner ∧ next.device = state.device ∧
      next.identity = state.identity ∧ next.vector = state.vector ∧
      next.otherResource = state.otherResource := by
  cases action
  all_goals
    simp only [step]
    repeat' split
    all_goals simp_all [record, canRecord]

theorem successful_nonquery_records {state next : State} {action : Action}
    (notQuery : action ≠ .query) (transition : step state action = (next, .ok)) :
    next.ledger.length = state.ledger.length + 1 := by
  cases action
  case query => contradiction
  all_goals
    simp only [step] at transition
    repeat' split at transition
    all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all

theorem quiescence_requires_exact_observation {state next : State}
    {expected produced acknowledged : Nat} {ccEnabled cstsReady : Bool}
    (transition : step state (.observeQuiescent expected produced acknowledged
      ccEnabled cstsReady) = (next, .ok)) :
    expected = state.generation ∧ produced = acknowledged ∧
      state.interruptMasked = true ∧ ccEnabled = false ∧ cstsReady = false ∧
      next.phase = .quiescent ∧ next.interruptMasked = true := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all

theorem resume_advances_generation {state next : State}
    {expected produced acknowledged : Nat} {ccEnabled cstsReady queuesReady : Bool}
    (transition : step state (.resume expected produced acknowledged ccEnabled cstsReady
      queuesReady) = (next, .ok)) :
    state.phase = .quiescent ∧ queuesReady = true ∧
      produced = acknowledged ∧ produced = state.interruptRevision ∧ ccEnabled = true ∧
      cstsReady = true ∧ next.generation = state.generation + 1 ∧
      state.interruptMasked = true ∧ next.phase = .active ∧
      next.interruptMasked = false := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all
    aesop

theorem unacknowledged_interrupt_refuses_quiescence (state : State)
    (expected produced acknowledged : Nat)
    (resetting : state.phase = .resetting)
    (masked : state.interruptMasked = true)
    (current : expected = state.generation)
    (pending : produced ≠ acknowledged) :
    step state (.observeQuiescent expected produced acknowledged false false) =
      (state, .interrupted) := by
  simp [step, resetting, masked, current, pending]

theorem permitted_ack_consumes_next (state : State) (expected produced heard : Nat)
    (expectedEq : expected = state.generation)
    (notOrphaned : state.phase ≠ .orphaned)
    (permitted : ackPermitted state produced heard = true)
    (capacity : canRecord state = true) :
    step state (.acknowledge expected produced heard) =
      (record state 4 state.generation state.interruptRevision heard state.phase true true
        state.interruptMasked, .ok) := by
  simp [step, expectedEq, notOrphaned, permitted, capacity]

theorem failed_step_preserves_state {state next : State} {action : Action} {status : Status}
    (failed : status ≠ .ok) (transition : step state action = (next, status)) :
    next = state := by
  cases action
  all_goals
    simp only [step] at transition
    repeat' split at transition
    all_goals simp_all [record, canRecord]

theorem begin_masks_interrupt {state next : State}
    {expected produced acknowledged : Nat}
    (transition : step state (.begin expected produced acknowledged) = (next, .ok)) :
    state.interruptMasked = false ∧ next.interruptMasked = true := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all

theorem begin_requires_acknowledged_interrupts {state next : State}
    {expected produced acknowledged : Nat}
    (transition : step state (.begin expected produced acknowledged) = (next, .ok)) :
    produced = acknowledged := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]

theorem resume_unmasks_interrupt {state next : State}
    {expected produced acknowledged : Nat} {ccEnabled cstsReady queuesReady : Bool}
    (transition : step state (.resume expected produced acknowledged ccEnabled cstsReady
      queuesReady) = (next, .ok)) :
    state.interruptMasked = true ∧ next.interruptMasked = false := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all

theorem owner_death_masks_interrupt {state next : State}
    {expected produced acknowledged : Nat}
    (transition : step state (.ownerDead expected produced acknowledged) = (next, .ok)) :
    next.interruptMasked = true := by
  simp only [step] at transition
  repeat' split at transition
  all_goals simp_all [record, canRecord]
  all_goals
    subst next
    simp_all

namespace Controls

def initial : State := ⟨2, 0x100, 0x5845101b, 0x22, 1, 7, 7, .active, false, [], 4, 8, 99⟩
def begun : State := (step initial (.begin 1 7 7)).1
def pendingRefused : Status := (step begun (.observeQuiescent 1 8 7 false false)).2
def acknowledged : State := (step begun (.acknowledge 1 8 8)).1
def quiet : State := (step acknowledged (.observeQuiescent 1 8 8 false false)).1
def resumed : State := (step quiet (.resume 1 8 8 true true true)).1
def orphaned : State := (step resumed (.ownerDead 2 8 8)).1
def pendingBeforeBegin : State :=
  { initial with interruptRevision := 0, acknowledgedRevision := 0 }
def pendingBeginStatus : Status := (step pendingBeforeBegin (.begin 1 1 0)).2
def drainedBeforeBegin : State := (step pendingBeforeBegin (.acknowledge 1 1 1)).1
def begunAfterDrain : State := (step drainedBeforeBegin (.begin 1 1 1)).1

theorem begin_records :
    begun.phase = .resetting ∧ begun.interruptMasked = true ∧ begun.ledger.length = 1 := by decide
theorem pending_interrupt_refused : pendingRefused = .interrupted := by decide
theorem interrupt_acknowledged :
    acknowledged.acknowledgedRevision = 8 ∧ acknowledged.ledger.length = 2 := by decide
theorem quiescence_records : quiet.phase = .quiescent ∧ quiet.ledger.length = 3 := by decide
theorem resume_records :
    resumed.phase = .active ∧ resumed.interruptMasked = false ∧
      resumed.generation = 2 ∧ resumed.ledger.length = 4 := by decide
theorem event_actions_exact : resumed.ledger.map (·.action) = [1, 4, 2, 3] := by decide
theorem stale_begin_refused : (step initial (.begin 2 7 7)).2 = .stale := by decide
theorem enabled_not_quiescent :
    (step acknowledged (.observeQuiescent 1 8 8 true false)).2 = .hardware := by decide
theorem queues_required : (step quiet (.resume 1 8 8 true true false)).2 = .invalid := by decide
theorem owner_death_orphans :
    orphaned.phase = .orphaned ∧ orphaned.interruptMasked = true ∧
      orphaned.ledger.map (·.action) = [1, 4, 2, 3, 5] := by decide
theorem unrelated_resource_survives : resumed.otherResource = initial.otherResource := by decide
theorem pending_receipt_defers_begin : pendingBeginStatus = .interrupted := by decide
theorem exact_receipt_allows_begin :
    drainedBeforeBegin.acknowledgedRevision = 1 ∧ begunAfterDrain.phase = .resetting ∧
      begunAfterDrain.interruptMasked = true := by decide

end Controls

#print axioms record_advances_once
#print axioms step_preserves_authority
#print axioms successful_nonquery_records
#print axioms quiescence_requires_exact_observation
#print axioms resume_advances_generation
#print axioms unacknowledged_interrupt_refuses_quiescence
#print axioms permitted_ack_consumes_next
#print axioms failed_step_preserves_state
#print axioms begin_masks_interrupt
#print axioms begin_requires_acknowledged_interrupts
#print axioms resume_unmasks_interrupt
#print axioms owner_death_masks_interrupt

end Mettapedia.Machines.Kernel.EpochDeviceReset
