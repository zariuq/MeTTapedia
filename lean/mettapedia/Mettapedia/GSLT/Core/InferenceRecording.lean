import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.Machines.TraceObservationBoundary
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Bounded recording of controlled inference

Recording extends the existing controller memory. Scheduling sees only the
original memory, so erasing the recorder preserves the complete search state
and controller continuation. The recorder keeps a bounded prefix in order,
with an explicit omitted count; truncation does not stop the search.

Recorded items describe selected inference occurrences, not automatically
committed external effects. A client chooses which existing node information
to materialize. Disabled and full recorders do not request materialization.
The model counts recording requests and retained items, not CPU instructions
or bytes. Concrete allocation, identity and concurrency services need their
own implementation correspondence. Complete payload projections require every
inner decoder to succeed. An abstract retained-storage bound additionally
requires a charge for each retained payload and the owners it keeps alive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.InferenceControl.Recording

open Mettapedia.GSLT.Core.BranchingTemporal

variable {Node Answer Memory Event Payload : Type*}

/-- A prefix retained in reverse order, with unused capacity and the number
of later items omitted. Once capacity is exhausted it is never replenished
by resumption. -/
structure Prefix (Event : Type*) where
  reversed : List Event
  remaining : Nat
  omitted : Nat
deriving DecidableEq, Repr

namespace Prefix

def initial (capacity : Nat) : Prefix Event := ⟨[], capacity, 0⟩

def items (record : Prefix Event) : List Event := record.reversed.reverse

/-- Transport retained payloads without changing capacity or omission status.
This is an observation of an existing record, not a request to record an
unavailable prefix of execution. -/
def map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : Prefix NextEvent :=
  ⟨record.reversed.map mapping, record.remaining, record.omitted⟩

@[simp] theorem map_id (record : Prefix Event) : record.map id = record := by
  cases record
  simp [map]

theorem map_comp {NextEvent FinalEvent : Type*}
    (first : Event → NextEvent) (second : NextEvent → FinalEvent) (record : Prefix Event) :
    (record.map first).map second = record.map (second ∘ first) := by
  simp [map, List.map_map]

@[simp] theorem items_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : (record.map mapping).items = record.items.map mapping := by
  simp [map, items, List.map_reverse]

/-- The thunk is demanded only when storage is available. The omitted
count is recording overhead even when no payload is materialized. -/
def push (record : Prefix Event) (event : Unit → Event) : Prefix Event :=
  match record.remaining with
  | 0 => { record with omitted := record.omitted + 1 }
  | left + 1 => { record with reversed := event () :: record.reversed, remaining := left }

/-- Payload transport commutes with accepting an event, including a full
prefix that only increases its omission count. -/
theorem push_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) (event : Unit → Event) :
    (record.push event).map mapping =
      (record.map mapping).push (fun _ => mapping (event ())) := by
  cases available : record.remaining <;> simp [push, map, available]

def append : Prefix Event → List Event → Prefix Event
  | record, [] => record
  | record, event :: rest => append (record.push (fun _ => event)) rest

/-- Only an untruncated prefix may be presented as the complete recording
since its captured start. It says nothing about execution before that start. -/
def complete? (record : Prefix Event) : Option (List Event) :=
  if record.omitted = 0 then some record.items else none

theorem complete?_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Prefix Event) : (record.map mapping).complete? =
      record.complete?.map (List.map mapping) := by
  by_cases complete : record.omitted = 0 <;> simp [complete?, map, items, complete]

theorem push_full (record : Prefix Event) (full : record.remaining = 0)
    (first second : Unit → Event) : record.push first = record.push second := by
  simp [push, full]

theorem append_append (record : Prefix Event) (first second : List Event) :
    record.append (first ++ second) = (record.append first).append second := by
  induction first generalizing record with
  | nil => rfl
  | cons event rest ih => exact ih _

theorem append_state (record : Prefix Event) (events : List Event) :
    (record.append events).items = record.items ++ events.take record.remaining ∧
      (record.append events).remaining = record.remaining - events.length ∧
      (record.append events).omitted = record.omitted + (events.length - record.remaining) := by
  induction events generalizing record with
  | nil => simp [append]
  | cons event rest ih =>
      cases available : record.remaining with
      | zero =>
          obtain ⟨retained, left, omitted⟩ := ih (record.push (fun _ => event))
          simp only [append, push, available]
          simp only [push, available] at retained left omitted
          simp [items] at retained ⊢
          exact ⟨retained, by simpa using left, by omega⟩
      | succ availableCount =>
          obtain ⟨retained, left, omitted⟩ := ih (record.push (fun _ => event))
          simp only [append, push, available]
          simp only [push, available] at retained left omitted
          simp only [items, List.reverse_cons] at retained
          refine ⟨?_, ?_, ?_⟩
          · simpa [available, items, List.append_assoc] using retained
          · simpa [available] using left
          · simpa [available] using omitted

theorem initial_items (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).items = events.take capacity := by
  simpa [initial, items] using (append_state (initial capacity) events).1

theorem initial_omitted (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).omitted = events.length - capacity := by
  simpa [initial] using (append_state (initial capacity) events).2.2

theorem complete_iff (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).complete? = some events ↔
      events.length ≤ capacity := by
  rw [complete?, initial_omitted]
  by_cases fits : events.length ≤ capacity
  · simp [fits, Nat.sub_eq_zero_of_le fits, initial_items, List.take_of_length_le fits]
  · have positive : events.length - capacity ≠ 0 := by omega
    simp [fits, positive]

/-- The two numerical readouts count retained payloads and omitted requests
separately. Their sum is the exact number of observed selections. -/
theorem request_account (capacity : Nat) (events : List Event) :
    ((initial capacity : Prefix Event).append events).items.length +
      ((initial capacity : Prefix Event).append events).omitted = events.length := by
  rw [initial_items, initial_omitted, List.length_take]
  omega


private theorem mapPayloads_iff (decode : Event → Option Payload)
    (events : List Event) (payloads : List Payload) :
    events.mapM decode = some payloads ↔
      List.Forall₂ (fun event payload => decode event = some payload) events payloads := by
  induction events generalizing payloads with
  | nil => cases payloads <;> simp
  | cons event rest ih =>
      cases decoded : decode event with
      | none => cases payloads <;> simp [List.mapM_cons, decoded]
      | some payload =>
          cases payloads with
          | nil =>
              cases tail : rest.mapM decode <;> simp [List.mapM_cons, decoded, tail]
          | cons first others =>
              cases tail : rest.mapM decode with
              | none => simp [List.mapM_cons, decoded, tail, ← ih]
              | some values => simp [List.mapM_cons, decoded, tail, ← ih]

/-- Decode every retained payload only when the outer prefix is complete.
A refused inner graph makes the projection incomplete, rather than silently
filtering that occurrence from a successful readout. -/
def project? (decode : Event → Option Payload) (record : Prefix Event) : Option (List Payload) :=
  record.complete?.bind (fun events => events.mapM decode)

theorem project?_iff (decode : Event → Option Payload) (record : Prefix Event)
    (payloads : List Payload) : project? decode record = some payloads ↔
    record.omitted = 0 ∧
      List.Forall₂ (fun event payload => decode event = some payload) record.items payloads := by
  by_cases complete : record.omitted = 0
  · simp [project?, complete?, complete, mapPayloads_iff]
  · simp [project?, complete?, complete]

theorem project?_length (decode : Event → Option Payload) (record : Prefix Event)
    (payloads : List Payload) (accepted : project? decode record = some payloads) :
    payloads.length = record.items.length :=
  ((project?_iff decode record payloads).mp accepted).2.length_eq.symm

theorem project?_truncated (decode : Event → Option Payload) (record : Prefix Event)
    (lost : record.omitted ≠ 0) : project? decode record = none := by
  simp [project?, complete?, lost]

/-- An inner refusal cannot disappear from a complete outer recording. -/
theorem project?_refused (decode : Event → Option Payload) (record : Prefix Event)
    (event : Event) (member : event ∈ record.items) (refused : decode event = none) :
    project? decode record = none := by
  cases result : project? decode record with
  | none => rfl
  | some payloads =>
      have related := ((project?_iff decode record payloads).mp result).2
      have all : ∀ event ∈ record.items, ∃ payload, decode event = some payload := by
        clear result
        generalize record.items = events at related ⊢
        induction related with
        | nil => simp
        | cons decoded rest ih =>
            intro event found
            rcases List.mem_cons.mp found with rfl | found
            · exact ⟨_, decoded⟩
            · exact ih event found
      obtain ⟨payload, decoded⟩ := all event member
      simp [refused] at decoded

/-- Occurrence keys are retained when the payload decoder preserves them.
Payload equality alone supplies no such identity law. -/
theorem project?_keys {Key : Type*} (decode : Event → Option Payload)
    (eventKey : Event → Key) (payloadKey : Payload → Key)
    (faithful : ∀ event payload, decode event = some payload → eventKey event = payloadKey payload)
    (record : Prefix Event) (payloads : List Payload)
    (accepted : project? decode record = some payloads) :
    record.items.map eventKey = payloads.map payloadKey := by
  have related := ((project?_iff decode record payloads).mp accepted).2
  clear accepted
  generalize record.items = events at related ⊢
  induction related with
  | nil => rfl
  | cons decoded rest ih =>
      simp only [List.map_cons]
      rw [faithful _ _ decoded, ih]

theorem initial_project?_iff (decode : Event → Option Payload) (capacity : Nat)
    (events : List Event) (payloads : List Payload) :
    project? decode ((initial capacity).append events) = some payloads ↔
      events.length ≤ capacity ∧
        List.Forall₂ (fun event payload => decode event = some payload) events payloads := by
  rw [project?_iff, initial_omitted, initial_items]
  by_cases fits : events.length ≤ capacity
  · simp [fits, Nat.sub_eq_zero_of_le fits, List.take_of_length_le fits]
  · have positive : events.length - capacity ≠ 0 := by omega
    simp [positive, fits]

/-- A conservative retained-storage charge is bounded only when every
retained payload has a supplied charge bound. Node count alone supplies none. -/
theorem retained_charge_bound (charge : Event → Nat) (capacity perItem : Nat)
    (events : List Event) (bounded : ∀ event ∈ events.take capacity, charge event ≤ perItem) :
    ((((initial capacity : Prefix Event).append events).items).map charge).sum ≤ capacity * perItem := by
  rw [initial_items]
  have localBound := List.sum_le_card_nsmul ((events.take capacity).map charge) perItem (by
    intro value member
    obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
    exact bounded event eventMember)
  simp only [List.length_map, List.length_take, nsmul_eq_mul] at localBound
  exact localBound.trans (Nat.mul_le_mul_right perItem (Nat.min_le_left _ _))

/-- A complete graph readout uses the existing causal receipt. Its explicit
boundary lists dependencies captured before this recording scope. Structural
checking does not authenticate the evaluator's claimed dependency edges. -/
def graph? [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event)) :
    Option (Mettapedia.Machines.CausalReceipt Event) := do
  let events ← record.complete?
  let receipt : Mettapedia.Machines.CausalReceipt Event := ⟨roots, events⟩
  if receipt.check boundary then some receipt else none

theorem graph?_sound [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event))
    (receipt : Mettapedia.Machines.CausalReceipt Event)
    (accepted : graph? boundary roots record = some receipt) :
    record.complete? = some receipt.events ∧ receipt.WellFormed boundary ∧ receipt.roots = roots := by
  unfold graph? at accepted
  cases complete : record.complete? with
  | none => simp [complete] at accepted
  | some events =>
    simp only [complete] at accepted
    change (if Mettapedia.Machines.CausalReceipt.check boundary ⟨roots, events⟩
      then some ⟨roots, events⟩ else none) = some receipt at accepted
    split at accepted
    · rename_i checked
      cases Option.some.inj accepted
      exact ⟨rfl, (Mettapedia.Machines.CausalReceipt.check_iff _ _).mp checked, rfl⟩
    · cases accepted

theorem graph?_truncated [DecidableEq Event] (boundary roots : List Event)
    (record : Prefix (Mettapedia.Machines.CausalEvent Event)) (lost : record.omitted ≠ 0) :
    graph? boundary roots record = none := by
  simp [graph?, complete?, lost]

/-- A complete graph readout requires both occurrence coverage and the
structural graph contract. Neither is inferred from the returned answer. -/
theorem initial_graph_iff [DecidableEq Event] (boundary roots : List Event)
    (capacity : Nat) (events : List (Mettapedia.Machines.CausalEvent Event)) :
    graph? boundary roots ((initial capacity).append events) = some ⟨roots, events⟩ ↔
      events.length ≤ capacity ∧ Mettapedia.Machines.CausalReceipt.WellFormed boundary
        ⟨roots, events⟩ := by
  constructor
  · intro accepted
    obtain ⟨complete, valid, _⟩ := graph?_sound boundary roots _ _ accepted
    exact ⟨(complete_iff capacity events).mp complete, valid⟩
  · rintro ⟨fits, valid⟩
    have complete := (complete_iff capacity events).mpr fits
    have checked := (Mettapedia.Machines.CausalReceipt.check_iff _ _).mpr valid
    simp [graph?, complete, checked]

end Prefix

/-- `none` is genuinely disabled; `some 0` records omissions from the first
selected occurrence. The two states have different observation contracts. -/
def initial (capacity : Option Nat) : Option (Prefix Event) :=
  capacity.map Prefix.initial

def accept (record : Option (Prefix Event)) (event : Unit → Event) : Option (Prefix Event) :=
  match record with
  | none => none
  | some record => some (record.push event)

theorem accept_map {NextEvent : Type*} (mapping : Event → NextEvent)
    (record : Option (Prefix Event)) (event : Unit → Event) :
    (accept record event).map (Prefix.map mapping) =
      accept (record.map (Prefix.map mapping)) (fun _ => mapping (event ())) := by
  cases record with
  | none => rfl
  | some record => simp only [accept, Option.map_some, Prefix.push_map]

def append (record : Option (Prefix Event)) (events : List Event) : Option (Prefix Event) :=
  record.map (fun retained => retained.append events)

@[simp] theorem append_nil (record : Option (Prefix Event)) : append record [] = record := by
  cases record <;> rfl

theorem append_cons (record : Option (Prefix Event)) (event : Event) (rest : List Event) :
    append record (event :: rest) = append (accept record (fun _ => event)) rest := by
  cases record <;> rfl

theorem append_append (record : Option (Prefix Event)) (first second : List Event) :
    append record (first ++ second) = append (append record first) second := by
  cases record with
  | none => rfl
  | some record => simp [append, Prefix.append_append]

def controller (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (capacity : Option Nat) : Controller Node Answer (Memory × Option (Prefix Event)) where
  initialMemory := (base.initialMemory, initial capacity)
  scheduler memory := base.scheduler memory.1
  advance memory node answer generated :=
    (base.advance memory.1 node answer generated,
      accept memory.2 (fun _ => observe memory.1 node answer generated))

abbrev erase (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    Snapshot Node Answer Memory := snapshot.mapMemory Prod.fst

/-- Transfer the original continuation and its existing bounded record.
Disabled recording stays disabled; payload transport does not replenish
capacity or hide an omitted occurrence. -/
def transferMemory {NextMemory NextEvent : Type*} (transfer : Memory → NextMemory)
    (mapping : Event → NextEvent) (memory : Memory × Option (Prefix Event)) :
    NextMemory × Option (Prefix NextEvent) :=
  (transfer memory.1, memory.2.map (Prefix.map mapping))

@[simp] theorem transferMemory_id (memory : Memory × Option (Prefix Event)) :
    transferMemory id id memory = memory := by
  rcases memory with ⟨memory, record⟩
  cases record <;> simp [transferMemory]

theorem transferMemory_comp {NextMemory FinalMemory NextEvent FinalEvent : Type*}
    (one : Memory → NextMemory) (two : NextMemory → FinalMemory)
    (first : Event → NextEvent) (second : NextEvent → FinalEvent)
    (memory : Memory × Option (Prefix Event)) :
    transferMemory two second (transferMemory one first memory) =
      transferMemory (two ∘ one) (second ∘ first) memory := by
  rcases memory with ⟨memory, record⟩
  cases record <;> simp [transferMemory, Prefix.map_comp, Function.comp_def]

/-- Erasing before or after transporting a recorded checkpoint gives the
same complete plain checkpoint. -/
theorem erase_mapState {NextNode NextMemory NextEvent : Type*}
    (mapping : Node → NextNode) (transfer : Memory → NextMemory)
    (payloadMap : Event → NextEvent)
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    erase (snapshot.mapState mapping (transferMemory transfer payloadMap)) =
      (erase snapshot).mapState mapping transfer := by
  cases snapshot
  rfl

section Transport

variable {NextNode NextMemory NextEvent : Type*}
    (mapping : Node → NextNode) (transfer : Memory → NextMemory)
    (payloadMap : Event → NextEvent)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer NextMemory)
    (observeSource : Memory → Node → Option Answer → List Node → Event)
    (observeTarget : NextMemory → NextNode → Option Answer → List NextNode → NextEvent)
    (emits : ∀ node, source.emit node = target.emit (mapping node))
    (successors : ∀ node,
      (source.successors node).map mapping = target.successors (mapping node))
    (reorders : ∀ memory nodes,
      ((first.scheduler memory).reorder nodes).map mapping =
        (second.scheduler (transfer memory)).reorder (nodes.map mapping))
    (integrates : ∀ memory pending generated,
      ((first.scheduler memory).integrate pending generated).map mapping =
        (second.scheduler (transfer memory)).integrate
          (pending.map mapping) (generated.map mapping))
    (advances : ∀ memory node emission generated,
      transfer (first.advance memory node emission generated) =
        second.advance (transfer memory) (mapping node) emission (generated.map mapping))
    (observations : ∀ memory node emission generated,
      payloadMap (observeSource memory node emission generated) =
        observeTarget (transfer memory) (mapping node) emission (generated.map mapping))

include advances observations in
theorem controller_advance_transfer (capacity : Option Nat)
    (memory : Memory × Option (Prefix Event)) (node : Node)
    (emission : Option Answer) (generated : List Node) :
    transferMemory transfer payloadMap
        ((controller first observeSource capacity).advance memory node emission generated) =
      (controller second observeTarget capacity).advance
        (transferMemory transfer payloadMap memory) (mapping node) emission
          (generated.map mapping) := by
  simp only [controller, transferMemory, accept_map, advances, observations]

include emits successors reorders integrates advances observations in
/-- The actual recording controllers commute with state transport. These
are local authority, scheduler, continuation and observation laws, rather
than an assumed equality between complete executions. -/
theorem tick_transport (capacity : Option Nat)
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    (Snapshot.tick source (controller first observeSource capacity) snapshot).mapState
        mapping (transferMemory transfer payloadMap) =
      Snapshot.tick target (controller second observeTarget capacity)
        (snapshot.mapState mapping (transferMemory transfer payloadMap)) := by
  apply Snapshot.tick_mapState mapping (transferMemory transfer payloadMap) source target
    (controller first observeSource capacity) (controller second observeTarget capacity)
    emits successors
  · intro memory nodes
    exact reorders memory.1 nodes
  · intro memory pending generated
    exact integrates memory.1 pending generated
  · exact controller_advance_transfer mapping transfer payloadMap first second
      observeSource observeTarget advances observations capacity

include emits successors reorders integrates advances observations in
/-- Every finite recorded prefix transports the whole frontier and both
continuations, including disabled, full and truncated recorder states. -/
theorem run_transport (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    (Snapshot.run source (controller first observeSource capacity) fuel snapshot).mapState
        mapping (transferMemory transfer payloadMap) =
      Snapshot.run target (controller second observeTarget capacity) fuel
        (snapshot.mapState mapping (transferMemory transfer payloadMap)) := by
  apply Snapshot.run_mapState mapping (transferMemory transfer payloadMap) source target
    (controller first observeSource capacity) (controller second observeTarget capacity)
    emits successors
  · intro memory nodes
    exact reorders memory.1 nodes
  · intro memory pending generated
    exact integrates memory.1 pending generated
  · exact controller_advance_transfer mapping transfer payloadMap first second
      observeSource observeTarget advances observations capacity

end Transport

/-- Recording is outside the scheduler's semantic memory. The entire
frontier and ordered emissions are preserved, not merely the final values. -/
theorem tick_erasure (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) (capacity : Option Nat)
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    erase (Snapshot.tick system (controller base observe capacity) snapshot) =
      Snapshot.tick system base (erase snapshot) := by
  cases snapshot with
  | mk search memory =>
      rcases memory with ⟨memory, record⟩
      simp only [Snapshot.tick, controller, erase, Snapshot.mapMemory]
      cases (base.scheduler memory).reorder search.frontier <;> rfl

theorem run_erasure (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) (capacity : Option Nat)
    (fuel : Nat) (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    erase (Snapshot.run system (controller base observe capacity) fuel snapshot) =
      Snapshot.run system base fuel (erase snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Snapshot.run, tick_erasure, ih]; rfl

/-- Independent reference observation of the original controller's next
selection. An exhausted frontier emits no recording request. -/
def next (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (snapshot : Snapshot Node Answer Memory) : Option Event :=
  ((base.scheduler snapshot.memory).reorder snapshot.search.frontier).head?.map
    (fun node => observe snapshot.memory node (system.emit node) (system.successors node))

/-- The complete finite observation stream is specified on the unrecorded
controller. It is not stored by a disabled or bounded recorder. -/
def stream (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) :
    Nat → Snapshot Node Answer Memory → List Event
  | 0, _ => []
  | fuel + 1, snapshot =>
      stream system base observe fuel snapshot ++
        (next system base observe (Snapshot.run system base fuel snapshot)).toList

theorem tick_record (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) (capacity : Option Nat)
    (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    (Snapshot.tick system (controller base observe capacity) snapshot).memory.2 =
      append snapshot.memory.2 (next system base observe (erase snapshot)).toList := by
  cases snapshot with
  | mk search memory =>
      rcases memory with ⟨memory, record⟩
      simp only [Snapshot.tick, controller, erase, Snapshot.mapMemory, next]
      cases (base.scheduler memory).reorder search.frontier with
      | nil => exact (append_nil record).symm
      | cons node rest =>
          simp only [List.head?_cons, Option.map_some, Option.toList_some]
          rw [append_cons, append_nil]

/-- The operational recorder retains exactly the declared bounded prefix
of an independently specified execution stream. -/
theorem run_record (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) (capacity : Option Nat)
    (fuel : Nat) (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    (Snapshot.run system (controller base observe capacity) fuel snapshot).memory.2 =
      append snapshot.memory.2 (stream system base observe fuel (erase snapshot)) := by
  induction fuel with
  | zero => exact (append_nil snapshot.memory.2).symm
  | succ fuel ih =>
      rw [Snapshot.run, tick_record, ih, run_erasure, stream, append_append]

theorem disabled_record (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    (Snapshot.run system (controller base observe none) fuel
      ⟨snapshot.search, (snapshot.memory, none)⟩).memory.2 = none := by
  rw [run_record]
  rfl

/-- The existing resumption law includes retained payloads, unused capacity
and omissions, together with the original complete search and controller. -/
theorem run_split (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event) (capacity : Option Nat)
    (first second : Nat) (snapshot : Snapshot Node Answer (Memory × Option (Prefix Event))) :
    Snapshot.run system (controller base observe capacity) (first + second) snapshot =
      Snapshot.run system (controller base observe capacity) second
        (Snapshot.run system (controller base observe capacity) first snapshot) :=
  Snapshot.run_add _ _ _ _ _

def start (snapshot : Snapshot Node Answer Memory) (capacity : Option Nat) :
    Snapshot Node Answer (Memory × Option (Prefix Event)) :=
  ⟨snapshot.search, (snapshot.memory, initial capacity)⟩

theorem start_mapState {NextNode NextMemory NextEvent : Type*}
    (mapping : Node → NextNode) (transfer : Memory → NextMemory)
    (payloadMap : Event → NextEvent) (snapshot : Snapshot Node Answer Memory)
    (capacity : Option Nat) :
    (start snapshot capacity).mapState mapping (transferMemory transfer payloadMap) =
      start (snapshot.mapState mapping transfer) capacity := by
  cases capacity <;> rfl

theorem retained_prefix (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).map Prefix.items =
        some ((stream system base observe fuel snapshot).take capacity) := by
  rw [run_record]
  simp [start, initial, append, erase, Snapshot.mapMemory, Prefix.initial_items]

theorem complete_record_iff (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).bind Prefix.complete? =
        some (stream system base observe fuel snapshot) ↔
      (stream system base observe fuel snapshot).length ≤ capacity := by
  rw [run_record]
  simpa only [start, initial, Option.map_some, erase, Snapshot.mapMemory,
    append, Option.bind_some] using
      Prefix.complete_iff capacity (stream system base observe fuel snapshot)


/-- Complete payload projection covers the independently specified original
controller stream, and every inner payload must have been decoded. -/
theorem complete_projection_iff (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (decode : Event → Option Payload) (capacity fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) (payloads : List Payload) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).bind (Prefix.project? decode) = some payloads ↔
      (stream system base observe fuel snapshot).length ≤ capacity ∧
        List.Forall₂ (fun event payload => decode event = some payload)
          (stream system base observe fuel snapshot) payloads := by
  rw [run_record]
  simpa only [start, initial, Option.map_some, erase, Snapshot.mapMemory,
    append, Option.bind_some] using
    Prefix.initial_project?_iff decode capacity (stream system base observe fuel snapshot) payloads

/-- Retained payload charge for the operational recorder. The charge must
account for any owner whose lifetime recording extends; this abstract bound
makes no assertion about a concrete allocator or physical byte counter. -/
theorem retained_charge_bound (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (charge : Event → Nat) (capacity perItem fuel : Nat)
    (snapshot : Snapshot Node Answer Memory)
    (bounded : ∀ event ∈ (stream system base observe fuel snapshot).take capacity,
      charge event ≤ perItem) (record : Prefix Event)
    (retained : (Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2 = some record) :
    (record.items.map charge).sum ≤ capacity * perItem := by
  have exactItems := retained_prefix system base observe capacity fuel snapshot
  rw [retained, Option.map_some, Option.some.injEq] at exactItems
  rw [exactItems]
  simpa only [Prefix.initial_items] using
    Prefix.retained_charge_bound charge capacity perItem
      (stream system base observe fuel snapshot) bounded

/-- The graph exported by the actual recorder covers the independently
specified controller stream, with its chosen scope and boundary identities. -/
theorem complete_graph_iff [DecidableEq Event] (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Mettapedia.Machines.CausalEvent Event)
    (boundary roots : List Event) (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).bind (Prefix.graph? boundary roots) =
        some ⟨roots, stream system base observe fuel snapshot⟩ ↔
      (stream system base observe fuel snapshot).length ≤ capacity ∧
        Mettapedia.Machines.CausalReceipt.WellFormed boundary
          ⟨roots, stream system base observe fuel snapshot⟩ := by
  rw [run_record]
  simpa only [start, initial, Option.map_some, erase, Snapshot.mapMemory,
    append, Option.bind_some] using
    Prefix.initial_graph_iff boundary roots capacity (stream system base observe fuel snapshot)

/-- A recorder's readout has exact occurrence coverage up to its capacity,
regardless of equality between payloads. No set or quotient is involved. -/
theorem recorded_requests (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (observe : Memory → Node → Option Answer → List Node → Event)
    (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).map
        (fun record => record.items.length + record.omitted) =
      some (stream system base observe fuel snapshot).length := by
  rw [run_record]
  simp [start, initial, append, erase, Snapshot.mapMemory, Prefix.request_account]

/-- Materialization is skipped when recording is disabled, independently
of the payload computation. This is a semantic demand fact, not an assertion
about the machine-code cost of a mode check. -/
theorem disabled_ignores_payload (first second : Unit → Event) :
    accept none first = accept none second := rfl

theorem node_stream_generated (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory) (fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) (roots : List Node)
    (sound : snapshot.search.Sound system roots) {node : Node}
    (member : node ∈ stream system base (fun _ selected _ _ => selected) fuel snapshot) :
    Generated system roots node := by
  induction fuel with
  | zero => simp [stream] at member
  | succ fuel ih =>
      rw [stream, List.mem_append] at member
      rcases member with earlier | selected
      · exact ih earlier
      · have runSound := Snapshot.sound_run system base sound fuel
        simp only [next, Option.mem_toList, Option.map_eq_some_iff] at selected
        obtain ⟨selectedNode, found, equal⟩ := selected
        subst node
        apply runSound.1 selectedNode
        apply (base.scheduler (Snapshot.run system base fuel snapshot).memory).mem_reorder_iff.mp
        exact List.mem_of_mem_head? found

/-- A retained selected node comes from the original inference system.
The retained prefix can be incomplete without granting spurious reachability. -/
theorem retained_node_generated (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory) (capacity fuel : Nat)
    (snapshot : Snapshot Node Answer Memory) (roots : List Node)
    (sound : snapshot.search.Sound system roots) (record : Prefix Node)
    (retained : (Snapshot.run system
      (controller base (fun _ selected _ _ => selected) (some capacity)) fuel
        (start snapshot (some capacity))).memory.2 = some record)
    {node : Node} (member : node ∈ record.items) : Generated system roots node := by
  have exactPrefix := retained_prefix system base (fun _ selected _ _ => selected)
    capacity fuel snapshot
  rw [retained, Option.map_some, Option.some.injEq] at exactPrefix
  rw [exactPrefix] at member
  exact node_stream_generated system base fuel snapshot roots sound
    (List.mem_of_mem_take member)

open Mettapedia.Machines

/-- Pure machine replay of each retained occurrence uses the same root,
machine and successor positions as execution. This is not permission to
repeat external effects or to claim completeness after truncation. -/
theorem retained_occurrence_replays {Term State Result : Type}
    (machine : OccurrenceMachineCore Term State Result)
    (base : Controller (WorkOccurrence State) (Result × List Nat) Memory)
    (initialState : State) (capacity fuel : Nat) (record : Prefix (WorkOccurrence State))
    (retained : (Snapshot.run (WorkOccurrence.system machine)
      (controller base (fun _ selected _ _ => selected) (some capacity)) fuel
        (start (Snapshot.initial base [WorkOccurrence.root initialState]) (some capacity))).memory.2 =
          some record)
    {occurrence : WorkOccurrence State} (member : occurrence ∈ record.items) :
    machine.follow initialState occurrence.trace = some occurrence.state := by
  apply WorkOccurrence.generated_valid machine
  exact retained_node_generated (WorkOccurrence.system machine) base capacity fuel
    (Snapshot.initial base [WorkOccurrence.root initialState]) [WorkOccurrence.root initialState]
    (BranchingTemporal.initial_sound _ _) record retained member

/-! ## Checked replay of complete captured expansions

The existing preparation capture is also a replay payload. Reconstruction
uses its recorded emission and ordered children, together with the captured
controller continuation. The authority check compares those observations with
the fixed branching system before accepting the reconstructed step. This is
pure replay; it grants no permission to repeat external effects.
-/

namespace Replay

def observe (_ : Memory) (node : Node) (emission : Option Answer) (generated : List Node) :
    Preparation.Capture Node Answer := ⟨node, emission, generated⟩

/-- Check the selected occurrence and its complete expansion before using
the recorded payload. Scheduler integration and memory updates still belong
to the captured controller. -/
def step? [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer) :
    Option (Snapshot Node Answer Memory) :=
  match (base.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | [] => none
  | node :: pending =>
      if frame = Preparation.capture system node then
        some {
          search := {
            events := snapshot.search.events ++
              frame.emission.toList.map (fun value => ⟨frame.input, value⟩)
            frontier := (base.scheduler snapshot.memory).integrate pending frame.generated }
          memory := base.advance snapshot.memory frame.input frame.emission frame.generated }
      else none

/-- An accepted reconstruction is the independently defined controller
step, including its ordered frontier, emissions and private continuation. -/
theorem step?_sound [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (snapshot result : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer)
    (accepted : step? system base snapshot frame = some result) :
    result = Snapshot.tick system base snapshot := by
  unfold step? at accepted
  cases order : (base.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | nil => simp [order] at accepted
  | cons node pending =>
      simp only [order] at accepted
      split at accepted
      · rename_i same
        subst frame
        cases Option.some.inj accepted
        simp only [Snapshot.tick, BranchingTemporal.tick, order, Preparation.capture]
        cases system.emit node <;> rfl
      · cases accepted

/-- Refusal retains the entire current checkpoint and every unconsumed
frame. The accepted prefix has already been reconstructed and is not reset. -/
def run [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory) :
    List (Preparation.Capture Node Answer) → Snapshot Node Answer Memory →
      Except (Snapshot Node Answer Memory × List (Preparation.Capture Node Answer))
        (Snapshot Node Answer Memory)
  | [], snapshot => .ok snapshot
  | frame :: rest, snapshot =>
      match step? system base snapshot frame with
      | none => .error (snapshot, frame :: rest)
      | some nextState => run system base rest nextState

/-- Joining recorded segments preserves the complete unconsumed suffix
on refusal as well as the complete checkpoint on success. -/
theorem run_append [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (first second : List (Preparation.Capture Node Answer))
    (snapshot : Snapshot Node Answer Memory) :
    run system base (first ++ second) snapshot =
      match run system base first snapshot with
      | .ok cut => run system base second cut
      | .error (cut, remaining) => .error (cut, remaining ++ second) := by
  induction first generalizing snapshot with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.cons_append, run]
      cases step? system base snapshot frame with
      | none => rfl
      | some nextState => exact ih nextState

/-- Every successful finite replay realizes that many actual expansions
from the supplied checkpoint. It does not infer an earlier initial state. -/
theorem run_sound [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (frames : List (Preparation.Capture Node Answer))
    (snapshot result : Snapshot Node Answer Memory)
    (accepted : run system base frames snapshot = .ok result) :
    result = Snapshot.run system base frames.length snapshot := by
  induction frames generalizing snapshot with
  | nil => exact (Except.ok.inj accepted).symm
  | cons frame rest ih =>
      simp only [run] at accepted
      cases stepped : step? system base snapshot frame with
      | none => simp [stepped] at accepted
      | some nextState =>
          have tail := ih nextState (by simpa only [stepped] using accepted)
          rw [step?_sound system base snapshot nextState frame stepped] at tail
          have splitRun := Snapshot.run_add system base 1 rest.length snapshot
          simpa only [List.length_cons, Nat.add_comm 1, Snapshot.run] using tail.trans splitRun.symm

/-- A refusal identifies an actual accepted prefix, its exact resulting
checkpoint, and the entire remaining suffix headed by the rejected frame. -/
theorem run_refused [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (frames pending : List (Preparation.Capture Node Answer))
    (snapshot cut : Snapshot Node Answer Memory)
    (refused : run system base frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Snapshot.run system base acceptedFrames.length snapshot ∧
      step? system base cut frame = none := by
  induction frames generalizing snapshot with
  | nil => cases refused
  | cons frame rest ih =>
      simp only [run] at refused
      cases stepped : step? system base snapshot frame with
      | none =>
          simp only [stepped] at refused
          cases Except.error.inj refused
          exact ⟨[], frame, rest, rfl, rfl, rfl, stepped⟩
      | some nextState =>
          obtain ⟨acceptedFrames, rejected, suffix, partition, remaining, state, invalid⟩ :=
            ih nextState (by simpa only [stepped] using refused)
          refine ⟨frame :: acceptedFrames, rejected, suffix, by simp [partition], remaining, ?_, invalid⟩
          rw [step?_sound system base snapshot nextState frame stepped] at state
          have splitRun := Snapshot.run_add system base 1 acceptedFrames.length snapshot
          simpa only [List.length_cons, Nat.add_comm 1, Snapshot.run] using state.trans splitRun.symm

/-- The next reference observation always replays, and an exhausted
frontier contributes no synthetic frame. -/
theorem run_next [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) :
    run system base (next system base observe snapshot).toList snapshot =
      .ok (Snapshot.tick system base snapshot) := by
  cases order : (base.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | nil =>
      simp [next, order, run, Snapshot.tick, BranchingTemporal.tick]
  | cons node pending =>
      simp only [next, List.head?_cons, Option.map_some, Option.toList_some,
        run, step?, order, observe, Preparation.capture, ↓reduceIte]
      simp only [Snapshot.tick, BranchingTemporal.tick, order]
      cases system.emit node <;> rfl

/-- Replaying the independently specified complete observation stream
recovers the whole controlled run, including a still-live residual. -/
theorem run_stream [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (fuel : Nat) (snapshot : Snapshot Node Answer Memory) :
    run system base (stream system base observe fuel snapshot) snapshot =
      .ok (Snapshot.run system base fuel snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [stream, run_append, ih]
      exact run_next system base _

/-- Truncation is a separate failure from a rejected replay frame. The
prefix object retains its omitted count, and a rejected frame retains the
complete checkpoint and unconsumed payloads. -/
def readout [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (record : Prefix (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory) :=
  record.complete?.map (fun frames => run system base frames snapshot)

theorem readout_truncated [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (record : Prefix (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory)
    (omitted : record.omitted ≠ 0) : readout system base record snapshot = none := by
  simp [readout, Prefix.complete?, omitted]

/-- This uses the actual bounded recorder, whose independent stream
correspondence was proved above. No completeness is inferred from answers. -/
theorem recorded_replay [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory)
    (fits : (stream system base observe fuel snapshot).length ≤ capacity) :
    ((Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).bind
        (fun record => readout system base record snapshot) =
      some (.ok (Snapshot.run system base fuel snapshot)) := by
  have complete := (complete_record_iff system base observe capacity fuel snapshot).mpr fits
  cases retained : (Snapshot.run system (controller base observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2 with
  | none => simp [retained] at complete
  | some record =>
      simp only [retained, Option.bind_some] at complete ⊢
      simp [readout, complete, run_stream]

/-- An accepted frame names the selected input and its whole authorized
expansion. Equal emitted answers alone do not supply this input evidence. -/
theorem step?_selected [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (snapshot result : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer)
    (accepted : step? system base snapshot frame = some result) :
    ∃ node pending, (base.scheduler snapshot.memory).reorder snapshot.search.frontier =
      node :: pending ∧ frame = Preparation.capture system node := by
  unfold step? at accepted
  cases ordered : (base.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | nil => simp [ordered] at accepted
  | cons node pending =>
      simp only [ordered] at accepted
      split at accepted
      · rename_i same
        exact ⟨node, pending, rfl, same⟩
      · cases accepted

theorem step?_capture [DecidableEq Node] [DecidableEq Answer]
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (snapshot : Snapshot Node Answer Memory) (node : Node) (pending : List Node)
    (selected : (base.scheduler snapshot.memory).reorder snapshot.search.frontier =
      node :: pending) :
    step? system base snapshot (Preparation.capture system node) =
      some (Snapshot.tick system base snapshot) := by
  simp only [step?, selected, ↓reduceIte, Snapshot.tick, BranchingTemporal.tick,
    Preparation.capture]
  cases system.emit node <;> rfl

/-- Transport both success and refusal through the same whole-state map.
A refusal carries its exact checkpoint and entire unconsumed frame suffix. -/
def mapResult {NextNode NextMemory : Type*} (mapping : Node → NextNode)
    (transfer : Memory → NextMemory)
    (result : Except (Snapshot Node Answer Memory × List (Preparation.Capture Node Answer))
      (Snapshot Node Answer Memory)) :
    Except (Snapshot NextNode Answer NextMemory × List (Preparation.Capture NextNode Answer))
      (Snapshot NextNode Answer NextMemory) :=
  match result with
  | .ok snapshot => .ok (snapshot.mapState mapping transfer)
  | .error (snapshot, remaining) =>
      .error (snapshot.mapState mapping transfer, remaining.map (Preparation.Capture.mapNodes mapping))

@[simp] theorem mapResult_id
    (result : Except (Snapshot Node Answer Memory × List (Preparation.Capture Node Answer))
      (Snapshot Node Answer Memory)) : mapResult id id result = result := by
  cases result with
  | ok snapshot => simp [mapResult]
  | error remaining =>
      rcases remaining with ⟨snapshot, frames⟩
      have identity : Preparation.Capture.mapNodes (Node := Node) (Answer := Answer) id = id := by
        funext frame
        exact Preparation.Capture.mapNodes_id frame
      simp [mapResult, identity]

theorem mapResult_comp {NextNode FinalNode NextMemory FinalMemory : Type*}
    (first : Node → NextNode) (second : NextNode → FinalNode)
    (one : Memory → NextMemory) (two : NextMemory → FinalMemory)
    (result : Except (Snapshot Node Answer Memory × List (Preparation.Capture Node Answer))
      (Snapshot Node Answer Memory)) :
    mapResult second two (mapResult first one result) =
      mapResult (second ∘ first) (two ∘ one) result := by
  cases result with
  | ok snapshot => simp only [mapResult, Snapshot.mapState_comp]
  | error remaining =>
      rcases remaining with ⟨snapshot, frames⟩
      simp [mapResult, Snapshot.mapState_comp, List.map_map,
        Preparation.Capture.mapNodes_comp, Function.comp_def]

section Translation

variable {NextNode NextMemory : Type*}
variable [DecidableEq Node] [DecidableEq NextNode] [DecidableEq Answer]
variable (mapping : Node → NextNode) (transfer : Memory → NextMemory)
variable (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
variable (first : Controller Node Answer Memory) (second : Controller NextNode Answer NextMemory)
variable (emits : ∀ node, source.emit node = target.emit (mapping node))
variable (successors : ∀ node,
  (source.successors node).map mapping = target.successors (mapping node))
variable (reorders : ∀ memory nodes,
  ((first.scheduler memory).reorder nodes).map mapping =
    (second.scheduler (transfer memory)).reorder (nodes.map mapping))
variable (integrates : ∀ memory pending generated,
  ((first.scheduler memory).integrate pending generated).map mapping =
    (second.scheduler (transfer memory)).integrate
      (pending.map mapping) (generated.map mapping))
variable (advances : ∀ memory node emission generated,
  transfer (first.advance memory node emission generated) =
    second.advance (transfer memory) (mapping node) emission (generated.map mapping))

include emits successors reorders integrates advances

/-- Forward replay preservation needs the local execution laws, but no
injectivity: an actually authenticated source frame remains authenticated. -/
theorem step?_accepted_mapState
    (snapshot result : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer)
    (accepted : step? source first snapshot frame = some result) :
    step? target second (snapshot.mapState mapping transfer) (frame.mapNodes mapping) =
      some (result.mapState mapping transfer) := by
  obtain ⟨node, pending, selected, same⟩ := step?_selected source first snapshot result frame accepted
  have targetSelected :
      (second.scheduler (transfer snapshot.memory)).reorder
        (snapshot.mapState mapping transfer).search.frontier = mapping node :: pending.map mapping := by
    change (second.scheduler (transfer snapshot.memory)).reorder
      (snapshot.search.frontier.map mapping) = _
    rw [← reorders, selected, List.map_cons]
  rw [same, Preparation.capture_mapNodes mapping source target emits successors,
    step?_sound source first snapshot result frame accepted]
  exact (step?_capture target second (snapshot.mapState mapping transfer) (mapping node)
    (pending.map mapping) targetSelected).trans
      (congrArg some (Snapshot.tick_mapState mapping transfer source target first second
        emits successors reorders integrates advances snapshot).symm)

/-- Injectivity of recorded input representations additionally reflects
refusal. A collapsed input can otherwise authenticate a different frame. -/
theorem step?_mapState (faithful : Function.Injective mapping)
    (snapshot : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer) :
    step? target second (snapshot.mapState mapping transfer) (frame.mapNodes mapping) =
      (step? source first snapshot frame).map (Snapshot.mapState mapping transfer) := by
  cases selected : (first.scheduler snapshot.memory).reorder snapshot.search.frontier with
  | nil =>
      have targetSelected :
          (second.scheduler (transfer snapshot.memory)).reorder
            (snapshot.mapState mapping transfer).search.frontier = [] := by
        change (second.scheduler (transfer snapshot.memory)).reorder
          (snapshot.search.frontier.map mapping) = _
        rw [← reorders, selected, List.map_nil]
      change (second.scheduler (transfer snapshot.memory)).reorder
        (snapshot.search.frontier.map mapping) = [] at targetSelected
      simp only [step?, Snapshot.mapState, Snapshot.mapNodes, Snapshot.mapMemory,
        BranchingTemporal.Snapshot.mapNodes, selected, targetSelected, Option.map_none]
  | cons node pending =>
      by_cases same : frame = Preparation.capture source node
      · have accepted : step? source first snapshot frame =
            some (Snapshot.tick source first snapshot) := by
          rw [same]
          exact step?_capture source first snapshot node pending selected
        rw [accepted, Option.map_some]
        exact step?_accepted_mapState mapping transfer source target first second emits successors
          reorders integrates advances snapshot _ frame accepted
      · have targetSelected :
            (second.scheduler (transfer snapshot.memory)).reorder
              (snapshot.mapState mapping transfer).search.frontier =
                mapping node :: pending.map mapping := by
          change (second.scheduler (transfer snapshot.memory)).reorder
            (snapshot.search.frontier.map mapping) = _
          rw [← reorders, selected, List.map_cons]
        have different : frame.mapNodes mapping ≠ Preparation.capture target (mapping node) := by
          intro equal
          apply same
          apply Preparation.Capture.mapNodes_injective mapping faithful
          exact equal.trans (Preparation.capture_mapNodes mapping source target emits successors node).symm
        change (second.scheduler (transfer snapshot.memory)).reorder
          (snapshot.search.frontier.map mapping) = mapping node :: pending.map mapping at targetSelected
        simp only [step?, Snapshot.mapState, Snapshot.mapNodes, Snapshot.mapMemory,
          BranchingTemporal.Snapshot.mapNodes, selected, targetSelected, same, different,
          ↓reduceIte, Option.map_none]

/-- Successful finite replay transports even through a noninjective
observation when the local execution and controller laws hold. -/
theorem run_accepted_mapState
    (frames : List (Preparation.Capture Node Answer)) (snapshot result : Snapshot Node Answer Memory)
    (accepted : run source first frames snapshot = .ok result) :
    run target second (frames.map (Preparation.Capture.mapNodes mapping))
      (snapshot.mapState mapping transfer) = .ok (result.mapState mapping transfer) := by
  induction frames generalizing snapshot with
  | nil =>
      cases Except.ok.inj accepted
      rfl
  | cons frame rest ih =>
      simp only [run] at accepted
      cases stepped : step? source first snapshot frame with
      | none => simp [stepped] at accepted
      | some nextState =>
          have targetStep := step?_accepted_mapState mapping transfer source target first second
            emits successors reorders integrates advances snapshot nextState frame stepped
          simp only [List.map_cons, run, targetStep]
          exact ih nextState (by simpa only [stepped] using accepted)

/-- Faithful translation commutes with the exact replay checker, including
the checkpoint and complete pending suffix at any rejected frame. -/
theorem run_mapState (faithful : Function.Injective mapping)
    (frames : List (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory) :
    run target second (frames.map (Preparation.Capture.mapNodes mapping))
      (snapshot.mapState mapping transfer) =
      mapResult mapping transfer (run source first frames snapshot) := by
  induction frames generalizing snapshot with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.map_cons, run,
        step?_mapState mapping transfer source target first second emits successors
          reorders integrates advances faithful]
      cases step? source first snapshot frame with
      | none => rfl
      | some nextState => exact ih nextState

/-- Bounded-record transport retains incomplete-recording refusal, and a
complete record obeys the same success/refusal state-translation law. -/
theorem readout_mapState (faithful : Function.Injective mapping)
    (record : Prefix (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory) :
    readout target second (record.map (Preparation.Capture.mapNodes mapping))
      (snapshot.mapState mapping transfer) =
      (readout source first record snapshot).map (mapResult mapping transfer) := by
  simp only [readout, Prefix.complete?_map, Option.map_map]
  cases record.complete? with
  | none => rfl
  | some frames =>
      simp only [Option.map_some]
      exact congrArg some (run_mapState mapping transfer source target first second emits
        successors reorders integrates advances faithful frames snapshot)

theorem step?_refused_iff (faithful : Function.Injective mapping)
    (snapshot : Snapshot Node Answer Memory) (frame : Preparation.Capture Node Answer) :
    step? target second (snapshot.mapState mapping transfer) (frame.mapNodes mapping) = none ↔
      step? source first snapshot frame = none := by
  rw [step?_mapState mapping transfer source target first second emits successors
    reorders integrates advances faithful]
  cases step? source first snapshot frame <;> simp

/-- No successful target replay of mapped frames can be invented at a
translated checkpoint. The source reconstruction remains available even
when the memory observation itself forgets information. -/
theorem run_success_reflected (faithful : Function.Injective mapping)
    (frames : List (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory)
    (result : Snapshot NextNode Answer NextMemory)
    (accepted : run target second (frames.map (Preparation.Capture.mapNodes mapping))
      (snapshot.mapState mapping transfer) = .ok result) :
    ∃ sourceResult, run source first frames snapshot = .ok sourceResult ∧
      result = sourceResult.mapState mapping transfer := by
  rw [run_mapState mapping transfer source target first second emits successors
    reorders integrates advances faithful] at accepted
  cases execution : run source first frames snapshot with
  | error remaining => simp [execution, mapResult] at accepted
  | ok sourceResult =>
      simp only [execution, mapResult] at accepted
      exact ⟨sourceResult, rfl, (Except.ok.inj accepted).symm⟩

/-- Target refusal reconstructs the precise source cut and remaining suffix;
there is no implication that a committed external effect has been undone. -/
theorem run_refusal_reflected (faithful : Function.Injective mapping)
    (frames : List (Preparation.Capture Node Answer)) (snapshot : Snapshot Node Answer Memory)
    (cut : Snapshot NextNode Answer NextMemory) (pending : List (Preparation.Capture NextNode Answer))
    (refused : run target second (frames.map (Preparation.Capture.mapNodes mapping))
      (snapshot.mapState mapping transfer) = .error (cut, pending)) :
    ∃ sourceCut sourcePending, run source first frames snapshot = .error (sourceCut, sourcePending) ∧
      cut = sourceCut.mapState mapping transfer ∧
      pending = sourcePending.map (Preparation.Capture.mapNodes mapping) := by
  rw [run_mapState mapping transfer source target first second emits successors
    reorders integrates advances faithful] at refused
  cases execution : run source first frames snapshot with
  | ok sourceResult => simp [execution, mapResult] at refused
  | error remaining =>
      rcases remaining with ⟨sourceCut, sourcePending⟩
      simp only [execution, mapResult] at refused
      have equal := (Except.error.inj refused).symm
      exact ⟨sourceCut, sourcePending, rfl, congrArg Prod.fst equal, congrArg Prod.snd equal⟩

/-- The existing bounded recorder supplies the source frames. Translation
preserves their completeness boundary and reconstructs the independently
defined target run under the same local execution laws. -/
theorem recorded_replay_mapState (faithful : Function.Injective mapping)
    (capacity fuel : Nat) (snapshot : Snapshot Node Answer Memory)
    (fits : (stream source first observe fuel snapshot).length ≤ capacity) :
    ((Snapshot.run source (controller first observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2).bind
        (fun record => readout target second (record.map (Preparation.Capture.mapNodes mapping))
          (snapshot.mapState mapping transfer)) =
      some (.ok (Snapshot.run target second fuel (snapshot.mapState mapping transfer))) := by
  have translated :
      ((Snapshot.run source (controller first observe (some capacity)) fuel
        (start snapshot (some capacity))).memory.2).bind
          (fun record => readout target second (record.map (Preparation.Capture.mapNodes mapping))
            (snapshot.mapState mapping transfer)) =
        (((Snapshot.run source (controller first observe (some capacity)) fuel
          (start snapshot (some capacity))).memory.2).bind
            (fun record => readout source first record snapshot)).map (mapResult mapping transfer) := by
    cases (Snapshot.run source (controller first observe (some capacity)) fuel
      (start snapshot (some capacity))).memory.2 with
    | none => rfl
    | some record =>
        exact readout_mapState mapping transfer source target first second emits successors
          reorders integrates advances faithful record snapshot
  rw [translated, recorded_replay source first capacity fuel snapshot fits]
  simp only [Option.map_some, mapResult,
    Snapshot.run_mapState mapping transfer source target first second emits successors
      reorders integrates advances]

end Translation

end Replay

namespace Controls

private abbrev TestNode := WorkOccurrence OccurrenceMachineCore.DuplicateExampleState
private abbrev TestAnswer := Nat × List Nat

private def base : Controller TestNode TestAnswer Unit := Controller.fixed Scheduler.breadthFirst
private def system := WorkOccurrence.system OccurrenceMachineCore.duplicateExample
private def observe (_ : Unit) (node : TestNode) (_ : Option TestAnswer) (_ : List TestNode) := node
private def point : Snapshot TestNode TestAnswer Unit :=
  Snapshot.initial base [WorkOccurrence.root .root]
private def execute (capacity : Option Nat) (fuel : Nat) :=
  Snapshot.run system (controller base observe capacity) fuel (start point capacity)

theorem duplicate_occurrences_remain_distinct :
    ((execute (some 3) 3).memory.2).map
      (fun record => record.items.map WorkOccurrence.trace) = some [[], [0], [1]] ∧
    (execute (some 3) 3).search.events.map Emission.value = [(7, [0]), (7, [1])] := by
  exact ⟨rfl, rfl⟩

theorem truncation_preserves_complete_search :
    (execute (some 1) 3).search = (Snapshot.run system base 3 point).search ∧
      ((execute (some 1) 3).memory.2).map
        (fun record => (record.items.map WorkOccurrence.trace, record.omitted)) =
          some ([[]], 2) ∧
      ((execute (some 1) 3).memory.2).bind Prefix.complete? = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem resume_retains_prefix_and_omissions :
    Snapshot.run system (controller base observe (some 1)) 2 (execute (some 1) 1) =
      execute (some 1) 3 := by
  exact (run_split system base observe (some 1) 1 2 (start point (some 1))).symm

theorem disabled_and_zero_capacity_differ :
    (execute none 3).memory.2 = none ∧
      ((execute (some 0) 3).memory.2).map Prefix.omitted = some 3 ∧
      (execute none 3).search = (execute (some 0) 3).search := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal retained prefixes can hide different amounts of computation.
An incomplete recording cannot explain the complete observed run by itself. -/
theorem retained_items_do_not_determine_completion :
    ((execute (some 1) 1).memory.2).map Prefix.items =
      ((execute (some 1) 3).memory.2).map Prefix.items ∧
      (execute (some 1) 1).search.frontier ≠ [] ∧
      (execute (some 1) 3).search.frontier = [] := by
  exact ⟨rfl, by decide, rfl⟩

theorem resetting_recorder_on_resume_loses_prefix :
    let cut := execute (some 3) 1
    let reset : Snapshot TestNode TestAnswer (Unit × Option (Prefix TestNode)) :=
      ⟨cut.search, (cut.memory.1, initial (some 3))⟩
    (Snapshot.run system (controller base observe (some 3)) 2 reset).memory.2 ≠
      (execute (some 3) 3).memory.2 := by
  decide

theorem completion_creates_no_recording_requests :
    execute (some 3) 7 = execute (some 3) 3 := by
  rfl

private def graphObserve (_ : Unit) (node : TestNode) (_ : Option TestAnswer) (_ : List TestNode) :
    CausalEvent (List Nat) :=
  ⟨node.trace, if node.trace.isEmpty then [] else [node.trace.dropLast]⟩

private def graphExecute (capacity fuel : Nat) :=
  Snapshot.run system (controller base graphObserve (some capacity)) fuel
    (start point (some capacity))

theorem complete_graph_keeps_duplicate_answer_occurrences :
    ((graphExecute 3 3).memory.2).bind (Prefix.graph? [] [[0], [1]]) =
      some ⟨[[0], [1]], [⟨[], []⟩, ⟨[0], [[]]⟩, ⟨[1], [[]]⟩]⟩ := by
  decide

theorem truncated_graph_does_not_certify_complete_run :
    (graphExecute 1 3).search = (graphExecute 3 3).search ∧
      ((graphExecute 1 3).memory.2).bind (Prefix.graph? [] [[0], [1]]) = none := by
  exact ⟨rfl, rfl⟩

theorem late_graph_needs_captured_boundary :
    let suffix : List (CausalEvent (List Nat)) := [⟨[0], [[]]⟩, ⟨[1], [[]]⟩]
    let recorded := (Prefix.initial 2).append suffix
    Prefix.graph? [[]] [[0], [1]] recorded = some ⟨[[0], [1]], suffix⟩ ∧
      Prefix.graph? [] [[0], [1]] recorded = none := by
  decide

private def captureExecute (capacity fuel : Nat) :=
  Snapshot.run system (controller base Replay.observe (some capacity)) fuel
    (start point (some capacity))

/-- Replay recovers two answer occurrences with the same payload, together
with the exact exhausted frontier. -/
theorem replay_preserves_duplicate_occurrences :
    ((captureExecute 3 3).memory.2).bind (fun record => Replay.readout system base record point) =
      some (.ok (Snapshot.run system base 3 point)) ∧
    (Snapshot.run system base 3 point).search.events.map Emission.value =
      [(7, [0]), (7, [1])] := by
  exact ⟨Replay.recorded_replay system base 3 3 point (by decide), rfl⟩

/-- A complete recording of a finite prefix may reconstruct an open run.
Replay completeness and search completion are different observations. -/
theorem replay_preserves_open_residual :
    ((captureExecute 2 2).memory.2).bind (fun record => Replay.readout system base record point) =
      some (.ok (Snapshot.run system base 2 point)) ∧
    ((Snapshot.run system base 2 point).search.frontier.map WorkOccurrence.trace) = [[1]] := by
  exact ⟨Replay.recorded_replay system base 2 2 point (by decide), rfl⟩

private def firstCapture : Preparation.Capture TestNode TestAnswer :=
  Preparation.capture system (WorkOccurrence.root .root)
private def secondCapture : Preparation.Capture TestNode TestAnswer :=
  Preparation.capture system ⟨.done, [0]⟩
private def thirdCapture : Preparation.Capture TestNode TestAnswer :=
  Preparation.capture system ⟨.done, [1]⟩
private def changedCapture : Preparation.Capture TestNode TestAnswer :=
  { secondCapture with emission := some (99, [0]) }

theorem replay_refusal_keeps_checkpoint_and_suffix :
    Replay.run system base [firstCapture, changedCapture, thirdCapture] point =
      .error (Snapshot.run system base 1 point, [changedCapture, thirdCapture]) := by
  rfl

theorem replay_does_not_exchange_equal_answer_occurrences :
    Replay.run system base [firstCapture, thirdCapture, secondCapture] point =
      .error (Snapshot.run system base 1 point, [thirdCapture, secondCapture]) := by
  rfl

private def changedSystem : BranchingSystem TestNode TestAnswer :=
  { system with successors := fun _ => [] }

theorem replay_changed_authority_refused :
    Replay.run changedSystem base [firstCapture, secondCapture, thirdCapture] point =
      .error (point, [firstCapture, secondCapture, thirdCapture]) := by
  rfl

theorem truncated_record_does_not_replay_complete_search :
    ((captureExecute 1 3).memory.2).bind (fun record => Replay.readout system base record point) =
      none ∧ (captureExecute 1 3).search.frontier = [] := by
  exact ⟨rfl, rfl⟩

private def switchingController : Controller TestNode TestAnswer Nat where
  initialMemory := 0
  scheduler count := if count = 0 then Scheduler.breadthFirst else Scheduler.reverseBreadthFirst
  advance count _ _ _ := count + 1

private def switchingPoint : Snapshot TestNode TestAnswer Nat :=
  Snapshot.initial switchingController [WorkOccurrence.root .root]

/-- Controller memory changes the second selected occurrence. Both the
selection order and the final continuation survive recording and replay. -/
theorem replay_recovers_controller_memory :
    ((Snapshot.run system (controller switchingController Replay.observe (some 3)) 3
      (start switchingPoint (some 3))).memory.2).bind
        (fun record => Replay.readout system switchingController record switchingPoint) =
      some (.ok (Snapshot.run system switchingController 3 switchingPoint)) ∧
    (Snapshot.run system switchingController 3 switchingPoint).memory = 3 ∧
    (Snapshot.run system switchingController 3 switchingPoint).search.events.map Emission.value =
      [(7, [1]), (7, [0])] := by
  exact ⟨Replay.recorded_replay system switchingController 3 3 switchingPoint (by decide), rfl, rfl⟩

theorem replay_wrong_controller_refused :
    Replay.run system switchingController [firstCapture, secondCapture, thirdCapture]
      switchingPoint =
      .error (Snapshot.run system switchingController 1 switchingPoint,
        [secondCapture, thirdCapture]) := by
  rfl

theorem replay_missing_occurrence_refused :
    Replay.run system base [firstCapture, thirdCapture] point =
      .error (Snapshot.run system base 1 point, [thirdCapture]) := by
  rfl

theorem replay_duplicated_occurrence_refused :
    Replay.run system base [firstCapture, secondCapture, secondCapture, thirdCapture] point =
      .error (Snapshot.run system base 2 point, [secondCapture, thirdCapture]) := by
  rfl

theorem late_recording_requires_its_captured_checkpoint :
    let cut := Snapshot.run system base 1 point
    let record := (Prefix.initial 2).append [secondCapture, thirdCapture]
    Replay.readout system base record cut = some (.ok (Snapshot.run system base 3 point)) ∧
      Replay.readout system base record point =
        some (.error (point, [secondCapture, thirdCapture])) := by
  exact ⟨rfl, rfl⟩

namespace Translation

private inductive RelocatedNode where
  | word : Nat → RelocatedNode
  | external
deriving DecidableEq, Repr

private def relocate (node : Nat) : RelocatedNode := .word (node + 10)
private def transfer (memory : Nat) : Nat × Nat := (memory, memory + 4)

private def source : BranchingSystem Nat Nat where
  emit node := if node = 1 ∨ node = 2 then some 7 else none
  successors node := if node = 0 then [1, 2] else []

/-- An independent target authority with an explicit extra behavior outside
the translated image. No target operation is defined by invoking the source. -/
private def target : BranchingSystem RelocatedNode Nat where
  emit
    | .word index => if index = 11 ∨ index = 12 then some 7 else none
    | .external => some 99
  successors
    | .word index => if index = 10 then [.word 11, .word 12] else []
    | .external => []

private def first : Controller Nat Nat Nat where
  initialMemory := 0
  scheduler memory := if memory % 2 = 0 then Scheduler.breadthFirst else Scheduler.reverseBreadthFirst
  advance memory _ _ _ := memory + 1

private def second : Controller RelocatedNode Nat (Nat × Nat) where
  initialMemory := (0, 4)
  scheduler memory := if memory.1 % 2 = 0 then Scheduler.breadthFirst else Scheduler.reverseBreadthFirst
  advance memory _ _ _ := (memory.1 + 1, memory.2 + 1)

private theorem relocate_injective : Function.Injective relocate := by
  intro one two equal
  have indices := RelocatedNode.word.inj equal
  omega

private theorem emits (node : Nat) : source.emit node = target.emit (relocate node) := by
  have one : node + 10 = 11 ↔ node = 1 := by omega
  have two : node + 10 = 12 ↔ node = 2 := by omega
  simp [source, target, relocate, one, two]

private theorem successors (node : Nat) :
    (source.successors node).map relocate = target.successors (relocate node) := by
  by_cases zero : node = 0 <;> simp [source, target, relocate, zero]

private theorem reorders (memory : Nat) (nodes : List Nat) :
    ((first.scheduler memory).reorder nodes).map relocate =
      (second.scheduler (transfer memory)).reorder (nodes.map relocate) := by
  by_cases even : memory % 2 = 0 <;>
    simp [first, second, transfer, even, Scheduler.breadthFirst,
      Scheduler.reverseBreadthFirst, List.map_reverse]

private theorem integrates (memory : Nat) (pending generated : List Nat) :
    ((first.scheduler memory).integrate pending generated).map relocate =
      (second.scheduler (transfer memory)).integrate
        (pending.map relocate) (generated.map relocate) := by
  by_cases even : memory % 2 = 0 <;>
    simp [first, second, transfer, even, Scheduler.breadthFirst, Scheduler.reverseBreadthFirst]

private theorem advances (memory node : Nat) (emission : Option Nat) (generated : List Nat) :
    transfer (first.advance memory node emission generated) =
      second.advance (transfer memory) (relocate node) emission (generated.map relocate) := by
  change (memory + 1, memory + 1 + 4) = (memory + 1, memory + 4 + 1)
  rfl

private def point : Snapshot Nat Nat Nat := Snapshot.initial first [0]
private def frames : List (Preparation.Capture Nat Nat) :=
  [Preparation.capture source 0, Preparation.capture source 2, Preparation.capture source 1]

private theorem observations (memory node : Nat) (emission : Option Nat)
    (generated : List Nat) :
    (Replay.observe memory node emission generated).mapNodes relocate =
      Replay.observe (transfer memory) (relocate node) emission (generated.map relocate) := by
  rfl

/-- Transport compares the actual two recording controllers at every fuel
and capacity. The target independently chooses its own selected occurrences
and updates its two-component continuation. -/
theorem relocated_recording_law (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Nat Nat Nat) :
    (Snapshot.run source (controller first Replay.observe capacity) fuel
      (start snapshot capacity)).mapState relocate
        (transferMemory transfer (Preparation.Capture.mapNodes relocate)) =
      Snapshot.run target (controller second Replay.observe capacity) fuel
        (start (snapshot.mapState relocate transfer) capacity) := by
  rw [run_transport relocate transfer (Preparation.Capture.mapNodes relocate)
    source target first second Replay.observe Replay.observe emits successors reorders
      integrates advances observations, start_mapState]

theorem relocated_recording_erasure (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Nat Nat Nat) :
    erase ((Snapshot.run source (controller first Replay.observe capacity) fuel
      (start snapshot capacity)).mapState relocate
        (transferMemory transfer (Preparation.Capture.mapNodes relocate))) =
      Snapshot.run target second fuel (snapshot.mapState relocate transfer) := by
  rw [erase_mapState, run_erasure, Snapshot.run_mapState relocate transfer source target
    first second emits successors reorders integrates advances]
  rfl

theorem relocation_retains_disabled_and_zero_capacity_status :
    (Snapshot.run target (controller second Replay.observe none) 3
      (start (point.mapState relocate transfer) none)).memory.2 = none ∧
    (Snapshot.run target (controller second Replay.observe (some 0)) 3
      (start (point.mapState relocate transfer) (some 0))).memory.2 =
        some ⟨[], 0, 3⟩ := by
  exact ⟨rfl, rfl⟩

theorem relocation_retains_prefix_and_omissions :
    (Snapshot.run target (controller second Replay.observe (some 1)) 3
      (start (point.mapState relocate transfer) (some 1))).memory.2 =
        some ⟨[Preparation.capture target (.word 10)], 0, 2⟩ ∧
    (Snapshot.run target (controller second Replay.observe (some 1)) 3
      (start (point.mapState relocate transfer) (some 1))).search =
        ⟨[⟨.word 12, 7⟩, ⟨.word 11, 7⟩], []⟩ := by
  exact ⟨rfl, rfl⟩

/-- Literal target operations satisfy the general translation law for every
source checkpoint and every supplied frame sequence, not just this fixture. -/
theorem relocated_replay_law (recorded : List (Preparation.Capture Nat Nat))
    (snapshot : Snapshot Nat Nat Nat) :
    Replay.run target second (recorded.map (Preparation.Capture.mapNodes relocate))
      (snapshot.mapState relocate transfer) =
      Replay.mapResult relocate transfer (Replay.run source first recorded snapshot) :=
  Replay.run_mapState relocate transfer source target first second emits successors reorders
    integrates advances relocate_injective recorded snapshot

theorem relocated_replay_preserves_occurrences_and_memory :
    Replay.run target second (frames.map (Preparation.Capture.mapNodes relocate))
      (point.mapState relocate transfer) =
      .ok ⟨⟨[⟨.word 12, 7⟩, ⟨.word 11, 7⟩], []⟩, (3, 7)⟩ := by
  rw [relocated_replay_law]
  rfl

theorem relocated_open_replay_preserves_complete_residual :
    Replay.run target second ((frames.take 2).map (Preparation.Capture.mapNodes relocate))
      (point.mapState relocate transfer) =
      .ok ⟨⟨[⟨.word 12, 7⟩], [.word 11]⟩, (2, 6)⟩ := by
  rw [relocated_replay_law]
  rfl

theorem relocated_wrong_order_keeps_checkpoint_and_suffix :
    let wrong := [Preparation.capture source 0, Preparation.capture source 1,
      Preparation.capture source 2]
    Replay.run target second (wrong.map (Preparation.Capture.mapNodes relocate))
      (point.mapState relocate transfer) =
      .error (⟨⟨[], [.word 11, .word 12]⟩, (1, 5)⟩,
        [Preparation.capture target (.word 11), Preparation.capture target (.word 12)]) := by
  dsimp only
  rw [relocated_replay_law]
  rfl

theorem relocated_actual_recorder_replays :
    ((Snapshot.run source (controller first Replay.observe (some 3)) 3
      (start point (some 3))).memory.2).bind
        (fun record => Replay.readout target second
          (record.map (Preparation.Capture.mapNodes relocate)) (point.mapState relocate transfer)) =
      some (.ok (Snapshot.run target second 3 (point.mapState relocate transfer))) :=
  Replay.recorded_replay_mapState relocate transfer source target first second emits successors
    reorders integrates advances relocate_injective 3 3 point (by decide)

theorem relocation_does_not_complete_a_truncated_record :
    ((Snapshot.run source (controller first Replay.observe (some 1)) 3
      (start point (some 1))).memory.2).bind
        (fun record => Replay.readout target second
          (record.map (Preparation.Capture.mapNodes relocate)) (point.mapState relocate transfer)) = none := by
  rfl

/-- Reflection is restricted to translated checkpoints. Arbitrary target
states may have behavior that the source authority does not authorize. -/
theorem target_behavior_outside_image_is_not_source_behavior :
    target.emit .external = some 99 ∧ ∀ node, source.emit node ≠ some 99 := by
  constructor
  · rfl
  · intro node
    simp [source]

private def twinSource : BranchingSystem Bool Nat where
  emit _ := some 7
  successors _ := []

private def collapsedTarget : BranchingSystem Nat Nat where
  emit _ := some 7
  successors _ := []

private def twins : Controller Bool Nat Unit := Controller.fixed Scheduler.breadthFirst
private def collapsed : Controller Nat Nat Unit := Controller.fixed Scheduler.breadthFirst
private def collapse (_ : Bool) : Nat := 0
private def twinPoint : Snapshot Bool Nat Unit := Snapshot.initial twins [false]

theorem collapsed_input_preserves_forward_steps (snapshot : Snapshot Bool Nat Unit) :
    (Snapshot.tick twinSource twins snapshot).mapState collapse id =
      Snapshot.tick collapsedTarget collapsed (snapshot.mapState collapse id) := by
  apply Snapshot.tick_mapState collapse id twinSource collapsedTarget twins collapsed
  · intro node; rfl
  · intro node; rfl
  · intro memory nodes; rfl
  · intro memory pending generated
    simp [twins, collapsed, Controller.fixed, Scheduler.breadthFirst, List.map_append]
  · intro memory node emission generated; rfl

/-- All forward local laws hold above, but the collapsed input accepts a
forged occurrence. This discriminates the injectivity premise of reflection. -/
theorem collapsed_input_accepts_a_refused_source_frame :
    let wrong := Preparation.capture twinSource true
    Replay.step? twinSource twins twinPoint wrong = none ∧
      Replay.step? collapsedTarget collapsed (twinPoint.mapState collapse id)
        (wrong.mapNodes collapse) = some ⟨⟨[⟨0, 7⟩], []⟩, ()⟩ := by
  exact ⟨rfl, rfl⟩

end Translation

private def payloadGraph : CausalReceipt Nat := ⟨[1], [⟨1, []⟩]⟩
private def payloadEntries : List (Nat × Option (CausalReceipt Nat)) :=
  [(10, some payloadGraph), (11, some payloadGraph)]
private def payloadDecode (entry : Nat × Option (CausalReceipt Nat)) :
    Option (Nat × CausalReceipt Nat) := do
  let payload ← entry.2
  if payload.check [] then some (entry.1, payload) else none

theorem equal_graphs_keep_occurrences :
    Prefix.project? payloadDecode ((Prefix.initial 2).append payloadEntries) =
      some [(10, payloadGraph), (11, payloadGraph)] ∧
      (10 : Nat) ≠ 11 := by decide

theorem inner_refusal_is_not_complete :
    let events : List (Nat × Option (CausalReceipt Nat)) := [(10, some payloadGraph), (11, none)]
    let record := (Prefix.initial 2).append events
    record.complete? = some events ∧ Prefix.project? payloadDecode record = none ∧
      events.filterMap payloadDecode = [(10, payloadGraph)] := by decide

theorem outer_truncation_is_not_complete :
    Prefix.project? payloadDecode ((Prefix.initial 1).append payloadEntries) = none := by decide

/-- One retained entry can have arbitrarily large payload charge. -/
theorem item_bound_does_not_bound_payload (bound : Nat) :
    let record := (Prefix.initial 1 : Prefix Nat).append [bound + 1]
    record.items.length = 1 ∧ bound < (record.items.map id).sum := by
  exact ⟨rfl, Nat.lt_succ_self bound⟩

/-- Structural failure inside a retained graph also refuses the whole
projection. It does not become an absent answer occurrence. -/
theorem invalid_inner_graph_is_not_complete :
    let malformed : CausalReceipt Nat := ⟨[1], []⟩
    let events : List (Nat × Option (CausalReceipt Nat)) :=
      [(10, some payloadGraph), (11, some malformed)]
    let record := (Prefix.initial 2).append events
    record.complete? = some events ∧ Prefix.project? payloadDecode record = none := by decide

private def partialGraph (node : TestNode) : Option (List Nat × CausalReceipt Nat) :=
  if node.trace = [0] then none else some (node.trace, payloadGraph)

/-- Refusing one inner graph leaves both equal-valued answer occurrences
and the original complete search unchanged. -/
theorem inner_refusal_preserves_complete_search :
    (execute (some 3) 3).search = (Snapshot.run system base 3 point).search ∧
      (execute (some 3) 3).search.events.map Emission.value = [(7, [0]), (7, [1])] ∧
      ((execute (some 3) 3).memory.2).bind (Prefix.project? partialGraph) = none := by
  exact ⟨rfl, rfl, rfl⟩

end Controls

#print axioms Prefix.append_state
#print axioms Prefix.complete_iff
#print axioms Prefix.request_account
#print axioms Prefix.project?_iff
#print axioms Prefix.project?_length
#print axioms Prefix.project?_truncated
#print axioms Prefix.project?_refused
#print axioms Prefix.project?_keys
#print axioms Prefix.initial_project?_iff
#print axioms Prefix.retained_charge_bound
#print axioms complete_projection_iff
#print axioms retained_charge_bound
#print axioms Controls.equal_graphs_keep_occurrences
#print axioms Controls.inner_refusal_is_not_complete
#print axioms Controls.outer_truncation_is_not_complete
#print axioms Controls.item_bound_does_not_bound_payload
#print axioms Controls.invalid_inner_graph_is_not_complete
#print axioms Controls.inner_refusal_preserves_complete_search
#print axioms Prefix.graph?_sound
#print axioms Prefix.graph?_truncated
#print axioms Prefix.initial_graph_iff
#print axioms tick_erasure
#print axioms run_erasure
#print axioms run_record
#print axioms disabled_record
#print axioms run_split
#print axioms retained_prefix
#print axioms complete_record_iff
#print axioms complete_graph_iff
#print axioms recorded_requests
#print axioms retained_occurrence_replays
#print axioms Replay.step?_sound
#print axioms Replay.run_append
#print axioms Replay.run_sound
#print axioms Replay.run_refused
#print axioms Replay.run_next
#print axioms Replay.run_stream
#print axioms Replay.readout_truncated
#print axioms Replay.recorded_replay
#print axioms Controls.replay_preserves_duplicate_occurrences
#print axioms Controls.replay_preserves_open_residual
#print axioms Controls.replay_refusal_keeps_checkpoint_and_suffix
#print axioms Controls.replay_does_not_exchange_equal_answer_occurrences
#print axioms Controls.replay_changed_authority_refused
#print axioms Controls.truncated_record_does_not_replay_complete_search
#print axioms Controls.replay_recovers_controller_memory
#print axioms Controls.replay_wrong_controller_refused
#print axioms Controls.replay_missing_occurrence_refused
#print axioms Controls.replay_duplicated_occurrence_refused
#print axioms Controls.late_recording_requires_its_captured_checkpoint
#print axioms Controls.duplicate_occurrences_remain_distinct
#print axioms Controls.truncation_preserves_complete_search
#print axioms Controls.resume_retains_prefix_and_omissions
#print axioms Controls.disabled_and_zero_capacity_differ
#print axioms Controls.retained_items_do_not_determine_completion
#print axioms Controls.resetting_recorder_on_resume_loses_prefix
#print axioms Controls.completion_creates_no_recording_requests
#print axioms Controls.complete_graph_keeps_duplicate_answer_occurrences
#print axioms Controls.truncated_graph_does_not_certify_complete_run
#print axioms Controls.late_graph_needs_captured_boundary
#print axioms Prefix.map_id
#print axioms Prefix.map_comp
#print axioms Prefix.items_map
#print axioms Prefix.push_map
#print axioms Prefix.complete?_map
#print axioms accept_map
#print axioms transferMemory_id
#print axioms transferMemory_comp
#print axioms erase_mapState
#print axioms controller_advance_transfer
#print axioms tick_transport
#print axioms run_transport
#print axioms start_mapState
#print axioms Replay.step?_selected
#print axioms Replay.step?_capture
#print axioms Replay.mapResult_id
#print axioms Replay.mapResult_comp
#print axioms Replay.step?_accepted_mapState
#print axioms Replay.step?_mapState
#print axioms Replay.run_accepted_mapState
#print axioms Replay.run_mapState
#print axioms Replay.readout_mapState
#print axioms Replay.step?_refused_iff
#print axioms Replay.run_success_reflected
#print axioms Replay.run_refusal_reflected
#print axioms Replay.recorded_replay_mapState
#print axioms Controls.Translation.relocated_recording_law
#print axioms Controls.Translation.relocated_recording_erasure
#print axioms Controls.Translation.relocation_retains_disabled_and_zero_capacity_status
#print axioms Controls.Translation.relocation_retains_prefix_and_omissions
#print axioms Controls.Translation.relocated_replay_law
#print axioms Controls.Translation.relocated_replay_preserves_occurrences_and_memory
#print axioms Controls.Translation.relocated_open_replay_preserves_complete_residual
#print axioms Controls.Translation.relocated_wrong_order_keeps_checkpoint_and_suffix
#print axioms Controls.Translation.relocated_actual_recorder_replays
#print axioms Controls.Translation.relocation_does_not_complete_a_truncated_record
#print axioms Controls.Translation.target_behavior_outside_image_is_not_source_behavior
#print axioms Controls.Translation.collapsed_input_preserves_forward_steps
#print axioms Controls.Translation.collapsed_input_accepts_a_refused_source_frame

end Mettapedia.GSLT.Core.InferenceControl.Recording
