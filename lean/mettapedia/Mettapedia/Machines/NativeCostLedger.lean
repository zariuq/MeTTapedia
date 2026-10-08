import Mettapedia.Algebra.RunLengthEvents
import Mettapedia.Algebra.WorkSpan
import Mettapedia.Algebra.ParallelCrossover
import Mettapedia.Algebra.OccurrenceIdentity
import Mettapedia.Machines.VariableInventory
import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Core.InferenceRecording
import Mathlib.Data.BitVec

/-!
# Cumulative native event receipts

The `native-events-v1` profile counts named representation operations. Its units
do not measure arithmetic bit complexity, memory bytes or elapsed time. Event
identity, origin scope and work occurrence remain in the chronological receipt.
Run-length encoding retains all three; total work is a separate additive view.

This is a mathematical model of the receipt representation and its valuation.
Extraction of authentic evaluator events, bounded identity allocation and C
memory ownership have additional correspondence obligations. A sequential
work/span readout is labelled as such: it is not a parallel dependency span.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeCostLedger

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics.IndexedEventValuation

inductive Kind where
  | quantum | candidateRow | indexVisit | matchAttempt | matchNode
  | heapLookup | heapIndexVisit | heapUpdate | receiptAppend | bindingClone
  | queueInsert | queueTake | queueVisit | queueMove | capture | restore
  | frameAllocate | frameRetire | publish | coefficientAppend | coefficientMultiply
  | costRead | analysisStep | workerDispatch | workerJoin | commitCheck | equationActivation
  | storageProbe | coefficientHandle
  deriving DecidableEq, Repr

instance : Fintype Kind where
  elems := {.quantum, .candidateRow, .indexVisit, .matchAttempt, .matchNode,
    .heapLookup, .heapIndexVisit, .heapUpdate, .receiptAppend, .bindingClone,
    .queueInsert, .queueTake, .queueVisit, .queueMove, .capture, .restore,
    .frameAllocate, .frameRetire, .publish, .coefficientAppend, .coefficientMultiply,
    .costRead, .analysisStep, .workerDispatch, .workerJoin, .commitCheck, .equationActivation,
    .storageProbe, .coefficientHandle}
  complete := by intro kind; cases kind <;> simp

structure Payload where
  origin : Nat
  occurrence : Nat
  kind : Kind
  units : Nat
  deriving DecidableEq, Repr

abbrev Event := RunLengthEvents.Event Payload
abbrev Run := RunLengthEvents.Run Payload
abbrev Ledger := List Run
abbrev Totals := (Kind → Nat) × Nat

def eventGrade (event : Event) : Totals :=
  (fun kind => if event.2.kind = kind then event.2.units else 0, event.2.units)

def totals (events : List Event) : Totals := (events.map eventGrade).sum

def snapshot (ledger : Ledger) : Totals := totals (RunLengthEvents.expand ledger)

/-- Cost and ordered evidence are independent valuations of the same events. -/
abbrev receiptValuation : Valuation Event :=
  (additive eventGrade).prod (chronological id)

theorem receiptValuation_exact (events : List Event) :
    receiptValuation.historyGrade events = some (totals events, events) := by
  rw [Valuation.prod_historyGrade, additive_historyGrade, chronological_historyGrade]
  simp [totals]

theorem totals_append (first second : List Event) :
    totals (first ++ second) = totals first + totals second := by
  simp [totals, List.sum_append]

theorem snapshot_append (first second : Ledger) :
    snapshot (first ++ second) = snapshot first + snapshot second := by
  rw [snapshot, RunLengthEvents.expand_append, totals_append]
  rfl

/-- Every run is charged once per represented physical event, not once per run. -/
theorem single_run_snapshot (run : Run) :
    snapshot [run] = run.repetitions • eventGrade (run.firstIdentity, run.payload) := by
  simp only [snapshot, RunLengthEvents.expand, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, totals]
  exact RunLengthEvents.Run.sum_payload
    (fun payload => (fun kind => if payload.kind = kind then payload.units else 0, payload.units)) run

/-- The compressed receipt has the same totals as its full chronological history. -/
theorem snapshot_compressed (ledger : Ledger) :
    snapshot ledger =
      (ledger.map fun run => run.repetitions •
        eventGrade (run.firstIdentity, run.payload)).sum := by
  induction ledger with
  | nil => rfl
  | cons run rest ih =>
      change snapshot ([run] ++ rest) = _
      rw [snapshot_append, single_run_snapshot, ih]
      rfl

/-- Appending a new execution event retains all prior expenditure. -/
theorem snapshot_append_event (maximum : Nat) (ledger : Ledger) (event : Event) :
    snapshot (RunLengthEvents.appendEvent maximum ledger event) =
      snapshot ledger + eventGrade event := by
  rw [snapshot, RunLengthEvents.expand_appendEvent, totals_append]
  simp [totals, snapshot]

theorem count_le_work (events : List Event) (kind : Kind) :
    (totals events).1 kind ≤ (totals events).2 := by
  induction events with
  | nil => simp [totals]
  | cons event rest ih =>
      change (eventGrade event + totals rest).1 kind ≤ (eventGrade event + totals rest).2
      dsimp [eventGrade]
      split_ifs <;> omega

/-- The profile's total work is exactly the sum of its named counters. -/
theorem counters_sum_eq_work (events : List Event) :
    (∑ kind : Kind, (totals events).1 kind) = (totals events).2 := by
  induction events with
  | nil => simp [totals]
  | cons event rest ih =>
      change (∑ kind : Kind, (eventGrade event + totals rest).1 kind) =
        (eventGrade event + totals rest).2
      simp [eventGrade, Finset.sum_add_distrib, ih]

def identities (ledger : Ledger) : List Nat :=
  (RunLengthEvents.expand ledger).map Prod.fst

def Unique (ledger : Ledger) : Prop := (identities ledger).Nodup

/-- All retained identities belong to earlier successful reservations in
the same namespace. The frontier survives suspension along with the ledger. -/
def BelowCounter (ledger : Ledger) (current : Nat) : Prop :=
  ∀ identity ∈ identities ledger, identity < current

theorem belowCounter_mono (ledger : Ledger) (first second : Nat)
    (bounded : BelowCounter ledger first) (advanced : first ≤ second) :
    BelowCounter ledger second := by
  intro identity present
  exact (bounded identity present).trans_le advanced

/-- Freshness follows from the allocator frontier, rather than from an
independent assumption about a new event. This concerns a completed successful
reservation; a refused identity does not produce a complete event receipt. -/
theorem reserved_identity_fresh (maximum current identity : Nat) (ledger : Ledger)
    (bounded : BelowCounter ledger current)
    (granted : (OccurrenceIdentity.reserve maximum current).1 = some identity) :
    identity ∉ identities ledger := by
  have full : OccurrenceIdentity.reserve maximum current =
      (some identity, (OccurrenceIdentity.reserve maximum current).2) := by rw [← granted]
  have same := (OccurrenceIdentity.reserve_issued_iff _ _ _ _).mp full |>.2.2.1
  intro present
  have earlier := bounded identity present
  omega

theorem belowCounter_append (maximum current after : Nat) (ledger : Ledger) (event : Event)
    (bounded : BelowCounter ledger current) (advanced : current ≤ after)
    (newBelow : event.1 < after) :
    BelowCounter (RunLengthEvents.appendEvent maximum ledger event) after := by
  intro identity present
  change identity ∈ (RunLengthEvents.expand
    (RunLengthEvents.appendEvent maximum ledger event)).map Prod.fst at present
  rw [RunLengthEvents.expand_appendEvent, List.map_append, List.map_singleton] at present
  rcases List.mem_append.mp present with previous | added
  · exact (bounded identity previous).trans_le advanced
  · have same := List.mem_singleton.mp added
    exact same ▸ newBelow

/-- A fresh physical identity preserves the one-charge-per-event invariant. -/
theorem unique_append_event (maximum : Nat) (ledger : Ledger) (event : Event)
    (unique : Unique ledger) (fresh : event.1 ∉ identities ledger) :
    Unique (RunLengthEvents.appendEvent maximum ledger event) := by
  change ((RunLengthEvents.expand
    (RunLengthEvents.appendEvent maximum ledger event)).map Prod.fst).Nodup
  rw [RunLengthEvents.expand_appendEvent, List.map_append, List.map_singleton,
    List.nodup_append]
  refine ⟨unique, by simp, ?_⟩
  intro first present second singleton equal
  have secondIdentity : second = event.1 := List.mem_singleton.mp singleton
  exact fresh ((equal.trans secondIdentity) ▸ present)

/-- Live ledger locations in an inner-to-outer scope chain. Locations are
distinct from event-origin identities: an exhausted identity allocator does
not make two live ledger locations the same. Null observations are omitted. -/
def scopeTargets (scopes : List (Option Nat)) : List Nat :=
  (VariableInventory.firstOccurrences []
    ((scopes.filterMap id).map fun location => (location, ()))).map Prod.fst

theorem scopeTargets_mem (scopes : List (Option Nat)) (location : Nat) :
    location ∈ scopeTargets scopes ↔ some location ∈ scopes := by
  rw [scopeTargets, VariableInventory.mem_firstOccurrences_keys]
  simp

theorem scopeTargets_unique (scopes : List (Option Nat)) : (scopeTargets scopes).Nodup :=
  VariableInventory.firstOccurrences_keys_nodup _ _

/-- The runtime-style scan compares every frame with the full preceding
prefix, including disabled observations and discarded duplicate frames.
Null destinations perform no append. This is a finite chain observation;
the validity and lifetime of physical linked frames are separate premises. -/
def prefixScopeTargets (scopes : List (Option Nat)) : List Nat :=
  (VariableInventory.presentEntries
    (VariableInventory.firstByPrefix [] (scopes.map fun location => (location, ())))).map Prod.fst

/-- The full-prefix scan and the independent live-key inventory select
exactly the same ordered destinations, including repeated null frames. -/
theorem prefixScopeTargets_correspondence (scopes : List (Option Nat)) :
    prefixScopeTargets scopes = scopeTargets scopes := by
  rw [prefixScopeTargets, VariableInventory.firstByPrefix_correspondence,
    VariableInventory.presentEntries_firstOccurrences]
  simp [scopeTargets, VariableInventory.presentEntries,
    List.filterMap_map, List.map_filterMap]

/-- Deliver one physical event to an ordered list of ledger locations.
Each update is the ordinary run-length append, with its whole prior history.
The list is not assumed unique by the construction. -/
def deliver (maximum : Nat) (event : Event) :
    List Nat → (Nat → Ledger) → Nat → Ledger
  | [], store => store
  | location :: rest, store => deliver maximum event rest
      (fun candidate => if candidate = location then
        RunLengthEvents.appendEvent maximum (store candidate) event else store candidate)

theorem deliver_eq_updateKeys (maximum : Nat) (event : Event) (locations : List Nat)
    (store : Nat → Ledger) :
    deliver maximum event locations store =
      VariableInventory.updateKeys (fun _ ledger => RunLengthEvents.appendEvent maximum ledger event)
        locations store := by
  induction locations generalizing store with
  | nil => rfl
  | cons location rest ih =>
      rw [deliver, VariableInventory.updateKeys, ih]
      congr 1
      funext candidate
      by_cases same : candidate = location <;> simp [same]

/-- Unique destinations append exactly once to each containing ledger and
leave every other ledger intact. This is a whole-history statement. -/
theorem deliver_unique_at (maximum : Nat) (event : Event) (locations : List Nat)
    (store : Nat → Ledger) (unique : locations.Nodup) (location : Nat) :
    deliver maximum event locations store location =
      if location ∈ locations then RunLengthEvents.appendEvent maximum (store location) event
      else store location := by
  rw [deliver_eq_updateKeys]
  exact VariableInventory.updateKeys_unique_at _ _ _ unique location

/-- An observed operation is propagated once to each distinct containing
observation. Re-entering a ledger does not create another physical event. -/
def chargeScopes (maximum : Nat) (scopes : List (Option Nat)) (event : Event)
    (store : Nat → Ledger) : Nat → Ledger :=
  deliver maximum event (scopeTargets scopes) store

theorem chargeScopes_at (maximum : Nat) (scopes : List (Option Nat)) (event : Event)
    (store : Nat → Ledger) (location : Nat) :
    chargeScopes maximum scopes event store location =
      if some location ∈ scopes then RunLengthEvents.appendEvent maximum (store location) event
      else store location := by
  rw [chargeScopes, deliver_unique_at _ _ _ _ (scopeTargets_unique scopes)]
  simp only [scopeTargets_mem]

/-- No active observation means no receipt construction or history change.
The event argument describes the mathematical operation; this construction
does not require allocating its representation in an unobserved execution. -/
theorem chargeScopes_disabled (maximum : Nat) (event : Event) (store : Nat → Ledger) :
    chargeScopes maximum [] event store = store := rfl

/-- Every containing ledger retains exactly the same new physical identity,
origin and work occurrence, together with its own preceding chronology. -/
theorem chargeScopes_history (maximum : Nat) (scopes : List (Option Nat)) (event : Event)
    (store : Nat → Ledger) (location : Nat) (present : some location ∈ scopes) :
    RunLengthEvents.expand (chargeScopes maximum scopes event store location) =
      RunLengthEvents.expand (store location) ++ [event] := by
  rw [chargeScopes_at, if_pos present, RunLengthEvents.expand_appendEvent]

/-- A containing view charges only the new event, even when the same view
occurs repeatedly in the dynamic scope chain. -/
theorem chargeScopes_snapshot (maximum : Nat) (scopes : List (Option Nat)) (event : Event)
    (store : Nat → Ledger) (location : Nat) (present : some location ∈ scopes) :
    snapshot (chargeScopes maximum scopes event store location) =
      snapshot (store location) + eventGrade event := by
  rw [chargeScopes_at, if_pos present]
  exact snapshot_append_event _ _ _

/-- Freshness is required only in ledgers receiving the event. This keeps
each observation's physical-identity invariant without merging those views. -/
theorem chargeScopes_preserves_unique (maximum : Nat) (scopes : List (Option Nat))
    (event : Event) (store : Nat → Ledger) (location : Nat)
    (unique : Unique (store location))
    (fresh : some location ∈ scopes → event.1 ∉ identities (store location)) :
    Unique (chargeScopes maximum scopes event store location) := by
  rw [chargeScopes_at]
  split
  · rename_i present
    exact unique_append_event maximum _ _ unique (fresh present)
  · exact unique

/-- One successful reservation supplies all containing views with the same
fresh physical identity. Receipt destinations are live locations, so this law
does not depend on the separate origin-identity namespace being available.
The atomic ABI and authentic event-production obligations remain separate. -/
theorem chargeScopes_reserved_invariant (runMaximum identityMaximum current identity : Nat)
    (scopes : List (Option Nat)) (payload : Payload) (store : Nat → Ledger)
    (unique : ∀ location, Unique (store location))
    (bounded : ∀ location, BelowCounter (store location) current)
    (granted : (OccurrenceIdentity.reserve identityMaximum current).1 = some identity) :
    ∀ location,
      Unique (chargeScopes runMaximum scopes (identity, payload) store location) ∧
      BelowCounter (chargeScopes runMaximum scopes (identity, payload) store location)
        (OccurrenceIdentity.reserve identityMaximum current).2 := by
  intro location
  constructor
  · exact chargeScopes_preserves_unique _ _ _ _ _ (unique location)
      (fun _ => reserved_identity_fresh _ _ _ _ (bounded location) granted)
  · rw [chargeScopes_at]
    split
    · exact belowCounter_append _ _ _ _ _ (bounded location)
        (OccurrenceIdentity.reserve_monotone _ _)
        (OccurrenceIdentity.reserve_identity_bounds _ _ _ granted).2.1
    · exact belowCounter_mono _ _ _ (bounded location)
        (OccurrenceIdentity.reserve_monotone _ _)

/-- A successful weak-CAS attempt supplies the ordinary scoped-charge
invariant. Freshness is derived from the attempt's executable comparison,
including its actual shared counter, rather than assumed for a completed
reservation. Physical ledger publication and the atomic ABI remain separate. -/
theorem chargeScopes_weakReservation_invariant {Caller : Type*} [DecidableEq Caller]
    (runMaximum identityMaximum : Nat)
    (state : OccurrenceIdentity.WeakReservation.State Caller)
    (request : OccurrenceIdentity.WeakReservation.Request Caller)
    (caller : Caller) (identity : Nat) (scopes : List (Option Nat))
    (payload : Payload) (store : Nat → Ledger)
    (unique : ∀ location, Unique (store location))
    (bounded : ∀ location, BelowCounter (store location) state.counter)
    (issued : (OccurrenceIdentity.WeakReservation.step identityMaximum state request).2 =
      some (caller, identity)) :
    ∀ location,
      Unique (chargeScopes runMaximum scopes (identity, payload) store location) ∧
      BelowCounter (chargeScopes runMaximum scopes (identity, payload) store location)
        (OccurrenceIdentity.WeakReservation.step identityMaximum state request).1.counter := by
  obtain ⟨_, advanced, reservation⟩ :=
    OccurrenceIdentity.WeakReservation.issued_linearizes
      identityMaximum state request caller identity issued
  have granted : (OccurrenceIdentity.reserve identityMaximum state.counter).1 =
      some identity := congrArg Prod.fst reservation
  have next : (OccurrenceIdentity.reserve identityMaximum state.counter).2 =
      identity + 1 := congrArg Prod.snd reservation
  rw [advanced, ← next]
  exact chargeScopes_reserved_invariant runMaximum identityMaximum
    state.counter identity scopes payload store unique bounded granted

/-- An observation of successful reservations, delivered in their actual
issuance order. The list is the protocol's mathematical observation, not
extra runtime receipt storage. Each invocation carries its captured scopes
and payload; unsuccessful attempts produce no entry to deliver. -/
def recordReservations {Caller : Type*} (maximum : Nat)
    (scopes : Caller → List (Option Nat)) (payload : Caller → Payload) :
    List (Caller × Nat) → (Nat → Ledger) → Nat → Ledger
  | [], store => store
  | (caller, identity) :: rest, store =>
      recordReservations maximum scopes payload rest
        (chargeScopes maximum (scopes caller) (identity, payload caller) store)

/-- Every containing view receives exactly the successful physical events,
in chronological order, after its complete inherited history. -/
theorem recordReservations_history {Caller : Type*} (maximum : Nat)
    (scopes : Caller → List (Option Nat)) (payload : Caller → Payload)
    (issued : List (Caller × Nat)) (store : Nat → Ledger) (location : Nat) :
    RunLengthEvents.expand
        (recordReservations maximum scopes payload issued store location) =
      RunLengthEvents.expand (store location) ++
        issued.filterMap (fun reservation =>
          if some location ∈ scopes reservation.1 then
            some (reservation.2, payload reservation.1) else none) := by
  induction issued generalizing store with
  | nil => simp [recordReservations]
  | cons reservation rest ih =>
      rcases reservation with ⟨caller, identity⟩
      rw [recordReservations, ih, chargeScopes_at]
      by_cases present : some location ∈ scopes caller
      · simp [present, RunLengthEvents.expand_appendEvent, List.append_assoc]
      · simp [present]

/-- Splitting receipt observation preserves each live ledger's full prior
chronology. This concerns observation order; physical publication requires
its own ownership and synchronization correspondence. -/
theorem recordReservations_append {Caller : Type*} (maximum : Nat)
    (scopes : Caller → List (Option Nat)) (payload : Caller → Payload)
    (first second : List (Caller × Nat)) (store : Nat → Ledger) :
    recordReservations maximum scopes payload (first ++ second) store =
      recordReservations maximum scopes payload second
        (recordReservations maximum scopes payload first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons reservation rest ih =>
      rcases reservation with ⟨caller, identity⟩
      exact ih _

/-- All interleaved attempts preserve freshness and one charge per physical
identity in every ledger. Lost comparisons and spurious failures may delay
issuance, but neither emits a repeated identity or changes receipt history. -/
theorem recordReservations_weakRun_invariant {Caller : Type*} [DecidableEq Caller]
    (runMaximum identityMaximum : Nat)
    (scopes : Caller → List (Option Nat)) (payload : Caller → Payload)
    (requests : List (OccurrenceIdentity.WeakReservation.Request Caller))
    (state : OccurrenceIdentity.WeakReservation.State Caller) (store : Nat → Ledger)
    (unique : ∀ location, Unique (store location))
    (bounded : ∀ location, BelowCounter (store location) state.counter) :
    ∀ location,
      Unique (recordReservations runMaximum scopes payload
        (OccurrenceIdentity.WeakReservation.run identityMaximum requests state).2 store location) ∧
      BelowCounter (recordReservations runMaximum scopes payload
        (OccurrenceIdentity.WeakReservation.run identityMaximum requests state).2 store location)
        (OccurrenceIdentity.WeakReservation.run identityMaximum requests state).1.counter := by
  induction requests generalizing state store with
  | nil => exact fun location => ⟨unique location, bounded location⟩
  | cons request rest ih =>
      cases emitted : (OccurrenceIdentity.WeakReservation.step identityMaximum state request).2 with
      | none =>
          have retained : ∀ location, BelowCounter (store location)
              (OccurrenceIdentity.WeakReservation.step identityMaximum state request).1.counter :=
            fun location => belowCounter_mono _ _ _ (bounded location)
              (OccurrenceIdentity.WeakReservation.counter_monotone _ _ _)
          simpa only [OccurrenceIdentity.WeakReservation.run, emitted,
            Option.toList_none, List.nil_append] using ih _ store unique retained
      | some reservation =>
          rcases reservation with ⟨caller, identity⟩
          have charged := chargeScopes_weakReservation_invariant runMaximum identityMaximum
            state request caller identity (scopes caller) (payload caller) store unique bounded emitted
          simpa only [OccurrenceIdentity.WeakReservation.run, emitted,
            Option.toList_some, List.singleton_append, recordReservations] using
            ih _ (chargeScopes runMaximum (scopes caller) (identity, payload caller) store)
              (fun location => (charged location).1) (fun location => (charged location).2)

/-- Two contenders issue two events despite reading the same initial value.
Repeated scope entry charges each containing view only once; a losing and a
spurious attempt contribute no receipt. -/
theorem weak_reservation_scope_control :
    let scopes : Fin 3 → List (Option Nat) := fun _ => [some 4, none, some 4]
    let payload : Fin 3 → Payload := fun caller => ⟨12, caller.val, .publish, 1⟩
    let store : Nat → Ledger := fun _ => []
    let issued := (OccurrenceIdentity.WeakReservation.run 7
      OccurrenceIdentity.WeakReservation.Controls.contested
      (OccurrenceIdentity.WeakReservation.initial 5)).2
    RunLengthEvents.expand (recordReservations 255 scopes payload issued store 4) =
      [(5, ⟨12, 0, .publish, 1⟩), (6, ⟨12, 1, .publish, 1⟩)] ∧
      recordReservations 255 scopes payload issued store 9 = [] := by
  decide

/-- Disabled scopes and a repeated containing scope leave two distinct
views with one copy of the same new physical occurrence. -/
theorem repeated_scope_control :
    let event : Event := (8, ⟨12, 30, .heapLookup, 1⟩)
    let store : Nat → Ledger := fun _ => []
    RunLengthEvents.expand (chargeScopes 255 [some 4, some 9, none, some 4] event store 4) =
      [event] ∧
    RunLengthEvents.expand (chargeScopes 255 [some 4, some 9, none, some 4] event store 9) =
      [event] ∧
    chargeScopes 255 [some 4, some 9, none, some 4] event store 5 = [] := by
  decide

/-- Omitting destination deduplication changes both chronology and work.
Re-entering a destination does not justify charging one execution twice. -/
theorem repeated_destination_double_charges :
    let event : Event := (8, ⟨12, 30, .heapLookup, 1⟩)
    let store : Nat → Ledger := fun _ => []
    (snapshot (deliver 255 event [4, 4] store 4)).2 = 2 ∧
      (snapshot (chargeScopes 255 [some 4, some 4] event store 4)).2 = 1 := by
  decide

def readEvent (identity origin occurrence : Nat) : Event :=
  (identity, ⟨origin, occurrence, .costRead, 1⟩)

/-- Inspection returns the preceding snapshot and then records its own event. -/
def inspect (maximum : Nat) (ledger : Ledger) (identity origin occurrence : Nat) :
    Totals × Ledger :=
  (snapshot ledger, RunLengthEvents.appendEvent maximum ledger (readEvent identity origin occurrence))

theorem inspect_preceding (maximum : Nat) (ledger : Ledger)
    (identity origin occurrence : Nat) :
    (inspect maximum ledger identity origin occurrence).1 = snapshot ledger := rfl

theorem inspect_charged (maximum : Nat) (ledger : Ledger)
    (identity origin occurrence : Nat) :
    snapshot (inspect maximum ledger identity origin occurrence).2 =
      snapshot ledger + eventGrade (readEvent identity origin occurrence) :=
  snapshot_append_event maximum ledger _

theorem inspect_work (maximum : Nat) (ledger : Ledger)
    (identity origin occurrence : Nat) :
    (snapshot (inspect maximum ledger identity origin occurrence).2).2 =
      (snapshot ledger).2 + 1 := by
  rw [inspect_charged]
  rfl

/-- Saturation of a machine counter is a lower bound on the mathematical total. -/
def boundedTotal (maximum value : Nat) : Nat := min maximum value

theorem boundedTotal_lower_bound (maximum value : Nat) :
    boundedTotal maximum value ≤ value := Nat.min_le_right _ _

theorem boundedTotal_exact_iff (maximum value : Nat) :
    boundedTotal maximum value = value ↔ value ≤ maximum := by
  simp [boundedTotal]

/-- Repeated saturated additions are the saturation of the accumulated total. -/
theorem boundedTotal_add (maximum first second : Nat) :
    boundedTotal maximum (boundedTotal maximum first + second) =
      boundedTotal maximum (first + second) := by
  dsimp [boundedTotal]
  omega

/-- The runtime overflow branch returns the bound rather than wrapping. -/
def addLowerBound (maximum left right : Nat) : Nat × Bool :=
  if right > maximum - left then (maximum, true) else (left + right, false)

theorem addLowerBound_value (maximum left right : Nat) (leftFits : left ≤ maximum) :
    (addLowerBound maximum left right).1 = boundedTotal maximum (left + right) := by
  simp only [addLowerBound]
  split <;> dsimp [boundedTotal] <;> omega

theorem addLowerBound_overflow (maximum left right : Nat) (leftFits : left ≤ maximum) :
    (addLowerBound maximum left right).2 = true ↔ maximum < left + right := by
  by_cases overflow : maximum < left + right
  · have guard : right > maximum - left := by omega
    simp [addLowerBound, guard, overflow]
  · have guard : ¬right > maximum - left := by omega
    simp [addLowerBound, guard, overflow]

/-- Unsigned counter addition with a sticky overflow flag. The subtraction is
performed before addition, so a successful branch cannot wrap. -/
def wordAddLowerBound {width : Nat} (left right : BitVec width)
    (previousOverflow : Bool) : BitVec width × Bool :=
  if right > BitVec.allOnes width - left then (BitVec.allOnes width, true)
  else (left + right, previousOverflow)

/-- The independent bit-vector implementation agrees with mathematical
saturation at every width, including the runtime's 64-bit profile. This is an
unsigned primitive correspondence; source extraction and memory ownership
remain separate obligations. -/
theorem wordAddLowerBound_correspondence {width : Nat} (left right : BitVec width)
    (previousOverflow : Bool) :
    let result := wordAddLowerBound left right previousOverflow
    (result.1.toNat, result.2) =
      ((addLowerBound (2 ^ width - 1) left.toNat right.toNat).1,
        previousOverflow || (addLowerBound (2 ^ width - 1) left.toNat right.toNat).2) := by
  have leftFits : left.toNat ≤ 2 ^ width - 1 := by
    have bound := left.isLt
    omega
  have subtractExact : (BitVec.allOnes width - left).toNat =
      2 ^ width - 1 - left.toNat := by
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_allOnes]
      exact leftFits), BitVec.toNat_allOnes]
  have guard : right > BitVec.allOnes width - left ↔
      right.toNat > 2 ^ width - 1 - left.toNat := by
    change BitVec.allOnes width - left < right ↔ _
    rw [BitVec.lt_def, subtractExact]
  by_cases overflow : right.toNat > 2 ^ width - 1 - left.toNat
  · simp [wordAddLowerBound, guard.mpr overflow, addLowerBound, overflow]
  · have fits : left.toNat + right.toNat < 2 ^ width := by
      have positive := Nat.two_pow_pos width
      omega
    simp [wordAddLowerBound, not_congr guard |>.mpr overflow, addLowerBound,
      overflow, BitVec.toNat_add_of_lt fits]

/-- The counter's numerical readout is mathematical saturation. This
projection keeps the word width symbolic, including at concrete clients. -/
theorem wordAddLowerBound_value {width : Nat} (left right : BitVec width)
    (previousOverflow : Bool) :
    (wordAddLowerBound left right previousOverflow).1.toNat =
      (addLowerBound (2 ^ width - 1) left.toNat right.toNat).1 :=
  congrArg (fun pair : Nat × Bool => pair.1)
    (wordAddLowerBound_correspondence left right previousOverflow)

/-- The flag's readout retains prior overflow and records any new overflow.
The numerical counter and Boolean flag have separate projection laws. -/
theorem wordAddLowerBound_flag {width : Nat} (left right : BitVec width)
    (previousOverflow : Bool) :
    (wordAddLowerBound left right previousOverflow).2 =
      (previousOverflow || (addLowerBound (2 ^ width - 1) left.toNat right.toNat).2) :=
  congrArg (fun pair : Nat × Bool => pair.2)
    (wordAddLowerBound_correspondence left right previousOverflow)

/-- Adding no work leaves both the unsigned total and its inherited flag
unchanged. The fact holds at every word width. -/
theorem word_add_zero {width : Nat} (left : BitVec width) (previousOverflow : Bool) :
    wordAddLowerBound left 0 previousOverflow = (left, previousOverflow) := by
  have noOverflow : ¬ (0 : BitVec width) > BitVec.allOnes width - left := by
    change ¬ BitVec.allOnes width - left < (0 : BitVec width)
    have zeroRead : (0 : BitVec width).toNat = 0 := by
      change (0#width).toNat = 0
      exact BitVec.toNat_zero
    rw [BitVec.lt_def, zeroRead]
    exact Nat.not_lt_zero _
  simp only [wordAddLowerBound, if_neg noOverflow]
  exact congrArg (fun value : BitVec width => (value, previousOverflow)) (add_zero left)

/-- Exactly reaching the largest representable value is still exact. An
inherited overflow flag is retained, but equality does not introduce one. -/
theorem word_exact_maximum {width : Nat} (previousOverflow : Bool) :
    wordAddLowerBound (0 : BitVec width) (BitVec.allOnes width) previousOverflow =
      (BitVec.allOnes width, previousOverflow) := by
  simp [wordAddLowerBound]

/-- A previous overflow cannot be erased by a later small increment. -/
theorem word_overflow_is_sticky {width : Nat} (left right : BitVec width) :
    (wordAddLowerBound left right true).2 = true := by
  unfold wordAddLowerBound
  split <;> rfl

/-- Repeated calls to the unsigned counter primitive. The inherited flag is
part of the accumulator, including when execution resumes with more events. -/
def wordAccumulate {width : Nat} (current : BitVec width) (overflow : Bool) :
    List (BitVec width) → BitVec width × Bool
  | [] => (current, overflow)
  | increment :: rest =>
      let next := wordAddLowerBound current increment overflow
      wordAccumulate next.1 next.2 rest

/-- Numerical saturation is applied to the whole cumulative sum, regardless
of the number of primitive calls used to accumulate it. -/
theorem wordAccumulate_value {width : Nat} (current : BitVec width)
    (overflow : Bool) (increments : List (BitVec width)) :
    (wordAccumulate current overflow increments).1.toNat =
      boundedTotal (2 ^ width - 1) (current.toNat + (increments.map BitVec.toNat).sum) := by
  induction increments generalizing current overflow with
  | nil =>
      have fits : current.toNat ≤ 2 ^ width - 1 := by
        have bounded := current.isLt
        omega
      simp [wordAccumulate, boundedTotal, Nat.min_eq_right fits]
  | cons increment rest ih =>
      change (wordAccumulate (wordAddLowerBound current increment overflow).1
        (wordAddLowerBound current increment overflow).2 rest).1.toNat = _
      rw [ih, wordAddLowerBound_value, addLowerBound_value]
      · rw [boundedTotal_add]
        simp only [List.map_cons, List.sum_cons, Nat.add_assoc]
      · have bounded := current.isLt
        omega

/-- The cumulative flag records both inherited overflow and overflow of the
new mathematical sum. A saturated counter does not become exact on resume. -/
theorem wordAccumulate_flag {width : Nat} (current : BitVec width)
    (overflow : Bool) (increments : List (BitVec width)) :
    (wordAccumulate current overflow increments).2 =
      (overflow || decide (2 ^ width - 1 <
        current.toNat + (increments.map BitVec.toNat).sum)) := by
  induction increments generalizing current overflow with
  | nil =>
      have fits : current.toNat ≤ 2 ^ width - 1 := by
        have bounded := current.isLt
        omega
      simp [wordAccumulate, Nat.not_lt_of_ge fits]
  | cons increment rest ih =>
      change (wordAccumulate (wordAddLowerBound current increment overflow).1
        (wordAddLowerBound current increment overflow).2 rest).2 = _
      rw [ih, wordAddLowerBound_flag, wordAddLowerBound_value]
      have fits : current.toNat ≤ 2 ^ width - 1 := by
        have bounded := current.isLt
        omega
      by_cases exceeded : 2 ^ width - 1 < current.toNat + increment.toNat
      · have flag : (addLowerBound (2 ^ width - 1) current.toNat increment.toNat).2 =
            true := (addLowerBound_overflow _ _ _ fits).mpr exceeded
        have allExceeded : 2 ^ width - 1 <
            current.toNat + (increment.toNat + (rest.map BitVec.toNat).sum) := by omega
        simp [flag, allExceeded]
      · have flag : (addLowerBound (2 ^ width - 1) current.toNat increment.toNat).2 =
            false := Bool.eq_false_iff.mpr (fun positive =>
              exceeded ((addLowerBound_overflow _ _ _ fits).mp positive))
        have value : (addLowerBound (2 ^ width - 1) current.toNat increment.toNat).1 =
            current.toNat + increment.toNat := by
          rw [addLowerBound_value _ _ _ fits]
          exact Nat.min_eq_right (by omega)
        simp [flag, value, Nat.add_assoc]

/-- Splitting an event batch retains the accumulator and its sticky flag. -/
theorem wordAccumulate_append {width : Nat} (current : BitVec width)
    (overflow : Bool) (first second : List (BitVec width)) :
    wordAccumulate current overflow (first ++ second) =
      wordAccumulate (wordAccumulate current overflow first).1
        (wordAccumulate current overflow first).2 second := by
  induction first generalizing current overflow with
  | nil => rfl
  | cons increment rest ih =>
      simpa only [List.cons_append, wordAccumulate] using
        ih (wordAddLowerBound current increment overflow).1
          (wordAddLowerBound current increment overflow).2

/-- An ordinary batch remains exact; the same later zero increment cannot
erase a previous saturated receipt. -/
theorem word_accumulation_controls :
    wordAccumulate (250 : BitVec 8) false [1, 3] = (254, false) ∧
      wordAccumulate (250 : BitVec 8) false [4, 9, 0] = (255, true) := by decide

/-- Restarting the meter at a resume boundary loses both prior work and its
overflow information, even when the resumed computation adds no work. -/
theorem word_resume_reset_counterexample :
    let inherited := wordAccumulate (250 : BitVec 8) false [9]
    wordAccumulate inherited.1 inherited.2 [0] = (255, true) ∧
      wordAccumulate inherited.1 inherited.2 [0] ≠ wordAccumulate 0 false [0] := by
  decide

/-- A representable increment is exact; overflow uses the upper bound and
must be distinguished from ordinary wrapping unsigned addition. -/
theorem word_counter_controls :
    wordAddLowerBound (250 : BitVec 8) 4 false = (254, false) ∧
      wordAddLowerBound (250 : BitVec 8) 9 false = (255, true) ∧
      (250 : BitVec 8) + 9 = 3 := by decide

namespace Recording

/-- One observed operation, with a representable numerical increment.
`retained` is the storage service's permission to retain this event; it is
irrelevant after the history becomes incomplete. Identity zero denotes a
refused reservation. These service inputs require their own C correspondence. -/
structure Charge (width : Nat) where
  identity : Nat
  origin : Nat
  occurrence : Nat
  kind : Kind
  units : BitVec width
  retained : Bool
  deriving DecidableEq

def Charge.event {width : Nat} (charge : Charge width) : Event :=
  (charge.identity,
    ⟨charge.origin, charge.occurrence, charge.kind, charge.units.toNat⟩)

/-- Numerical counters and retained chronology are separate state. A
missing identity or storage refusal does not undo the counted operation.
This is the observed sequential append boundary, not a parallel join. -/
structure State (width : Nat) where
  counts : Kind → BitVec width
  work : BitVec width
  span : BitVec width
  parallel : Bool
  overflow : Bool
  traceIncomplete : Bool
  history : Ledger

def initial (width : Nat) (traceIncomplete : Bool := false) : State width :=
  ⟨fun _ => 0, 0, 0, false, false, traceIncomplete, []⟩

/-- Charge the kind counter, work and sequential span before attempting
history retention. The inherited flags survive suspension. Zero work is
ignored before identity or storage availability is inspected. -/
def append {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) : State width :=
  if charge.units = 0 then state else
    let counted := wordAddLowerBound (state.counts charge.kind) charge.units state.overflow
    let worked := wordAddLowerBound state.work charge.units counted.2
    let spanned := wordAddLowerBound state.span charge.units worked.2
    let incomplete := state.traceIncomplete || decide (charge.identity = 0) || !charge.retained
    { counts := fun kind => if kind = charge.kind then counted.1 else state.counts kind
      work := worked.1
      span := spanned.1
      parallel := state.parallel
      overflow := spanned.2
      traceIncomplete := incomplete
      history := if incomplete then state.history
        else RunLengthEvents.appendEvent maximum state.history charge.event }

def run {width : Nat} (maximum : Nat) : List (Charge width) → State width → State width
  | [], state => state
  | charge :: rest, state => run maximum rest (append maximum state charge)

/-- All actual nonzero operations, independently of receipt retention. -/
def events {width : Nat} (charges : List (Charge width)) : List Event :=
  charges.filterMap fun charge => if charge.units = 0 then none else some charge.event

private theorem word_fits {width : Nat} (value : BitVec width) :
    value.toNat ≤ 2 ^ width - 1 := by
  have bounded := value.isLt
  omega

/-- Work is counted even when no complete chronological event can be
retained. The counter still agrees with mathematical saturation. -/
theorem append_work {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) :
    (append maximum state charge).work.toNat =
      boundedTotal (2 ^ width - 1) (state.work.toNat + charge.units.toNat) := by
  by_cases zero : charge.units = 0
  · simp [append, zero, boundedTotal, Nat.min_eq_right (word_fits state.work)]
  · simp only [append, if_neg zero]
    rw [wordAddLowerBound_value, addLowerBound_value _ _ _ (word_fits state.work)]

theorem append_span {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) :
    (append maximum state charge).span.toNat =
      boundedTotal (2 ^ width - 1) (state.span.toNat + charge.units.toNat) := by
  by_cases zero : charge.units = 0
  · simp [append, zero, boundedTotal, Nat.min_eq_right (word_fits state.span)]
  · simp only [append, if_neg zero]
    rw [wordAddLowerBound_value, addLowerBound_value _ _ _ (word_fits state.span)]

theorem append_count {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) (kind : Kind) :
    ((append maximum state charge).counts kind).toNat =
      boundedTotal (2 ^ width - 1)
        ((state.counts kind).toNat + if kind = charge.kind then charge.units.toNat else 0) := by
  by_cases zero : charge.units = 0
  · simp [append, zero, boundedTotal, Nat.min_eq_right (word_fits (state.counts kind))]
  · simp only [append, if_neg zero]
    by_cases same : kind = charge.kind
    · subst kind
      rw [if_pos (show charge.kind = charge.kind from rfl),
        if_pos (show charge.kind = charge.kind from rfl)]
      rw [wordAddLowerBound_value, addLowerBound_value _ _ _ (word_fits _)]
    · simp only [if_neg same, Nat.add_zero]
      exact (Nat.min_eq_right (word_fits _)).symm

/-- A refusal permanently marks this receipt as incomplete, including on
later successful reservations. No future append repairs the missing past. -/
theorem append_incomplete {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) (incomplete : state.traceIncomplete = true) :
    (append maximum state charge).traceIncomplete = true := by
  by_cases zero : charge.units = 0
  · simpa only [append, if_pos zero] using incomplete
  · simp only [append, if_neg zero, incomplete, Bool.true_or]

theorem run_incomplete {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (incomplete : state.traceIncomplete = true) :
    (run maximum charges state).traceIncomplete = true := by
  induction charges generalizing state with
  | nil => exact incomplete
  | cons charge rest ih => exact ih _ (append_incomplete _ _ _ incomplete)

theorem append_incomplete_history {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) (incomplete : state.traceIncomplete = true) :
    (append maximum state charge).history = state.history := by
  by_cases zero : charge.units = 0
  · simp only [append, if_pos zero]
  · simp only [append, if_neg zero, incomplete, Bool.true_or, if_true]

/-- Receipt retention stays stopped after the first failure. This keeps
the missing history explicit, instead of pretending later events repair it. -/
theorem run_incomplete_history {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (incomplete : state.traceIncomplete = true) :
    (run maximum charges state).history = state.history := by
  induction charges generalizing state with
  | nil => rfl
  | cons charge rest ih =>
      exact (ih _ (append_incomplete _ _ _ incomplete)).trans
        (append_incomplete_history _ _ _ incomplete)

theorem append_overflow {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) (overflow : state.overflow = true) :
    (append maximum state charge).overflow = true := by
  by_cases zero : charge.units = 0
  · simpa only [append, if_pos zero] using overflow
  · simp only [append, if_neg zero, overflow, word_overflow_is_sticky]

theorem run_overflow {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (overflow : state.overflow = true) :
    (run maximum charges state).overflow = true := by
  induction charges generalizing state with
  | nil => exact overflow
  | cons charge rest ih => exact ih _ (append_overflow _ _ _ overflow)

theorem run_complete_initial {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (complete : (run maximum charges state).traceIncomplete = false) :
    state.traceIncomplete = false := by
  cases inherited : state.traceIncomplete with
  | false => rfl
  | true => exact Bool.noConfusion ((run_incomplete _ _ _ inherited).symm.trans complete)

/-- A complete append retains exactly one new event, or no event for a
zero increment. This is not asserted for incomplete histories. -/
theorem append_history_of_complete {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) (complete : (append maximum state charge).traceIncomplete = false) :
    RunLengthEvents.expand (append maximum state charge).history =
      RunLengthEvents.expand state.history ++ events [charge] := by
  by_cases zero : charge.units = 0
  · simp [append, zero, events]
  · have allowed :
        (state.traceIncomplete || decide (charge.identity = 0) || !charge.retained) = false := by
      simpa only [append, if_neg zero] using complete
    simp only [append, if_neg zero, allowed, Bool.false_eq_true, if_false,
      RunLengthEvents.expand_appendEvent]
    simp only [events, List.filterMap_cons, if_neg zero, List.filterMap_nil]

/-- The entire state, including counters and sticky flags, composes across
resumption. Retaining only the stored events is insufficient. -/
theorem run_append {width : Nat} (maximum : Nat) (first second : List (Charge width))
    (state : State width) :
    run maximum (first ++ second) state =
      run maximum second (run maximum first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons charge rest ih => exact ih _

theorem events_append {width : Nat} (first second : List (Charge width)) :
    events (first ++ second) = events first ++ events second := by
  exact List.filterMap_append

/-- Every observed operation contributes its numerical work whether its
identity or storage was available. Saturation retains the cumulative sum. -/
theorem run_work {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) :
    (run maximum charges state).work.toNat =
      boundedTotal (2 ^ width - 1)
        (state.work.toNat + (charges.map fun charge => charge.units.toNat).sum) := by
  induction charges generalizing state with
  | nil => simp [run, boundedTotal, Nat.min_eq_right (word_fits state.work)]
  | cons charge rest ih =>
      rw [run, ih, append_work, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

/-- These append operations are sequential: the span coordinate accumulates
its inherited value, rather than claiming a parallel critical-path readout. -/
theorem run_span {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) :
    (run maximum charges state).span.toNat =
      boundedTotal (2 ^ width - 1)
        (state.span.toNat + (charges.map fun charge => charge.units.toNat).sum) := by
  induction charges generalizing state with
  | nil => simp [run, boundedTotal, Nat.min_eq_right (word_fits state.span)]
  | cons charge rest ih =>
      rw [run, ih, append_span, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Sequential appends retain an inherited causal-span declaration; they
cannot turn a previously parallel receipt into a sequential one. -/
theorem append_parallel {width : Nat} (maximum : Nat) (state : State width)
    (charge : Charge width) :
    (append maximum state charge).parallel = state.parallel := by
  unfold append
  split <;> rfl

theorem run_parallel {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) : (run maximum charges state).parallel = state.parallel := by
  induction charges generalizing state with
  | nil => rfl
  | cons charge rest ih => exact (ih _).trans (append_parallel _ _ _)

theorem run_count {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (kind : Kind) :
    ((run maximum charges state).counts kind).toNat =
      boundedTotal (2 ^ width - 1) ((state.counts kind).toNat +
        (charges.map fun charge => if kind = charge.kind then charge.units.toNat else 0).sum) := by
  induction charges generalizing state with
  | nil => simp [run, boundedTotal, Nat.min_eq_right (word_fits (state.counts kind))]
  | cons charge rest ih =>
      rw [run, ih, append_count, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Completeness justifies reconstructing the full retained chronology.
Without this flag, even a later successful reservation cannot justify it. -/
theorem run_history_of_complete {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (complete : (run maximum charges state).traceIncomplete = false) :
    RunLengthEvents.expand (run maximum charges state).history =
      RunLengthEvents.expand state.history ++ events charges := by
  induction charges generalizing state with
  | nil => simp [run, events]
  | cons charge rest ih =>
      have firstComplete := run_complete_initial maximum rest (append maximum state charge) complete
      rw [run, ih _ complete, append_history_of_complete _ _ _ firstComplete]
      rw [List.append_assoc, ← events_append]
      rfl

/-- Only a complete history is available as a complete trace observation.
Numerical counters remain separately readable when this returns none. -/
def completeHistory {width : Nat} (state : State width) : Option (List Event) :=
  if state.traceIncomplete then none else some (RunLengthEvents.expand state.history)

theorem completeHistory_of_run {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (state : State width) (complete : (run maximum charges state).traceIncomplete = false) :
    completeHistory (run maximum charges state) =
      some (RunLengthEvents.expand state.history ++ events charges) := by
  simp only [completeHistory, complete, Bool.false_eq_true, if_false]
  rw [run_history_of_complete _ _ _ complete]

private theorem events_work {width : Nat} (charges : List (Charge width)) :
    (totals (events charges)).2 = (charges.map fun charge => charge.units.toNat).sum := by
  induction charges with
  | nil => rfl
  | cons charge rest ih =>
      by_cases zero : charge.units = 0
      · have empty : events (charge :: rest) = events rest := by
          simp only [events, List.filterMap_cons, if_pos zero]
        have zeroNat : charge.units.toNat = 0 := by rw [zero]; rfl
        rw [empty]
        simpa only [List.map_cons, List.sum_cons, zeroNat, Nat.zero_add] using ih
      · simp only [events, List.filterMap_cons, if_neg zero, totals,
          List.map_cons, List.sum_cons, Prod.snd_add, eventGrade, Charge.event]
        exact congrArg (charge.units.toNat + ·) ih

private theorem events_count {width : Nat} (charges : List (Charge width)) (kind : Kind) :
    (totals (events charges)).1 kind =
      (charges.map fun charge => if kind = charge.kind then charge.units.toNat else 0).sum := by
  induction charges with
  | nil => rfl
  | cons charge rest ih =>
      by_cases zero : charge.units = 0
      · have empty : events (charge :: rest) = events rest := by
          simp only [events, List.filterMap_cons, if_pos zero]
        have zeroNat : charge.units.toNat = 0 := by rw [zero]; rfl
        rw [empty]
        simpa only [List.map_cons, List.sum_cons, zeroNat, ite_self, Nat.zero_add] using ih
      · simp only [events, List.filterMap_cons, if_neg zero,
          totals, List.map_cons, List.sum_cons, Prod.fst_add, Pi.add_apply,
          eventGrade, Charge.event]
        rw [show (if charge.kind = kind then charge.units.toNat else 0) =
            (if kind = charge.kind then charge.units.toNat else 0) by simp only [eq_comm]]
        exact congrArg ((if kind = charge.kind then charge.units.toNat else 0) + ·) ih

/-- On a complete freshly initialized receipt, its chronology determines
the saturated work counter. The incomplete view has no such law. -/
theorem complete_work {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (complete : (run maximum charges (initial width)).traceIncomplete = false) :
    (run maximum charges (initial width)).work.toNat =
      boundedTotal (2 ^ width - 1) (snapshot (run maximum charges (initial width)).history).2 := by
  have chronology := run_history_of_complete maximum charges (initial width) complete
  change RunLengthEvents.expand (run maximum charges (initial width)).history =
    [] ++ events charges at chronology
  rw [List.nil_append] at chronology
  rw [run_work, snapshot, chronology, events_work]
  simp [initial]

theorem complete_count {width : Nat} (maximum : Nat) (charges : List (Charge width))
    (complete : (run maximum charges (initial width)).traceIncomplete = false) (kind : Kind) :
    ((run maximum charges (initial width)).counts kind).toNat =
      boundedTotal (2 ^ width - 1) ((snapshot (run maximum charges (initial width)).history).1 kind) := by
  have chronology := run_history_of_complete maximum charges (initial width) complete
  change RunLengthEvents.expand (run maximum charges (initial width)).history =
    [] ++ events charges at chronology
  rw [List.nil_append] at chronology
  rw [run_count, snapshot, chronology, events_count]
  simp [initial]

/-- Complete numerical coordinates must be justified by their chronology.
An incomplete child keeps independent counters, without reconstructing
missing events or imposing a sequential meaning on its causal span. -/
def CompleteMeasured {width : Nat} (state : State width) : Prop :=
  state.traceIncomplete = false →
    state.work.toNat = boundedTotal (2 ^ width - 1) (snapshot state.history).2 ∧
      ∀ kind, (state.counts kind).toNat =
        boundedTotal (2 ^ width - 1) ((snapshot state.history).1 kind)

theorem run_completeMeasured {width : Nat} (maximum : Nat) (charges : List (Charge width)) :
    CompleteMeasured (run maximum charges (initial width)) :=
  fun complete => ⟨complete_work maximum charges complete,
    complete_count maximum charges complete⟩

theorem work_factors_complete_history (width maximum : Nat) :
    Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun charges : {charges : List (Charge width) //
          (run maximum charges (initial width)).traceIncomplete = false} =>
        (run maximum charges.val (initial width)).history)
      (fun charges => (run maximum charges.val (initial width)).work.toNat) :=
  ⟨fun history => boundedTotal (2 ^ width - 1) (snapshot history).2,
    fun charges => (complete_work maximum charges.val charges.property).symm⟩

/-- The public numerical observation retains flags and the stored prefix.
An incomplete prefix is useful data, but is not a complete trace certificate. -/
structure Observation where
  counts : Kind → Nat
  work : Nat
  span : Nat
  parallel : Bool
  overflow : Bool
  traceIncomplete : Bool
  retainedEvents : List Event

def observe {width : Nat} (state : State width) : Observation :=
  ⟨fun kind => (state.counts kind).toNat, state.work.toNat, state.span.toNat,
    state.parallel, state.overflow, state.traceIncomplete,
    RunLengthEvents.expand state.history⟩

def readCharge (identity origin occurrence : Nat) (retained : Bool) : Charge 64 :=
  ⟨identity, origin, occurrence, .costRead, 1, retained⟩

/-- A 64-bit profile read returns the preceding observation and then
charges its own operation. Formatting and scope delivery are separate services. -/
def inspect (maximum : Nat) (state : State 64) (identity origin occurrence : Nat)
    (retained : Bool) : Observation × State 64 :=
  (observe state, append maximum state (readCharge identity origin occurrence retained))

theorem inspect_preceding (maximum : Nat) (state : State 64)
    (identity origin occurrence : Nat) (retained : Bool) :
    (inspect maximum state identity origin occurrence retained).1 = observe state := rfl

/-- The read's work belongs to the following snapshot. Identity or storage
failure does not make inspection free, and inherited saturation is retained. -/
theorem inspect_work (maximum : Nat) (state : State 64)
    (identity origin occurrence : Nat) (retained : Bool) :
    (inspect maximum state identity origin occurrence retained).2.work.toNat =
      boundedTotal (2 ^ 64 - 1) (state.work.toNat + 1) :=
  append_work maximum state (readCharge identity origin occurrence retained)

theorem inspect_count (maximum : Nat) (state : State 64)
    (identity origin occurrence : Nat) (retained : Bool) :
    ((inspect maximum state identity origin occurrence retained).2.counts .costRead).toNat =
      boundedTotal (2 ^ 64 - 1) ((state.counts .costRead).toNat + 1) := by
  have counted := append_count maximum state (readCharge identity origin occurrence retained) .costRead
  rw [if_pos (show Kind.costRead = (readCharge identity origin occurrence retained).kind from rfl)]
    at counted
  exact counted

theorem inspect_retains_incomplete (maximum : Nat) (state : State 64)
    (identity origin occurrence : Nat) (retained : Bool)
    (incomplete : state.traceIncomplete = true) :
    (inspect maximum state identity origin occurrence retained).2.traceIncomplete = true ∧
      (inspect maximum state identity origin occurrence retained).2.history = state.history :=
  ⟨append_incomplete _ _ _ incomplete, append_incomplete_history _ _ _ incomplete⟩

/-- The independently specified unbounded read has the same resulting
chronology when the machine read's retention succeeds. -/
theorem inspect_history_of_complete (maximum : Nat) (state : State 64)
    (identity origin occurrence : Nat) (retained : Bool)
    (complete : (inspect maximum state identity origin occurrence retained).2.traceIncomplete = false) :
    RunLengthEvents.expand (inspect maximum state identity origin occurrence retained).2.history =
      RunLengthEvents.expand (NativeCostLedger.inspect maximum state.history
        identity origin occurrence).2 := by
  rw [inspect, append_history_of_complete _ _ _ complete]
  simp only [events, List.filterMap_cons, readCharge, List.filterMap_nil]
  rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
  exact (RunLengthEvents.expand_appendEvent maximum state.history
    (readEvent identity origin occurrence)).symm

/-- Reading a receipt again is a new charged observation. Reusing the
preceding value cannot account for the second operation. -/
theorem repeated_read_control :
    let first := inspect 255 (initial 64) 1 7 12 true
    let second := inspect 255 first.2 2 7 12 true
    first.1.work = 0 ∧ second.1.work = 1 ∧ second.2.work.toNat = 2 ∧
      first.1.retainedEvents = [] ∧ second.1.retainedEvents.length = 1 := by
  decide

/-- A receipt with missing earlier history remains numerically readable;
the read charges one more unit while retaining the same incomplete prefix. -/
theorem incomplete_read_control :
    let state : State 64 := { initial 64 with work := 9, span := 9, traceIncomplete := true }
    let read := inspect 255 state 2 7 12 true
    read.1.work = 9 ∧ read.1.traceIncomplete = true ∧ read.1.retainedEvents = [] ∧
      read.2.work.toNat = 10 ∧ read.2.traceIncomplete = true ∧ completeHistory read.2 = none := by
  decide

/-- Deliver to the supplied locations in their actual order. Each local
append receives its own retention decision and whole inherited state.
This construction does not impose uniqueness on the location list. -/
def deliver {width : Nat} (maximum : Nat) (charges : Nat → Charge width)
    (locations : List Nat) (store : Nat → State width) : Nat → State width :=
  VariableInventory.updateKeys (fun location state => append maximum state (charges location))
    locations store

/-- Retention is a per-destination service. It changes no physical event
field: identity, origin, occurrence, operation and units remain shared. -/
def localCharge {width : Nat} (charge : Charge width) (retained : Nat → Bool)
    (location : Nat) : Charge width := { charge with retained := retained location }

theorem localCharge_event {width : Nat} (charge : Charge width) (retained : Nat → Bool)
    (location : Nat) : (localCharge charge retained location).event = charge.event := rfl

/-- A finite active scope chain delivers one common physical event once
to each containing ledger, using that ledger's retention service. Live
locations, rather than exhausted origin identifiers, determine aliases. -/
def chargeScopes {width : Nat} (maximum : Nat) (scopes : List (Option Nat))
    (charge : Charge width) (retained : Nat → Bool) (store : Nat → State width) :
    Nat → State width :=
  deliver maximum (localCharge charge retained) (scopeTargets scopes) store

/-- Whole-state correspondence: unique destinations are charged once,
and all counters, flags and histories of absent destinations are retained. -/
theorem chargeScopes_at {width : Nat} (maximum : Nat) (scopes : List (Option Nat))
    (charge : Charge width) (retained : Nat → Bool) (store : Nat → State width)
    (location : Nat) :
    chargeScopes maximum scopes charge retained store location =
      if some location ∈ scopes then
        append maximum (store location) (localCharge charge retained location)
      else store location := by
  rw [chargeScopes, deliver,
    VariableInventory.updateKeys_unique_at _ _ _ (scopeTargets_unique scopes)]
  simp only [scopeTargets_mem]

/-- The independent full-prefix algorithm has the same entire resulting
store. This does not establish physical pointer validity or scope lifetime. -/
theorem chargeScopes_prefix_correspondence {width : Nat} (maximum : Nat)
    (scopes : List (Option Nat)) (charge : Charge width) (retained : Nat → Bool)
    (store : Nat → State width) :
    deliver maximum (localCharge charge retained) (prefixScopeTargets scopes) store =
      chargeScopes maximum scopes charge retained store := by
  rw [prefixScopeTargets_correspondence]
  rfl

theorem chargeScopes_disabled {width : Nat} (maximum : Nat) (charge : Charge width)
    (retained : Nat → Bool) (store : Nat → State width) :
    chargeScopes maximum [] charge retained store = store := rfl

/-- Saturation is local to each observer's inherited work counter. A
storage failure changes receipt availability, not the operation's cost. -/
theorem chargeScopes_work {width : Nat} (maximum : Nat) (scopes : List (Option Nat))
    (charge : Charge width) (retained : Nat → Bool) (store : Nat → State width)
    (location : Nat) :
    (chargeScopes maximum scopes charge retained store location).work.toNat =
      boundedTotal (2 ^ width - 1)
        ((store location).work.toNat + if some location ∈ scopes then charge.units.toNat else 0) := by
  rw [chargeScopes_at]
  by_cases present : some location ∈ scopes
  · simpa only [if_pos present, localCharge] using
      append_work maximum (store location) (localCharge charge retained location)
  · simp only [if_neg present, Nat.add_zero]
    exact (Nat.min_eq_right (word_fits (store location).work)).symm

theorem chargeScopes_count {width : Nat} (maximum : Nat) (scopes : List (Option Nat))
    (charge : Charge width) (retained : Nat → Bool) (store : Nat → State width)
    (location : Nat) (kind : Kind) :
    ((chargeScopes maximum scopes charge retained store location).counts kind).toNat =
      boundedTotal (2 ^ width - 1) (((store location).counts kind).toNat +
        if some location ∈ scopes ∧ kind = charge.kind then charge.units.toNat else 0) := by
  rw [chargeScopes_at]
  by_cases present : some location ∈ scopes
  · rw [if_pos present]
    have counted := append_count maximum (store location) (localCharge charge retained location) kind
    by_cases same : kind = charge.kind
    · rw [if_pos ⟨present, same⟩]
      rw [if_pos (show kind = (localCharge charge retained location).kind from same)] at counted
      exact counted
    · rw [if_neg (fun both => same both.2)]
      rw [if_neg (show kind ≠ (localCharge charge retained location).kind from same)] at counted
      exact counted
  · simp only [present, false_and, if_false, Nat.add_zero]
    exact (Nat.min_eq_right (word_fits ((store location).counts kind))).symm

/-- A complete destination receives the same new event as every other
complete destination, with its own preceding chronological prefix. -/
theorem chargeScopes_history_of_complete {width : Nat} (maximum : Nat)
    (scopes : List (Option Nat)) (charge : Charge width) (retained : Nat → Bool)
    (store : Nat → State width) (location : Nat) (present : some location ∈ scopes)
    (complete : (chargeScopes maximum scopes charge retained store location).traceIncomplete = false) :
    RunLengthEvents.expand (chargeScopes maximum scopes charge retained store location).history =
      RunLengthEvents.expand (store location).history ++ events [charge] := by
  rw [chargeScopes_at, if_pos present] at complete ⊢
  rw [append_history_of_complete _ _ _ complete]
  have same : events [localCharge charge retained location] = events [charge] := by
    simp only [events, List.filterMap_cons, List.filterMap_nil, localCharge, Charge.event]
  rw [same]

/-- Incompleteness persists per destination, without contaminating another
containing ledger or stopping this ledger's numerical charging. -/
theorem chargeScopes_incomplete {width : Nat} (maximum : Nat) (scopes : List (Option Nat))
    (charge : Charge width) (retained : Nat → Bool) (store : Nat → State width)
    (location : Nat) (incomplete : (store location).traceIncomplete = true) :
    (chargeScopes maximum scopes charge retained store location).traceIncomplete = true ∧
      (chargeScopes maximum scopes charge retained store location).history = (store location).history := by
  rw [chargeScopes_at]
  split
  · exact ⟨append_incomplete _ _ _ incomplete, append_incomplete_history _ _ _ incomplete⟩
  · exact ⟨incomplete, rfl⟩

/-- Each chronological command captures its own scope chain and
per-destination retention decisions. The residual is the remaining command
list together with the whole store, including sticky flags and history. -/
structure ScopedCharge (width : Nat) where
  scopes : List (Option Nat)
  charge : Charge width
  retained : Nat → Bool

/-- A finite readout keeps the complete scope chain and each active physical
destination's retention decision. Decisions at absent locations are not part
of this operation. This readout is data, not authority to issue a charge. -/
structure ScopedChargeReceipt (width : Nat) where
  scopes : List (Option Nat)
  charge : Charge width
  retention : List (Nat × Bool)
  deriving DecidableEq

def ScopedCharge.receipt {width : Nat} (command : ScopedCharge width) :
    ScopedChargeReceipt width :=
  ⟨command.scopes, command.charge,
    (scopeTargets command.scopes).map (fun location => (location, command.retained location))⟩

/-- Equality of these finite readouts identifies the retention service at
every destination actually used by the operation, without comparing an
infinite function or identifying distinct physical ledger locations. -/
theorem receipt_retention_eq {width : Nat} (first second : ScopedCharge width)
    (same : first.receipt = second.receipt) (location : Nat)
    (present : some location ∈ first.scopes) :
    first.retained location = second.retained location := by
  have scopes := congrArg ScopedChargeReceipt.scopes same
  have retention := congrArg ScopedChargeReceipt.retention same
  have entry : (location, first.retained location) ∈ first.receipt.retention :=
    List.mem_map.mpr ⟨location, (scopeTargets_mem first.scopes location).mpr present, rfl⟩
  rw [retention] at entry
  obtain ⟨other, _, equal⟩ := List.mem_map.mp entry
  have index : other = location := congrArg Prod.fst equal
  subst other
  exact (congrArg Prod.snd equal).symm

/-- A compared command preserves the entire functional store: counters,
sticky flags, chronological history, and all untouched locations. -/
theorem chargeScopes_receipt_eq {width : Nat} (maximum : Nat)
    (first second : ScopedCharge width) (same : first.receipt = second.receipt)
    (store : Nat → State width) :
    chargeScopes maximum first.scopes first.charge first.retained store =
      chargeScopes maximum second.scopes second.charge second.retained store := by
  have scopes := congrArg ScopedChargeReceipt.scopes same
  have charge := congrArg ScopedChargeReceipt.charge same
  funext location
  rw [chargeScopes_at, chargeScopes_at]
  change first.scopes = second.scopes at scopes
  change first.charge = second.charge at charge
  rw [← scopes]
  by_cases present : some location ∈ first.scopes
  · simp only [present, if_true]
    rw [charge]
    have retained := receipt_retention_eq first second same location present
    simp only [localCharge, retained]
  · simp only [present, if_false]

def runScopes {width : Nat} (maximum : Nat) :
    List (ScopedCharge width) → (Nat → State width) → Nat → State width
  | [], store => store
  | command :: rest, store =>
      runScopes maximum rest
        (chargeScopes maximum command.scopes command.charge command.retained store)

/-- Stopping and resuming with the whole inherited store preserves every
coordinate, not only work or the expanded complete portion of a receipt. -/
theorem runScopes_append {width : Nat} (maximum : Nat)
    (first second : List (ScopedCharge width)) (store : Nat → State width) :
    runScopes maximum (first ++ second) store =
      runScopes maximum second (runScopes maximum first store) := by
  induction first generalizing store with
  | nil => rfl
  | cons command rest ih => exact ih _

/-- Phase boundaries do not reset any destination state. The independent
flat command interpreter agrees with consuming each ordered phase in turn. -/
theorem runScopes_flatten {width : Nat} (maximum : Nat)
    (phases : List (List (ScopedCharge width))) (store : Nat → State width) :
    runScopes maximum phases.flatten store =
      phases.foldl (fun current commands => runScopes maximum commands current) store := by
  induction phases generalizing store with
  | nil => rfl
  | cons phase rest ih =>
      simp only [List.flatten_cons, runScopes_append, List.foldl_cons]
      exact ih _

/-- Scoped accounting is an instance of the existing controller observer.
Each selected occurrence supplies its independently specified chronological
commands, including their captured destinations and retention decisions.
No command is inferred from the number of selections or emitted answers. -/
def scopedController {Node Answer Memory : Type*} {width : Nat} (maximum : Nat)
    (base : Mettapedia.GSLT.Core.InferenceControl.Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (store : Nat → State width) :
    Mettapedia.GSLT.Core.InferenceControl.Controller Node Answer (Memory × (Nat → State width)) :=
  base.observing commands store
    (fun current phase => runScopes maximum phase current)

/-- Cost-blind erasure retains the whole controller run and complete
frontier. A client reading these costs has a stronger observation contract. -/
theorem scopedController_erasure {Node Answer Memory : Type*} {width : Nat}
    (maximum : Nat) (system : Mettapedia.GSLT.Core.BranchingTemporal.BranchingSystem Node Answer)
    (base : Mettapedia.GSLT.Core.InferenceControl.Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (fuel : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      Node Answer (Memory × (Nat → State width))) :
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system
      (scopedController maximum base commands initialStore) fuel snapshot).mapMemory Prod.fst =
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system base fuel
        (snapshot.mapMemory Prod.fst) :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.observing_run_erasure
    system base commands initialStore (fun current phase => runScopes maximum phase current)
    fuel snapshot

/-- The observer's whole poststore is the independent scoped-command run
over the unobserved controller stream. Existing incompleteness, overflow,
history and untouched locations survive this equality. -/
theorem scopedController_account {Node Answer Memory : Type*} {width : Nat}
    (maximum : Nat) (system : Mettapedia.GSLT.Core.BranchingTemporal.BranchingSystem Node Answer)
    (base : Mettapedia.GSLT.Core.InferenceControl.Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (fuel : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      Node Answer (Memory × (Nat → State width))) :
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system
      (scopedController maximum base commands initialStore) fuel snapshot).memory.2 =
      runScopes maximum
        (Mettapedia.GSLT.Core.InferenceControl.Recording.stream system base commands fuel
          (snapshot.mapMemory Prod.fst)).flatten snapshot.memory.2 := by
  rw [runScopes_flatten]
  exact Mettapedia.GSLT.Core.InferenceControl.Recording.observer_run
    system base commands initialStore (fun current phase => runScopes maximum phase current)
    fuel snapshot

/-- The independently specified single-ledger run is the projection of a
scoped execution. Multiplicity of frames does not multiply commands. -/
theorem runScopes_at {width : Nat} (maximum : Nat) (commands : List (ScopedCharge width))
    (store : Nat → State width) (location : Nat) :
    runScopes maximum commands store location =
      run maximum (commands.filterMap fun command =>
        if some location ∈ command.scopes then
          some (localCharge command.charge command.retained location) else none) (store location) := by
  induction commands generalizing store with
  | nil => rfl
  | cons command rest ih =>
      rw [runScopes, ih, chargeScopes_at]
      by_cases present : some location ∈ command.scopes <;>
        simp only [List.filterMap_cons, present, if_true, if_false, run]

/-- Comparing the ordered finite receipts preserves the whole resumed
account. Dropping, duplicating or reordering a command is not licensed by
equality of final numerical totals or authored answers. -/
theorem runScopes_receipt_eq {width : Nat} (maximum : Nat)
    (first second : List (ScopedCharge width))
    (same : first.map ScopedCharge.receipt = second.map ScopedCharge.receipt)
    (store : Nat → State width) :
    runScopes maximum first store = runScopes maximum second store := by
  induction first generalizing second store with
  | nil =>
      cases second with
      | nil => rfl
      | cons head rest => cases same
  | cons head rest ih =>
      cases second with
      | nil => cases same
      | cons other remaining =>
          obtain ⟨headSame, tailSame⟩ := List.cons.inj same
          rw [runScopes, runScopes, chargeScopes_receipt_eq maximum head other headSame]
          exact ih remaining tailSame _

/-- Projection to a live destination agrees with the independent local
ledger interpreter. Duplicate containing frames do not multiply a charge. -/
theorem scopedController_at {Node Answer Memory : Type*} {width : Nat}
    (maximum : Nat) (system : Mettapedia.GSLT.Core.BranchingTemporal.BranchingSystem Node Answer)
    (base : Mettapedia.GSLT.Core.InferenceControl.Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (fuel : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      Node Answer (Memory × (Nat → State width))) (location : Nat) :
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run system
      (scopedController maximum base commands initialStore) fuel snapshot).memory.2 location =
      run maximum
        ((Mettapedia.GSLT.Core.InferenceControl.Recording.stream system base commands fuel
          (snapshot.mapMemory Prod.fst)).flatten.filterMap fun command =>
            if some location ∈ command.scopes then
              some (localCharge command.charge command.retained location) else none)
        (snapshot.memory.2 location) := by
  rw [scopedController_account, runScopes_at]

section ControllerObservation

open Mettapedia.GSLT.Core.BranchingTemporal (BranchingSystem)
open Mettapedia.GSLT.Core.InferenceControl (Controller Snapshot)
open Mettapedia.GSLT.Core.InferenceControl.Recording (Prefix)

variable {Node Answer Memory Event : Type*} {width : Nat}

/-- Local transport of the original continuation and each complete phase
preserves every finite cost-bearing checkpoint. Physical charge identities,
scope destinations and retention inputs are compared before accounting. -/
theorem scopedController_transport {NextNode NextMemory : Type*}
    (maximum : Nat) (mapping : Node → NextNode) (transfer : Memory → NextMemory)
    (source : BranchingSystem Node Answer) (target : BranchingSystem NextNode Answer)
    (first : Controller Node Answer Memory) (second : Controller NextNode Answer NextMemory)
    (sourceCommands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (targetCommands : NextMemory → NextNode → Option Answer → List NextNode → List (ScopedCharge width))
    (initialStore : Nat → State width)
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
    (commands : ∀ memory node emission generated,
      sourceCommands memory node emission generated =
        targetCommands (transfer memory) (mapping node) emission (generated.map mapping))
    (fuel : Nat) (snapshot : Snapshot Node Answer (Memory × (Nat → State width))) :
    (Snapshot.run source (scopedController maximum first sourceCommands initialStore)
      fuel snapshot).mapState mapping (fun memory => (transfer memory.1, memory.2)) =
      Snapshot.run target (scopedController maximum second targetCommands initialStore) fuel
        (snapshot.mapState mapping (fun memory => (transfer memory.1, memory.2))) :=
  Snapshot.observing_run_transport mapping transfer id id source target first second
    sourceCommands targetCommands initialStore initialStore
    (fun current phase => runScopes maximum phase current)
    (fun current phase => runScopes maximum phase current)
    emits successors reorders integrates advances commands (fun _ _ => rfl) fuel snapshot

/-- Recording and scoped accounting share the original scheduler and may
exchange nesting order when both observations read only its continuation.
Both accumulated states and the entire search are retained by the swap.
Recorder-dependent expense is not an independent observation of this kind. -/
theorem recorded_scopedController_commute (maximum : Nat)
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (record : Memory → Node → Option Answer → List Node → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Node Answer
      ((Memory × (Nat → State width)) × Option (Prefix Event))) :
    (Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore)
        (fun memory => record memory.1) capacity) fuel snapshot).mapMemory
          (fun memory => ((memory.1.1, memory.2), memory.1.2)) =
      Snapshot.run system
        (scopedController maximum
          (Mettapedia.GSLT.Core.InferenceControl.Recording.controller base record capacity)
          (fun memory => commands memory.1) initialStore) fuel
        (snapshot.mapMemory (fun memory => ((memory.1.1, memory.2), memory.1.2))) := by
  simpa only [scopedController, Mettapedia.GSLT.Core.InferenceControl.Recording.controller] using
    Snapshot.independent_observers_run system base commands record initialStore
      (Mettapedia.GSLT.Core.InferenceControl.Recording.initial capacity)
      (fun current phase => runScopes maximum phase current)
      (fun current event => Mettapedia.GSLT.Core.InferenceControl.Recording.accept current
        (fun _ => event)) fuel snapshot

/-- Adding the bounded record preserves the whole scoped poststore. The
reference remains the independent unrecorded controller's command stream,
not a command list reconstructed from retained graph nodes. -/
theorem recorded_scopedController_account (maximum : Nat)
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (record : Memory → Node → Option Answer → List Node → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Node Answer
      ((Memory × (Nat → State width)) × Option (Prefix Event))) :
    (Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore)
        (fun memory => record memory.1) capacity) fuel snapshot).memory.1.2 =
      runScopes maximum
        (Mettapedia.GSLT.Core.InferenceControl.Recording.stream system base commands fuel
          (snapshot.mapMemory (fun memory => memory.1.1))).flatten snapshot.memory.1.2 := by
  have erased := congrArg (fun result => result.memory.2)
    (Mettapedia.GSLT.Core.InferenceControl.Recording.run_erasure system
      (scopedController maximum base commands initialStore)
      (fun memory => record memory.1) capacity fuel snapshot)
  exact erased.trans (scopedController_account maximum system base commands initialStore fuel
    (snapshot.mapMemory Prod.fst))

/-- Scoped accounting does not change a record whose payload reads only
the original continuation. Existing capacity and omissions survive; the
accounting and recorder observations do not need identical payload types. -/
theorem recorded_scopedController_record (maximum : Nat)
    (system : BranchingSystem Node Answer) (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (record : Memory → Node → Option Answer → List Node → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot Node Answer
      ((Memory × (Nat → State width)) × Option (Prefix Event))) :
    (Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore)
        (fun memory => record memory.1) capacity) fuel snapshot).memory.2 =
      Mettapedia.GSLT.Core.InferenceControl.Recording.append snapshot.memory.2
        (Mettapedia.GSLT.Core.InferenceControl.Recording.stream system base record fuel
          (snapshot.mapMemory (fun memory => memory.1.1))) := by
  rw [Mettapedia.GSLT.Core.InferenceControl.Recording.run_record]
  unfold scopedController
  rw [Mettapedia.GSLT.Core.InferenceControl.Recording.observing_stream_erasure]
  rfl

/-- Pure replay of a complete capture returns the whole cost-bearing
controller checkpoint, not merely the selected answers. The same initial
checkpoint, command service and controller are explicit parameters; this
does not authorize replay of an external effect or a different initial meter. -/
theorem scopedController_recorded_replay [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (capacity fuel : Nat)
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width)))
    (fits : (Mettapedia.GSLT.Core.InferenceControl.Recording.stream system
      (scopedController maximum base commands initialStore)
      Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.observe fuel snapshot).length ≤ capacity) :
    ((Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore)
        Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.observe (some capacity)) fuel
      (Mettapedia.GSLT.Core.InferenceControl.Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.readout system
          (scopedController maximum base commands initialStore) record snapshot) =
      some (.ok (Snapshot.run system
        (scopedController maximum base commands initialStore) fuel snapshot)) :=
  Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.recorded_replay
    system (scopedController maximum base commands initialStore) capacity fuel snapshot fits

end ControllerObservation

/-! ## Checked primitive phases over the existing replay protocol

The captured expansion and the required primitive phase are checked
independently. The command service is fixed by the supplied source/profile
contract; interpreting a supplied command list alone cannot authenticate it.
The adapter calls the existing replay transition and does not define another
evaluator. It grants no authority to repeat an external effect.
-/

namespace PhaseReplay

open Mettapedia.GSLT.Core.BranchingTemporal (BranchingSystem)
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.InferenceControl.Recording (Prefix stream next)

variable {Node Answer Memory : Type*} {width : Nat}

structure Frame (Node Answer : Type*) (width : Nat) where
  capture : Preparation.Capture Node Answer
  charges : List (ScopedChargeReceipt width)
  deriving DecidableEq

def observe
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (memory : Memory × (Nat → State width)) (node : Node)
    (emission : Option Answer) (generated : List Node) : Frame Node Answer width :=
  ⟨⟨node, emission, generated⟩,
    (commands memory.1 node emission generated).map ScopedCharge.receipt⟩

/-- Refusal changes no checkpoint. A structurally acceptable capture still
needs its full primitive phase, including administrative operations and
per-destination storage decisions, before this adapter accepts it. -/
def step? [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width)))
    (frame : Frame Node Answer width) :
    Option (Snapshot Node Answer (Memory × (Nat → State width))) :=
  match Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step? system
      (scopedController maximum base commands initialStore) snapshot frame.capture with
  | none => none
  | some result =>
      if frame.charges = (commands snapshot.memory.1 frame.capture.input
          frame.capture.emission frame.capture.generated).map ScopedCharge.receipt then
        some result else none

theorem step?_core [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (snapshot result : Snapshot Node Answer (Memory × (Nat → State width)))
    (frame : Frame Node Answer width)
    (accepted : step? maximum system base commands initialStore snapshot frame = some result) :
    Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step? system
      (scopedController maximum base commands initialStore) snapshot frame.capture = some result := by
  unfold step? at accepted
  cases checked : Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step? system
      (scopedController maximum base commands initialStore) snapshot frame.capture with
  | none => simp [checked] at accepted
  | some after =>
      simp only [checked] at accepted
      split at accepted
      · exact accepted
      · cases accepted

theorem step?_sound [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (snapshot result : Snapshot Node Answer (Memory × (Nat → State width)))
    (frame : Frame Node Answer width)
    (accepted : step? maximum system base commands initialStore snapshot frame = some result) :
    result = Snapshot.tick system (scopedController maximum base commands initialStore) snapshot := by
  exact Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step?_sound
    system (scopedController maximum base commands initialStore) snapshot result frame.capture
    (step?_core maximum system base commands initialStore snapshot result frame accepted)

theorem step?_phase [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (snapshot result : Snapshot Node Answer (Memory × (Nat → State width)))
    (frame : Frame Node Answer width)
    (accepted : step? maximum system base commands initialStore snapshot frame = some result) :
    frame.charges = (commands snapshot.memory.1 frame.capture.input
      frame.capture.emission frame.capture.generated).map ScopedCharge.receipt := by
  unfold step? at accepted
  cases checked : Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step? system
      (scopedController maximum base commands initialStore) snapshot frame.capture with
  | none => simp [checked] at accepted
  | some after =>
      simp only [checked] at accepted
      split at accepted
      · assumption
      · cases accepted

/-- Validation consumes the existing replay steps. A mismatched frame
retains the entire current checkpoint and all its unconsumed metadata. -/
def run [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) :
    List (Frame Node Answer width) → Snapshot Node Answer (Memory × (Nat → State width)) →
      Except (Snapshot Node Answer (Memory × (Nat → State width)) × List (Frame Node Answer width))
        (Snapshot Node Answer (Memory × (Nat → State width)))
  | [], snapshot => .ok snapshot
  | frame :: rest, snapshot =>
      match step? maximum system base commands initialStore snapshot frame with
      | none => .error (snapshot, frame :: rest)
      | some after => run maximum system base commands initialStore rest after

theorem run_append [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (first second : List (Frame Node Answer width))
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width))) :
    run maximum system base commands initialStore (first ++ second) snapshot =
      match run maximum system base commands initialStore first snapshot with
      | .ok cut => run maximum system base commands initialStore second cut
      | .error (cut, pending) => .error (cut, pending ++ second) := by
  induction first generalizing snapshot with
  | nil => rfl
  | cons frame rest ih =>
      simp only [List.cons_append, run]
      cases step? maximum system base commands initialStore snapshot frame with
      | none => rfl
      | some after => exact ih after

/-- Erasing the additional phase metadata yields the existing core replay
over the same complete checkpoint. No replacement scheduler is involved. -/
theorem run_core [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (frames : List (Frame Node Answer width))
    (snapshot result : Snapshot Node Answer (Memory × (Nat → State width)))
    (accepted : run maximum system base commands initialStore frames snapshot = .ok result) :
    Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.run system
      (scopedController maximum base commands initialStore) (frames.map Frame.capture) snapshot = .ok result := by
  induction frames generalizing snapshot with
  | nil =>
      cases (Except.ok.inj accepted)
      rfl
  | cons frame rest ih =>
      simp only [run] at accepted
      cases checked : step? maximum system base commands initialStore snapshot frame with
      | none => simp [checked] at accepted
      | some after =>
          rw [List.map_cons, Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.run,
            step?_core maximum system base commands initialStore snapshot after frame checked]
          exact ih after (by simpa only [checked] using accepted)

/-- Every accepted phase returns the independently defined cost-bearing
controller run, including its complete search, continuation and meter store. -/
theorem run_sound [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (frames : List (Frame Node Answer width))
    (snapshot result : Snapshot Node Answer (Memory × (Nat → State width)))
    (accepted : run maximum system base commands initialStore frames snapshot = .ok result) :
    result = Snapshot.run system (scopedController maximum base commands initialStore)
      frames.length snapshot := by
  simpa only [List.length_map] using
    Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.run_sound system
      (scopedController maximum base commands initialStore) (frames.map Frame.capture) snapshot result
      (run_core maximum system base commands initialStore frames snapshot result accepted)

theorem run_refused [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (frames pending : List (Frame Node Answer width))
    (snapshot cut : Snapshot Node Answer (Memory × (Nat → State width)))
    (refused : run maximum system base commands initialStore frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Snapshot.run system (scopedController maximum base commands initialStore)
        acceptedFrames.length snapshot ∧
      step? maximum system base commands initialStore cut frame = none := by
  induction frames generalizing snapshot with
  | nil => cases refused
  | cons frame rest ih =>
      simp only [run] at refused
      cases checked : step? maximum system base commands initialStore snapshot frame with
      | none =>
          simp only [checked] at refused
          cases Except.error.inj refused
          exact ⟨[], frame, rest, rfl, rfl, rfl, checked⟩
      | some after =>
          obtain ⟨acceptedFrames, rejected, remaining, partition, pendingEq, state, invalid⟩ :=
            ih after (by simpa only [checked] using refused)
          refine ⟨frame :: acceptedFrames, rejected, remaining, by simp [partition], pendingEq, ?_, invalid⟩
          rw [step?_sound maximum system base commands initialStore snapshot after frame checked] at state
          have splitRun := Snapshot.run_add system (scopedController maximum base commands initialStore)
            1 acceptedFrames.length snapshot
          simpa only [List.length_cons, Nat.add_comm 1, Snapshot.run] using state.trans splitRun.symm

theorem run_next [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width)
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width))) :
    run maximum system base commands initialStore
      (next system (scopedController maximum base commands initialStore) (observe commands) snapshot).toList
      snapshot = .ok (Snapshot.tick system (scopedController maximum base commands initialStore) snapshot) := by
  cases order : ((scopedController maximum base commands initialStore).scheduler snapshot.memory).reorder
      snapshot.search.frontier with
  | nil =>
      simp [next, order, run, Snapshot.tick, Mettapedia.GSLT.Core.BranchingTemporal.tick]
  | cons node pending =>
      simp only [next, List.head?_cons, Option.map_some, Option.toList_some, run,
        step?, Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step?, order,
        observe, Preparation.capture, ↓reduceIte]
      simp only [Snapshot.tick, Mettapedia.GSLT.Core.BranchingTemporal.tick, order]
      cases system.emit node <;> rfl

theorem run_stream [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (fuel : Nat)
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width))) :
    run maximum system base commands initialStore
      (stream system (scopedController maximum base commands initialStore) (observe commands) fuel snapshot)
      snapshot = .ok (Snapshot.run system (scopedController maximum base commands initialStore) fuel snapshot) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [stream, run_append, ih]
      exact run_next maximum system base commands initialStore _

def readout [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (record : Prefix (Frame Node Answer width))
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width))) :=
  record.complete?.map (fun frames => run maximum system base commands initialStore frames snapshot)

theorem readout_truncated [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (record : Prefix (Frame Node Answer width))
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width)))
    (omitted : record.omitted ≠ 0) :
    readout maximum system base commands initialStore record snapshot = none := by
  simp [readout, Prefix.complete?, omitted]

/-- A complete bounded recording validates its primitive phases and
reconstructs the actual whole controlled run at the held starting boundary. -/
theorem recorded_replay [DecidableEq Node] [DecidableEq Answer]
    (maximum : Nat) (system : BranchingSystem Node Answer)
    (base : Controller Node Answer Memory)
    (commands : Memory → Node → Option Answer → List Node → List (ScopedCharge width))
    (initialStore : Nat → State width) (capacity fuel : Nat)
    (snapshot : Snapshot Node Answer (Memory × (Nat → State width)))
    (fits : (stream system (scopedController maximum base commands initialStore)
      (observe commands) fuel snapshot).length ≤ capacity) :
    ((Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore) (observe commands) (some capacity)) fuel
      (Mettapedia.GSLT.Core.InferenceControl.Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => readout maximum system base commands initialStore record snapshot) =
      some (.ok (Snapshot.run system (scopedController maximum base commands initialStore) fuel snapshot)) := by
  have complete := (Mettapedia.GSLT.Core.InferenceControl.Recording.complete_record_iff system
    (scopedController maximum base commands initialStore) (observe commands) capacity fuel snapshot).mpr fits
  cases retained : (Snapshot.run system
      (Mettapedia.GSLT.Core.InferenceControl.Recording.controller
        (scopedController maximum base commands initialStore) (observe commands) (some capacity)) fuel
      (Mettapedia.GSLT.Core.InferenceControl.Recording.start snapshot (some capacity))).memory.2 with
  | none => simp [retained] at complete
  | some record =>
      simp only [retained, Option.bind_some] at complete ⊢
      simp [readout, complete, run_stream]

end PhaseReplay

namespace ControllerControls

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl (Controller Snapshot)

private def source : BranchingSystem Nat Nat where
  emit _ := some 7
  successors _ := []

private def base : Controller Nat Nat Nat where
  initialMemory := 0
  scheduler _ := Scheduler.breadthFirst
  advance memory _ _ _ := memory + 1

/-- This service transcript has one restore and one coordinator operation
per selected leaf, followed by its accepted publication. The coordinator
has occurrence zero; this does not identify it with the selected leaf. -/
private def commands (memory node : Nat) (_ : Option Nat) (_ : List Nat) :
    List (ScopedCharge 8) :=
  [⟨[some 4, none, some 4, some 9], ⟨3 * memory + 1, 12, node, .restore, 1, true⟩,
      fun location => decide (location ≠ 9)⟩,
   ⟨[some 4, none, some 4, some 9], ⟨3 * memory + 2, 12, 0, .quantum, 1, true⟩,
      fun location => decide (location ≠ 9)⟩,
   ⟨[some 4, none, some 4, some 9], ⟨3 * memory + 3, 12, node, .publish, 1, true⟩,
      fun location => decide (location ≠ 9)⟩]

private def controller :=
  Mettapedia.GSLT.Core.InferenceControl.Recording.controller
    (scopedController 255 base commands (fun _ => initial 8))
    (fun memory node _ _ => (memory.1, node)) (some 1)

private def start := Snapshot.initial controller [5, 8]

/-- One prefix retains the remaining leaf, source controller memory,
bounded recording and both numerical destinations. Losing event storage at
one destination does not stop that destination's accounting. -/
theorem prefix_retains_complete_state :
    let cut := Snapshot.run source controller 1 start
    cut.search.events = [⟨5, 7⟩] ∧ cut.search.frontier = [8] ∧ cut.memory.1.1 = 1 ∧
      (cut.memory.1.2 4).work.toNat = 3 ∧ (cut.memory.1.2 9).work.toNat = 3 ∧
      (cut.memory.1.2 9).traceIncomplete = true ∧ (cut.memory.1.2 9).history = [] ∧
      cut.memory.2 = some ⟨[(0, 5)], 0, 0⟩ := by
  decide

/-- The resumed prefix retains both equal-value emissions, six distinct
physical charges and the full recorder's omission. Duplicate containing
scopes do not multiply those charges, and unrelated destinations stay zero. -/
theorem resumed_record_and_accounts :
    let after := Snapshot.run source controller 1 (Snapshot.run source controller 1 start)
    after.search.events = [⟨5, 7⟩, ⟨8, 7⟩] ∧ after.search.frontier = [] ∧
      after.memory.1.1 = 2 ∧ (after.memory.1.2 4).work.toNat = 6 ∧
      (after.memory.1.2 9).work.toNat = 6 ∧ (after.memory.1.2 5).work.toNat = 0 ∧
      after.memory.2 = some ⟨[(0, 5)], 0, 1⟩ ∧
      RunLengthEvents.expand (after.memory.1.2 4).history =
        [(1, ⟨12, 5, .restore, 1⟩), (2, ⟨12, 0, .quantum, 1⟩),
         (3, ⟨12, 5, .publish, 1⟩), (4, ⟨12, 8, .restore, 1⟩),
         (5, ⟨12, 0, .quantum, 1⟩), (6, ⟨12, 8, .publish, 1⟩)] := by
  decide

/-- Equality is of the whole functional store and checkpoint, including
the incomplete destination and remaining recorder state. -/
theorem split_preserves_whole_store :
    Snapshot.run source controller 2 start =
      Snapshot.run source controller 1 (Snapshot.run source controller 1 start) :=
  Snapshot.run_add source controller 1 1 start

/-- Resetting only the cost store on resumption preserves the two answers
but reports three operations instead of six. Answer agreement cannot
establish account preservation. -/
theorem resetting_store_loses_charges :
    let cut := Snapshot.run source controller 1 start
    let reset := { cut with memory := ((cut.memory.1.1, fun _ => initial 8), cut.memory.2) }
    let good := Snapshot.run source controller 1 cut
    let bad := Snapshot.run source controller 1 reset
    good.search.events = bad.search.events ∧ (good.memory.1.2 4).work.toNat = 6 ∧
      (bad.memory.1.2 4).work.toNat = 3 := by
  decide

/-- Replenishing only recorder capacity also preserves the answers and
numerical account. It nevertheless invents a complete retained history at
the captured start where the original bounded observer has an omission. -/
theorem replenishing_record_hides_omission :
    let cut := Snapshot.run source controller 1 start
    let reset := { cut with memory :=
      (cut.memory.1, Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 1)) }
    let good := Snapshot.run source controller 1 cut
    let bad := Snapshot.run source controller 1 reset
    good.search.events = bad.search.events ∧
      (good.memory.1.2 4).work = (bad.memory.1.2 4).work ∧
      good.memory.2 = some ⟨[(0, 5)], 0, 1⟩ ∧ bad.memory.2 = some ⟨[(1, 8)], 0, 0⟩ := by
  decide

/-- Removing coordinator charges keeps the authored answers and all
selected-leaf restores/publications. It changes the declared metric, even
though those administrative operations have no selected-leaf occurrence. -/
theorem omitting_administrative_quantum_changes_account :
    let incomplete := scopedController 255 base
      (fun memory node answer generated =>
        (commands memory node answer generated).filter (fun command => command.charge.kind != .quantum))
      (fun _ => initial 8)
    let missing := Snapshot.run source incomplete 2 (Snapshot.initial incomplete [5, 8])
    let complete := Snapshot.run source controller 2 start
    complete.search.events = missing.search.events ∧
      (complete.memory.1.2 4).work.toNat = 6 ∧ (missing.memory.2 4).work.toNat = 4 := by
  decide

/-- A selected-input transcript does not authenticate its starting account.
Replaying at another captured meter returns the same two answers with ten
additional prior operations. The full starting checkpoint must be retained. -/
theorem different_starting_account_changes_replay :
    let plain := scopedController 255 base commands (fun _ => initial 8)
    let beginning := Snapshot.initial plain [5, 8]
    let frames := Mettapedia.GSLT.Core.InferenceControl.Recording.stream source plain
      Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.observe 2 beginning
    let other := { beginning with memory :=
      (beginning.memory.1, fun location => if location = 4 then
        append 255 (initial 8) ⟨90, 12, 0, .matchNode, 10, true⟩ else beginning.memory.2 location) }
    match Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.run source plain frames other with
    | .error _ => False
    | .ok replayed => replayed.search.events = [⟨5, 7⟩, ⟨8, 7⟩] ∧
        (replayed.memory.2 4).work.toNat = 16 ∧
        ((Snapshot.run source plain 2 beginning).memory.2 4).work.toNat = 6 := by
  dsimp [Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.run,
    Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step?,
    Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.observe,
    Mettapedia.GSLT.Core.InferenceControl.Recording.stream,
    Mettapedia.GSLT.Core.InferenceControl.Recording.next,
    Mettapedia.GSLT.Core.InferenceControl.Preparation.capture,
    Snapshot.initial, Snapshot.tick, Snapshot.run,
    Mettapedia.GSLT.Core.BranchingTemporal.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.tick,
    scopedController, Controller.observing, source, base, Scheduler.breadthFirst]
  decide

end ControllerControls

namespace PhaseReplayControls

open Mettapedia.GSLT.Core.InferenceControl (Snapshot)

private def control := scopedController 255 ControllerControls.base ControllerControls.commands
  (fun _ => initial 8)

private def start := Snapshot.initial control [5, 8]

private def first : PhaseReplay.Frame Nat Nat 8 :=
  PhaseReplay.observe ControllerControls.commands (0, fun _ => initial 8) 5 (some 7) []

private def second : PhaseReplay.Frame Nat Nat 8 :=
  PhaseReplay.observe ControllerControls.commands (1, fun _ => initial 8) 8 (some 7) []

private def omitted (frame : PhaseReplay.Frame Nat Nat 8) :=
  { frame with charges := frame.charges.filter (fun command => command.charge.kind != Kind.quantum) }

/-- Two equal answers remain separate occurrences. A refused destination
still counts all six operations and keeps its incomplete history. -/
theorem complete_phases_retain_occurrences_and_accounts :
    match PhaseReplay.run 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8) [first, second] start with
    | .error _ => False
    | .ok after => after.search.events = [⟨5, 7⟩, ⟨8, 7⟩] ∧ after.search.frontier = [] ∧
        after.memory.1 = 2 ∧ (after.memory.2 4).work.toNat = 6 ∧
        (after.memory.2 9).work.toNat = 6 ∧ (after.memory.2 9).traceIncomplete = true ∧
        (RunLengthEvents.expand (after.memory.2 4).history).map Prod.fst = [1, 2, 3, 4, 5, 6] := by
  dsimp [PhaseReplay.run, PhaseReplay.step?, first, second, start, control,
    PhaseReplay.observe, Mettapedia.GSLT.Core.InferenceControl.Recording.Replay.step?,
    Mettapedia.GSLT.Core.InferenceControl.Preparation.capture,
    Snapshot.initial, Snapshot.tick, Mettapedia.GSLT.Core.BranchingTemporal.initial,
    Mettapedia.GSLT.Core.BranchingTemporal.tick, scopedController,
    Mettapedia.GSLT.Core.InferenceControl.Controller.observing,
    ControllerControls.source, ControllerControls.base,
    Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst]
  decide

/-- The capture still names the authorized emission. Omitting an
administrative operation nevertheless prevents account authentication. -/
theorem omitted_quantum_refused :
    (omitted first).capture = first.capture ∧
      PhaseReplay.step? 255 ControllerControls.source ControllerControls.base
        ControllerControls.commands (fun _ => initial 8) start (omitted first) = none := by
  exact ⟨rfl, rfl⟩

theorem duplicated_charge_refused :
    PhaseReplay.step? 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8) start
        { first with charges := first.charges ++ first.charges.take 1 } = none := by
  rfl

/-- Reordering retains the numerical work sum, but changes the named
chronological phase. A sum is insufficient replay evidence. -/
theorem reordered_same_sum_refused :
    (runScopes 255 (ControllerControls.commands 0 5 (some 7) []).reverse
      (fun _ => initial 8) 4).work.toNat = 3 ∧
      (runScopes 255 (ControllerControls.commands 0 5 (some 7) [])
        (fun _ => initial 8) 4).work.toNat = 3 ∧
      PhaseReplay.step? 255 ControllerControls.source ControllerControls.base
        ControllerControls.commands (fun _ => initial 8) start
          { first with charges := first.charges.reverse } = none := by
  exact ⟨by decide, by decide, rfl⟩

theorem changed_retention_refused :
    PhaseReplay.step? 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8) start
        { first with charges := first.charges.map fun command =>
          { command with retention := command.retention.map fun entry =>
            if entry.1 = 9 then (9, true) else entry } } = none := by
  rfl

/-- Equal-looking ledger identities cannot replace a physical containing
location. Full scope chains are part of the checked phase. -/
theorem changed_destination_refused :
    PhaseReplay.step? 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8) start
        { first with charges := first.charges.map fun command =>
          { command with scopes := [some 4, none, some 5, some 9] } } = none := by
  rfl

/-- The accepted prefix's entire meter and continuation survive the denied
second phase. The same rejected payload remains available for correction. -/
theorem refusal_retains_paid_prefix :
    PhaseReplay.run 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8) [first, omitted second] start =
      .error (Snapshot.tick ControllerControls.source control start, [omitted second]) := by
  rfl

theorem bounded_recording_does_not_invent_complete_replay :
    PhaseReplay.readout 255 ControllerControls.source ControllerControls.base
      ControllerControls.commands (fun _ => initial 8)
      ((Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.initial 1).append [first, second])
      start = none := by
  rfl

end PhaseReplayControls

/-- A read captures the preceding observation before its temporary scope
is entered. Re-entering the same location in an outer frame does not charge
the read twice; a null read has a zero preceding observation and origin. -/
def inspectScopes (maximum : Nat) (store : Nat → State 64) (location : Option Nat)
    (outer : List (Option Nat)) (identity origin occurrence : Nat) (retained : Nat → Bool) :
    Observation × (Nat → State 64) :=
  let before := observe (location.map store |>.getD (initial 64 true))
  let charge := readCharge identity (if location.isSome then origin else 0) occurrence true
  (before, chargeScopes maximum (location :: outer) charge retained store)

theorem inspectScopes_preceding (maximum : Nat) (store : Nat → State 64) (location : Option Nat)
    (outer : List (Option Nat)) (identity origin occurrence : Nat) (retained : Nat → Bool) :
    (inspectScopes maximum store location outer identity origin occurrence retained).1 =
      observe (location.map store |>.getD (initial 64 true)) := rfl

/-- A live read agrees with the existing single-ledger inspection, while
the other containing scopes still receive the same physical read event. -/
theorem inspectScopes_at_read_location (maximum : Nat) (store : Nat → State 64) (location : Nat)
    (outer : List (Option Nat)) (identity origin occurrence : Nat) (retained : Nat → Bool) :
    ((inspectScopes maximum store (some location) outer identity origin occurrence retained).1,
      (inspectScopes maximum store (some location) outer identity origin occurrence retained).2 location) =
      inspect maximum (store location) identity origin occurrence (retained location) := by
  simp only [inspectScopes, Option.map_some, Option.getD_some, inspect]
  rw [chargeScopes_at, if_pos (List.mem_cons_self)]
  rfl

/-- The prefix scan's location equality, not an origin-identity equality,
preserves distinct views even when the origin allocator is exhausted. -/
theorem scoped_origin_exhaustion_control :
    let charge : Charge 8 := ⟨8, 0, 30, .heapLookup, 1, true⟩
    let store : Nat → State 8 := fun _ => initial 8
    let after := chargeScopes 255 [some 4, none, some 9, some 4] charge (fun _ => true) store
    (after 4).work.toNat = 1 ∧ (after 9).work.toNat = 1 ∧ (after 5).work.toNat = 0 ∧
      RunLengthEvents.expand (after 4).history = [charge.event] ∧
      RunLengthEvents.expand (after 9).history = [charge.event] := by
  decide

/-- One destination's failed storage leaves another destination complete;
both numerical counters still count the physical operation. -/
theorem scoped_retention_control :
    let charge : Charge 8 := ⟨8, 12, 30, .heapLookup, 1, true⟩
    let store : Nat → State 8 := fun _ => initial 8
    let after := chargeScopes 255 [some 4, some 9, some 4] charge (fun loc => decide (loc ≠ 4)) store
    (after 4).work.toNat = 1 ∧ (after 9).work.toNat = 1 ∧
      (after 4).traceIncomplete = true ∧ (after 4).history = [] ∧
      (after 9).traceIncomplete = false ∧ RunLengthEvents.expand (after 9).history = [charge.event] := by
  decide

/-- A duplicate-scope mutant double-charges a physical event. The actual
scope delivery preserves one charge without equating the duplicate frames. -/
theorem scoped_duplicate_delivery_control :
    let charge : Charge 8 := ⟨8, 12, 30, .heapLookup, 1, true⟩
    let store : Nat → State 8 := fun _ => initial 8
    (deliver 255 (fun _ => charge) [4, 4] store 4).work.toNat = 2 ∧
      (chargeScopes 255 [some 4, some 4] charge (fun _ => true) store 4).work.toNat = 1 := by
  decide

/-- Reading before charging cannot be replaced by a post-charge read.
Outer aliases receive the same read once and no unrelated ledger changes. -/
theorem scoped_read_order_control :
    let store : Nat → State 64 := fun _ => initial 64
    let read := inspectScopes 255 store (some 4) [some 9, none, some 4] 8 12 30 (fun _ => true)
    read.1.work = 0 ∧ (observe (read.2 4)).work = 1 ∧
      (read.2 9).work.toNat = 1 ∧ (read.2 5).work.toNat = 0 ∧
      read.1 ≠ observe (read.2 4) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro equal
  have wrong := congrArg Observation.work equal
  change (0 : Nat) = 1 at wrong
  exact Nat.zero_ne_one wrong

/-- A captured accounting context. The scope list is inner-to-outer and
contains live locations with each frame's occurrence. Origin identifiers
and destination locations remain distinct namespaces. Retention decisions
are supplied by the storage service for this operation. -/
structure ScopeState (width : Nat) where
  scopes : List (Option Nat × Nat)
  origins : Nat → Nat
  nextIdentity : Nat
  store : Nat → State width
  retained : Nat → Bool

/-- Construct the shared payload from the innermost frame. A null inner
ledger contributes origin zero even when outer live ledgers receive work. -/
def scopeCharge {width : Nat} (state : ScopeState width) (kind : Kind)
    (units : BitVec width) (identity : Nat) : Charge width :=
  let inner := state.scopes.headD (none, 0)
  ⟨identity, inner.1.map state.origins |>.getD 0, inner.2, kind, units, true⟩

/-- Observe a valid operation after its identity reservation linearizes.
Disabled observation and zero work reserve no identity. Refusal returns zero
but still charges active views and makes their missing history explicit.
Weak-CAS completion and physical scope/allocator realization are separate
from this captured-context execution. -/
def observeScopes {width : Nat} (runMaximum identityMaximum : Nat)
    (state : ScopeState width) (kind : Kind) (units : BitVec width) : Nat × ScopeState width :=
  if state.scopes = [] ∨ units = 0 then (0, state) else
    let reserved := OccurrenceIdentity.reserve identityMaximum state.nextIdentity
    let identity := reserved.1.getD 0
    let charge := scopeCharge state kind units identity
    (identity, { state with
      nextIdentity := reserved.2
      store := chargeScopes runMaximum (state.scopes.map Prod.fst) charge state.retained state.store })

theorem observeScopes_disabled {width : Nat} (runMaximum identityMaximum : Nat)
    (state : ScopeState width) (kind : Kind) (units : BitVec width) (disabled : state.scopes = []) :
    observeScopes runMaximum identityMaximum state kind units = (0, state) := by
  simp only [observeScopes, disabled, true_or, if_true]

theorem observeScopes_zero {width : Nat} (runMaximum identityMaximum : Nat)
    (state : ScopeState width) (kind : Kind) :
    observeScopes runMaximum identityMaximum state kind 0 = (0, state) := by
  simp only [observeScopes, or_true, if_true]

/-- The per-view numerical law is independent of successful issuance or
retention. The reserved identifier is not used as a destination key. -/
theorem observeScopes_work {width : Nat} (runMaximum identityMaximum : Nat)
    (state : ScopeState width) (kind : Kind) (units : BitVec width)
    (active : state.scopes ≠ []) (nonzero : units ≠ 0) (location : Nat) :
    ((observeScopes runMaximum identityMaximum state kind units).2.store location).work.toNat =
      boundedTotal (2 ^ width - 1) ((state.store location).work.toNat +
        if some location ∈ state.scopes.map Prod.fst then units.toNat else 0) := by
  simp only [observeScopes, active, nonzero, false_or, if_false]
  exact chargeScopes_work runMaximum _ _ _ _ location

/-- An issued identifier is positive, below the namespace sentinel and
advances its retained counter once. This follows from the independent
reservation algorithm, not an assumed freshness tag on the event. -/
theorem observeScopes_issued {width : Nat} (runMaximum identityMaximum : Nat)
    (state : ScopeState width) (kind : Kind) (units : BitVec width)
    (active : state.scopes ≠ []) (nonzero : units ≠ 0)
    (available : 0 < state.nextIdentity ∧ state.nextIdentity < identityMaximum) :
    (observeScopes runMaximum identityMaximum state kind units).1 = state.nextIdentity ∧
      (observeScopes runMaximum identityMaximum state kind units).2.nextIdentity =
        state.nextIdentity + 1 ∧
      0 < (observeScopes runMaximum identityMaximum state kind units).1 ∧
      (observeScopes runMaximum identityMaximum state kind units).1 < identityMaximum := by
  have reserved := (OccurrenceIdentity.reserve_issued_iff identityMaximum
    state.nextIdentity state.nextIdentity (state.nextIdentity + 1)).mpr
      ⟨available.1, available.2, rfl, rfl⟩
  simp only [observeScopes, active, nonzero, false_or, if_false, reserved, Option.getD_some]
  exact ⟨trivial, trivial, available.1, available.2⟩

/-- Missing event identity does not silently make an observed operation
free. No destination retains an event with the refusal sentinel as a name. -/
theorem scoped_identity_refusal_control :
    let state : ScopeState 8 := ⟨[(some 4, 30), (some 9, 31)], fun _ => 12,
      7, fun _ => initial 8, fun _ => true⟩
    let result := observeScopes 255 7 state .heapLookup 1
    result.1 = 0 ∧ result.2.nextIdentity = 7 ∧
      (result.2.store 4).work.toNat = 1 ∧ (result.2.store 9).work.toNat = 1 ∧
      (result.2.store 4).traceIncomplete = true ∧ (result.2.store 4).history = [] ∧
      (result.2.store 9).traceIncomplete = true ∧ (result.2.store 9).history = [] := by
  decide

/-- The innermost frame supplies occurrence and origin, rather than the
first non-null destination. Both outer views retain the same event. -/
theorem scoped_null_inner_control :
    let state : ScopeState 8 := ⟨[(none, 30), (some 4, 31), (some 9, 32), (some 4, 33)],
      fun _ => 12, 8, fun _ => initial 8, fun _ => true⟩
    let result := observeScopes 255 255 state .heapLookup 1
    result.1 = 8 ∧ result.2.nextIdentity = 9 ∧
      RunLengthEvents.expand (result.2.store 4).history = [(8, ⟨0, 30, .heapLookup, 1⟩)] ∧
      RunLengthEvents.expand (result.2.store 9).history = [(8, ⟨0, 30, .heapLookup, 1⟩)] := by
  decide

/-- Import the numerical coordinates of a child whose chronological receipt
is incomplete. The retained parent prefix is left intact, while each counter
is saturated independently. Sequential span is restored from the declared
schedule after all child imports; this fallback itself does not add span.
The complete C record loop and its memory representation remain separate
correspondence obligations. -/
def importIncomplete {width : Nat} (parent child : State width) : State width :=
  let countOverflow := decide (∃ kind : Kind,
    2 ^ width - 1 < (parent.counts kind).toNat + (child.counts kind).toNat)
  let worked := wordAddLowerBound parent.work child.work (parent.overflow || countOverflow)
  { counts := fun kind => (wordAddLowerBound (parent.counts kind) (child.counts kind) false).1
    work := worked.1
    span := parent.span
    parallel := parent.parallel || child.parallel
    overflow := worked.2 || child.overflow
    traceIncomplete := true
    history := parent.history }

theorem importIncomplete_work {width : Nat} (parent child : State width) :
    (importIncomplete parent child).work.toNat =
      boundedTotal (2 ^ width - 1) (parent.work.toNat + child.work.toNat) := by
  rw [importIncomplete, wordAddLowerBound_value,
    addLowerBound_value _ _ _ (word_fits parent.work)]

theorem importIncomplete_count {width : Nat} (parent child : State width) (kind : Kind) :
    ((importIncomplete parent child).counts kind).toNat =
      boundedTotal (2 ^ width - 1)
        ((parent.counts kind).toNat + (child.counts kind).toNat) := by
  rw [importIncomplete, wordAddLowerBound_value,
    addLowerBound_value _ _ _ (word_fits (parent.counts kind))]

theorem importIncomplete_history {width : Nat} (parent child : State width) :
    (importIncomplete parent child).history = parent.history := rfl

theorem importIncomplete_span {width : Nat} (parent child : State width) :
    (importIncomplete parent child).span = parent.span := rfl

theorem importIncomplete_incomplete {width : Nat} (parent child : State width) :
    (importIncomplete parent child).traceIncomplete = true := rfl

theorem importIncomplete_overflow {width : Nat} (parent child : State width)
    (overflow : parent.overflow = true) :
    (importIncomplete parent child).overflow = true := by
  simp [importIncomplete, overflow, word_overflow_is_sticky]

theorem importIncomplete_child_overflow {width : Nat} (parent child : State width)
    (overflow : child.overflow = true) :
    (importIncomplete parent child).overflow = true := by
  simp [importIncomplete, overflow]

/-- Logical import order remains part of the accumulator. A missing child
history never authorizes reinitializing the parent's counters or receipt. -/
def importIncompleteChildren {width : Nat} : List (State width) → State width → State width
  | [], parent => parent
  | child :: rest, parent => importIncompleteChildren rest (importIncomplete parent child)

theorem importIncompleteChildren_append {width : Nat} (first second : List (State width))
    (parent : State width) :
    importIncompleteChildren (first ++ second) parent =
      importIncompleteChildren second (importIncompleteChildren first parent) := by
  induction first generalizing parent with
  | nil => rfl
  | cons child rest ih => exact ih _

theorem importIncompleteChildren_work {width : Nat} (children : List (State width))
    (parent : State width) :
    (importIncompleteChildren children parent).work.toNat =
      boundedTotal (2 ^ width - 1)
        (parent.work.toNat + (children.map fun child => child.work.toNat).sum) := by
  induction children generalizing parent with
  | nil => simp [importIncompleteChildren, boundedTotal,
      Nat.min_eq_right (word_fits parent.work)]
  | cons child rest ih =>
      rw [importIncompleteChildren, ih, importIncomplete_work, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem importIncompleteChildren_count {width : Nat} (children : List (State width))
    (parent : State width) (kind : Kind) :
    ((importIncompleteChildren children parent).counts kind).toNat =
      boundedTotal (2 ^ width - 1) ((parent.counts kind).toNat +
        (children.map fun child => (child.counts kind).toNat).sum) := by
  induction children generalizing parent with
  | nil => simp [importIncompleteChildren, boundedTotal,
      Nat.min_eq_right (word_fits (parent.counts kind))]
  | cons child rest ih =>
      rw [importIncompleteChildren, ih, importIncomplete_count, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem importIncompleteChildren_history {width : Nat} (children : List (State width))
    (parent : State width) :
    (importIncompleteChildren children parent).history = parent.history := by
  induction children generalizing parent with
  | nil => rfl
  | cons child rest ih => exact (ih _).trans (importIncomplete_history _ _)

theorem importIncompleteChildren_span {width : Nat} (children : List (State width))
    (parent : State width) :
    (importIncompleteChildren children parent).span = parent.span := by
  induction children generalizing parent with
  | nil => rfl
  | cons child rest ih => exact (ih _).trans (importIncomplete_span _ _)

theorem importIncompleteChildren_incomplete {width : Nat} (children : List (State width))
    (parent : State width) (nonempty : children ≠ []) :
    (importIncompleteChildren children parent).traceIncomplete = true := by
  induction children generalizing parent with
  | nil => exact False.elim (nonempty rfl)
  | cons child rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail => exact ih (importIncomplete parent child) (by simp)

/-- Existing phase/lane/slice cost algebra, read through the child's
independent numerical counters. History completeness is not required for
this view. Execution and child-owner admission still justify the schedule. -/
def workerSchedule {width : Nat} (phases : List (List (List (State width)))) : WorkSpan :=
  ParallelCrossover.workerPhases
    (phases.map fun phase => phase.map fun lane => lane.map fun child =>
      ⟨child.work.toNat, child.span.toNat⟩)

theorem workerSchedule_work {width : Nat} (phases : List (List (List (State width)))) :
    (workerSchedule phases).work =
      (phases.flatten.flatten.map fun child => child.work.toNat).sum := by
  rw [workerSchedule, ParallelCrossover.workerPhases_work_flatten]
  simp only [List.map_flatten, List.map_map, Function.comp_def]

theorem workerSchedule_span {width : Nat} (phases : List (List (List (State width)))) :
    (workerSchedule phases).span =
      (phases.map fun phase =>
        (phase.map fun lane => (lane.map fun child => child.span.toNat).sum).foldr max 0).sum := by
  rw [workerSchedule, ParallelCrossover.workerPhases_span]
  simp only [List.map_map, Function.comp_def]

/-- Empty lanes represent idle workers, rather than a second admitted
child owner. A zero-cost child is still a child and retains its lane. -/
def multipleWorkers {width : Nat} (phases : List (List (List (State width)))) : Bool :=
  phases.any fun phase => 1 < (phase.filter fun lane => !lane.isEmpty).length

/-- After importing work, the declared causal schedule replaces the
temporary sequential span. Its bound is checked before conversion to a
machine word; inherited overflow and causal-span flags remain sticky. -/
def finishJoin {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) : State width :=
  let spanned := addLowerBound (2 ^ width - 1) precedingSpan.toNat (workerSchedule phases).span
  { imported with
    span := BitVec.ofNat width spanned.1
    overflow := imported.overflow || spanned.2
    parallel := imported.parallel || multipleWorkers phases }

private theorem addLowerBound_fits (maximum left right : Nat) (fits : left ≤ maximum) :
    (addLowerBound maximum left right).1 ≤ maximum := by
  rw [addLowerBound_value _ _ _ fits]
  exact Nat.min_le_left _ _

theorem finishJoin_span {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) :
    (finishJoin phases precedingSpan imported).span.toNat =
      boundedTotal (2 ^ width - 1) (precedingSpan.toNat + (workerSchedule phases).span) := by
  have bounded := addLowerBound_fits (2 ^ width - 1) precedingSpan.toNat
    (workerSchedule phases).span (word_fits precedingSpan)
  have positive := Nat.two_pow_pos width
  have strict : (addLowerBound (2 ^ width - 1) precedingSpan.toNat
      (workerSchedule phases).span).1 < 2 ^ width := by omega
  rw [finishJoin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt strict,
    addLowerBound_value _ _ _ (word_fits precedingSpan)]

theorem finishJoin_work {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) :
    (finishJoin phases precedingSpan imported).work = imported.work := rfl

theorem finishJoin_count {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) (kind : Kind) :
    (finishJoin phases precedingSpan imported).counts kind = imported.counts kind := rfl

theorem finishJoin_history {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) :
    (finishJoin phases precedingSpan imported).history = imported.history := rfl

theorem finishJoin_incomplete {width : Nat} (phases : List (List (List (State width))))
    (precedingSpan : BitVec width) (imported : State width) :
    (finishJoin phases precedingSpan imported).traceIncomplete = imported.traceIncomplete := rfl

/-- The all-incomplete-child profile uses the numerical fallback for
every admitted child, then retains the original parent's span prefix.
Mixed complete/incomplete imports and physical C memory are separate. -/
def joinIncomplete {width : Nat} (phases : List (List (List (State width))))
    (parent : State width) : State width :=
  finishJoin phases parent.span (importIncompleteChildren phases.flatten.flatten parent)

theorem joinIncomplete_work {width : Nat} (phases : List (List (List (State width))))
    (parent : State width) :
    (joinIncomplete phases parent).work.toNat =
      boundedTotal (2 ^ width - 1) (parent.work.toNat + (workerSchedule phases).work) := by
  rw [joinIncomplete, finishJoin_work, importIncompleteChildren_work, workerSchedule_work]

theorem joinIncomplete_count {width : Nat} (phases : List (List (List (State width))))
    (parent : State width) (kind : Kind) :
    ((joinIncomplete phases parent).counts kind).toNat =
      boundedTotal (2 ^ width - 1) ((parent.counts kind).toNat +
        (phases.flatten.flatten.map fun child => (child.counts kind).toNat).sum) := by
  rw [joinIncomplete, finishJoin_count, importIncompleteChildren_count]

theorem joinIncomplete_span {width : Nat} (phases : List (List (List (State width))))
    (parent : State width) :
    (joinIncomplete phases parent).span.toNat =
      boundedTotal (2 ^ width - 1) (parent.span.toNat +
        (phases.map fun phase =>
          (phase.map fun lane => (lane.map fun child => child.span.toNat).sum).foldr max 0).sum) := by
  rw [joinIncomplete, finishJoin_span, workerSchedule_span]

theorem joinIncomplete_history {width : Nat} (phases : List (List (List (State width))))
    (parent : State width) :
    (joinIncomplete phases parent).history = parent.history := by
  rw [joinIncomplete, finishJoin_history, importIncompleteChildren_history]

/-- The same ordered numerical child occurrences retain their work across
different phase and worker assignments. Their causal span can differ. -/
theorem joinIncomplete_work_eq_of_perm {width : Nat}
    (first second : List (List (List (State width)))) (parent : State width)
    (sameChildren : first.flatten.flatten.Perm second.flatten.flatten) :
    (joinIncomplete first parent).work = (joinIncomplete second parent).work := by
  apply BitVec.eq_of_toNat_eq
  rw [joinIncomplete_work, joinIncomplete_work, workerSchedule_work, workerSchedule_work,
    (sameChildren.map fun child => child.work.toNat).sum_eq]

/-- The fault-injected native control has two incomplete children with
work/span two and seven. Parallel placement keeps work nine and span seven;
one-worker placement keeps the same work and span nine. Empty histories
determine neither of these numerical coordinates. -/
theorem incomplete_join_placement_control :
    let left : State 8 := { initial 8 true with work := 2, span := 2 }
    let right : State 8 := { initial 8 true with work := 7, span := 7 }
    let parallel := joinIncomplete [[[left], [right]]] (initial 8)
    let sequential := joinIncomplete [[[left, right]]] (initial 8)
    parallel.work.toNat = 9 ∧ parallel.span.toNat = 7 ∧ parallel.parallel = true ∧
      sequential.work.toNat = 9 ∧ sequential.span.toNat = 9 ∧ sequential.parallel = false ∧
      parallel.traceIncomplete = true ∧ parallel.history = sequential.history := by
  decide

/-- Distinct child owners may have equal numerical coordinates. This
control concerns their accounting values; physical owner admission and
the subsequent causal-span update are separate boundaries. -/
theorem incomplete_child_import_control :
    let parent : State 8 :=
      { initial 8 with
        work := 5
        span := 3
        counts := fun kind => if kind = .publish then 5 else 0 }
    let child : State 8 :=
      { initial 8 true with
        work := 9
        span := 4
        parallel := true
        counts := fun kind => if kind = .publish then 9 else 0 }
    let joined := importIncompleteChildren [child, child] parent
    joined.work.toNat = 23 ∧ joined.span.toNat = 3 ∧
      (joined.counts .publish).toNat = 23 ∧ joined.traceIncomplete = true ∧
      joined.parallel = true ∧ joined.history = [] ∧
      joined.work.toNat ≠ (snapshot joined.history).2 := by
  decide

/-- A child import relates its existing receipt to actual replay inputs.
Storage-retention decisions may differ in the parent, but replay keeps
every event's identity, occurrence, kind and numerical increment. Numerical
agreement is required only when the child's history is complete. -/
structure Child (width : Nat) where
  state : State width
  replay : List (Charge width)
  measured : CompleteMeasured state
  replicated : state.traceIncomplete = false →
    events replay = RunLengthEvents.expand state.history

/-- Fresh execution supplies the accounting invariant. The caller may
provide distinct parent-retention decisions for the same copied events. -/
def Child.ofRun {width : Nat} (maximum : Nat) (executed replay : List (Charge width))
    (sameEvents : events replay = events executed) : Child width where
  state := run maximum executed (initial width)
  replay := replay
  measured := run_completeMeasured maximum executed
  replicated := fun complete => by
    have history := run_history_of_complete maximum executed (initial width) complete
    change RunLengthEvents.expand (run maximum executed (initial width)).history =
      [] ++ events executed at history
    rw [List.nil_append] at history
    exact sameEvents.trans history.symm

/-- Select the native import branch from the child's completeness flag.
A complete child replays its chronological operations through ordinary
append, including possible parent storage failure. An incomplete child
imports independent numerical coordinates and marks the missing history.
Child causal/overflow declarations survive either branch. -/
def importChild {width : Nat} (maximum : Nat) (parent : State width) (child : Child width) :
    State width :=
  let imported := if child.state.traceIncomplete then importIncomplete parent child.state
    else run maximum child.replay parent
  { imported with
    overflow := imported.overflow || child.state.overflow
    parallel := imported.parallel || child.state.parallel }

theorem importChild_work {width : Nat} (maximum : Nat) (parent : State width)
    (child : Child width) :
    (importChild maximum parent child).work.toNat =
      boundedTotal (2 ^ width - 1) (parent.work.toNat + child.state.work.toNat) := by
  cases complete : child.state.traceIncomplete with
  | true => simpa only [importChild, complete, if_true] using importIncomplete_work parent child.state
  | false =>
      have accounted := (child.measured complete).1
      have units : (child.replay.map fun charge => charge.units.toNat).sum =
          (snapshot child.state.history).2 :=
        (events_work child.replay).symm.trans
          (congrArg (fun occurrences => (totals occurrences).2) (child.replicated complete))
      simp only [importChild, complete, Bool.false_eq_true, if_false]
      rw [run_work, units, accounted]
      simpa only [Nat.add_comm] using
        (boundedTotal_add (2 ^ width - 1) (snapshot child.state.history).2 parent.work.toNat).symm

theorem importChild_count {width : Nat} (maximum : Nat) (parent : State width)
    (child : Child width) (kind : Kind) :
    ((importChild maximum parent child).counts kind).toNat =
      boundedTotal (2 ^ width - 1)
        ((parent.counts kind).toNat + (child.state.counts kind).toNat) := by
  cases complete : child.state.traceIncomplete with
  | true => simpa only [importChild, complete, if_true] using
      importIncomplete_count parent child.state kind
  | false =>
      have accounted := (child.measured complete).2 kind
      have units :
          (child.replay.map fun charge => if kind = charge.kind then charge.units.toNat else 0).sum =
            (snapshot child.state.history).1 kind :=
        (events_count child.replay kind).symm.trans
          (congrArg (fun occurrences => (totals occurrences).1 kind) (child.replicated complete))
      simp only [importChild, complete, Bool.false_eq_true, if_false]
      rw [run_count, units, accounted]
      simpa only [Nat.add_comm] using
        (boundedTotal_add (2 ^ width - 1) ((snapshot child.state.history).1 kind)
          (parent.counts kind).toNat).symm

theorem importChild_incomplete {width : Nat} (maximum : Nat) (parent : State width)
    (child : Child width) (incomplete : parent.traceIncomplete = true) :
    (importChild maximum parent child).traceIncomplete = true := by
  cases complete : child.state.traceIncomplete with
  | true => simp only [importChild, complete, if_true, importIncomplete_incomplete]
  | false => simpa only [importChild, complete, Bool.false_eq_true, if_false] using
      run_incomplete maximum child.replay parent incomplete

theorem importChild_incomplete_history {width : Nat} (maximum : Nat) (parent : State width)
    (child : Child width) (incomplete : parent.traceIncomplete = true) :
    (importChild maximum parent child).history = parent.history := by
  cases complete : child.state.traceIncomplete with
  | true => simp only [importChild, complete, if_true, importIncomplete_history]
  | false => simpa only [importChild, complete, Bool.false_eq_true, if_false] using
      run_incomplete_history maximum child.replay parent incomplete

/-- Import children in publication order, retaining the full accumulator.
The selected branch does not alter the child's declared work projection. -/
def importChildren {width : Nat} (maximum : Nat) : List (Child width) → State width → State width
  | [], parent => parent
  | child :: rest, parent => importChildren maximum rest (importChild maximum parent child)

theorem importChildren_append {width : Nat} (maximum : Nat) (first second : List (Child width))
    (parent : State width) :
    importChildren maximum (first ++ second) parent =
      importChildren maximum second (importChildren maximum first parent) := by
  induction first generalizing parent with
  | nil => rfl
  | cons child rest ih => exact ih _

theorem importChildren_work {width : Nat} (maximum : Nat) (children : List (Child width))
    (parent : State width) :
    (importChildren maximum children parent).work.toNat =
      boundedTotal (2 ^ width - 1)
        (parent.work.toNat + (children.map fun child => child.state.work.toNat).sum) := by
  induction children generalizing parent with
  | nil => simp [importChildren, boundedTotal, Nat.min_eq_right (word_fits parent.work)]
  | cons child rest ih =>
      rw [importChildren, ih, importChild_work, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem importChildren_count {width : Nat} (maximum : Nat) (children : List (Child width))
    (parent : State width) (kind : Kind) :
    ((importChildren maximum children parent).counts kind).toNat =
      boundedTotal (2 ^ width - 1) ((parent.counts kind).toNat +
        (children.map fun child => (child.state.counts kind).toNat).sum) := by
  induction children generalizing parent with
  | nil => simp [importChildren, boundedTotal, Nat.min_eq_right (word_fits (parent.counts kind))]
  | cons child rest ih =>
      rw [importChildren, ih, importChild_count, boundedTotal_add]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem importChildren_incomplete {width : Nat} (maximum : Nat) (children : List (Child width))
    (parent : State width) (incomplete : parent.traceIncomplete = true) :
    (importChildren maximum children parent).traceIncomplete = true := by
  induction children generalizing parent with
  | nil => exact incomplete
  | cons child rest ih => exact ih _ (importChild_incomplete _ _ _ incomplete)

theorem importChildren_incomplete_history {width : Nat} (maximum : Nat) (children : List (Child width))
    (parent : State width) (incomplete : parent.traceIncomplete = true) :
    (importChildren maximum children parent).history = parent.history := by
  induction children generalizing parent with
  | nil => rfl
  | cons child rest ih =>
      exact (ih _ (importChild_incomplete _ _ _ incomplete)).trans
        (importChild_incomplete_history _ _ _ incomplete)

def joinChildren {width : Nat} (maximum : Nat) (phases : List (List (List (Child width))))
    (parent : State width) : State width :=
  finishJoin (phases.map fun phase => phase.map fun lane => lane.map Child.state)
    parent.span (importChildren maximum phases.flatten.flatten parent)

theorem joinChildren_work {width : Nat} (maximum : Nat) (phases : List (List (List (Child width))))
    (parent : State width) :
    (joinChildren maximum phases parent).work.toNat =
      boundedTotal (2 ^ width - 1)
        (parent.work.toNat + (phases.flatten.flatten.map fun child => child.state.work.toNat).sum) := by
  rw [joinChildren, finishJoin_work, importChildren_work]

theorem joinChildren_span {width : Nat} (maximum : Nat) (phases : List (List (List (Child width))))
    (parent : State width) :
    (joinChildren maximum phases parent).span.toNat =
      boundedTotal (2 ^ width - 1) (parent.span.toNat +
        (phases.map fun phase => (phase.map fun lane =>
          (lane.map fun child => child.state.span.toNat).sum).foldr max 0).sum) := by
  rw [joinChildren, finishJoin_span, workerSchedule_span]
  simp only [List.map_map, Function.comp_def]

private def charge (identity units : Nat) (retained : Bool := true) : Charge 8 :=
  ⟨identity, 7, 12, .publish, BitVec.ofNat 8 units, retained⟩

/-- A zero increment does not poison a complete receipt. Refused identity
and unavailable storage both retain numerical work but stop chronology. -/
theorem refusal_and_storage_controls :
    let good := run 255 [charge 1 2, charge 0 0 false, charge 2 3] (initial 8)
    let refused := run 255 [charge 1 2, charge 0 3, charge 2 4] (initial 8)
    let unavailable := run 255 [charge 1 2, charge 2 3 false, charge 3 4] (initial 8)
    good.work.toNat = 5 ∧ good.traceIncomplete = false ∧
      (RunLengthEvents.expand good.history).length = 2 ∧
      refused.work.toNat = 9 ∧ refused.traceIncomplete = true ∧
      (RunLengthEvents.expand refused.history).length = 1 ∧
      unavailable.work.toNat = 9 ∧ unavailable.traceIncomplete = true ∧
      (RunLengthEvents.expand unavailable.history).length = 1 := by
  decide

/-- Complete and incomplete children use different import branches while
preserving the same work projection. After the missing middle history,
a later complete child cannot repair the retained prefix. Parent-side
storage failure is independent of a child's own complete receipt. -/
theorem mixed_child_import_controls :
    let first := Child.ofRun 255 [charge 1 2] [charge 1 2] rfl
    let missing := Child.ofRun 255 [charge 0 7] [charge 0 7] rfl
    let later := Child.ofRun 255 [charge 2 3] [charge 2 3] rfl
    let mixed := joinChildren 255 [[[first], [missing]], [[later]]] (initial 8)
    let unavailable := Child.ofRun 255 [charge 1 2] [charge 1 2 false] rfl
    let failed := joinChildren 255 [[[unavailable], [later]]] (initial 8)
    mixed.work.toNat = 12 ∧ mixed.span.toNat = 10 ∧ mixed.traceIncomplete = true ∧
      mixed.parallel = true ∧ identities mixed.history = [1] ∧
      failed.work.toNat = 5 ∧ failed.span.toNat = 3 ∧ failed.traceIncomplete = true ∧
      failed.history = [] := by
  decide

/-- Equal kind and units do not authorize changing the copied physical
event identity. The admitted child relation rules out that invented replay. -/
theorem copied_child_identity_refused :
    ¬ ∃ child : Child 8,
      child.state = run 255 [charge 1 2] (initial 8) ∧ child.replay = [charge 9 2] := by
  rintro ⟨child, state, replay⟩
  have complete : child.state.traceIncomplete = false := by rw [state]; decide
  have same := child.replicated complete
  rw [state, replay] at same
  exact (by decide : events [charge 9 2] ≠
    RunLengthEvents.expand (run 255 [charge 1 2] (initial 8)).history) same

/-- Saturation, history failure and resumption preserve separate evidence.
Restarting from an empty receipt loses numerical work and the missing past. -/
theorem incomplete_resume_control :
    let prior := run 255 [charge 1 250, charge 0 9] (initial 8)
    let resumed := run 255 [charge 2 0] prior
    resumed.work.toNat = 255 ∧ resumed.overflow = true ∧
      resumed.traceIncomplete = true ∧ completeHistory resumed = none ∧
      resumed.work ≠ (run 255 [charge 2 0] (initial 8)).work := by
  decide

/-- The same unavailable history and incompleteness flag can accompany
different charged work. Reconstructing counters from that view is invalid. -/
theorem work_does_not_factor_history :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun charges : List (Charge 8) =>
        let state := run 255 charges (initial 8)
        (state.history, state.traceIncomplete))
      (fun charges => (run 255 charges (initial 8)).work.toNat) := by
  apply Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
  exact ⟨[charge 0 1], [charge 0 2], rfl, by decide⟩

end Recording

/-- In the explicitly sequential profile, span equals the serial counted work. -/
def sequentialReadout (ledger : Ledger) : WorkSpan :=
  ⟨(snapshot ledger).2, (snapshot ledger).2⟩

theorem sequentialReadout_append (first second : Ledger) :
    sequentialReadout (first ++ second) =
      WorkSpan.sequential (sequentialReadout first) (sequentialReadout second) := by
  rw [sequentialReadout, snapshot_append]
  rfl

/-- A fork-join arrangement of chronological receipts. The shared prefix is
outside the children; each child contains only its new execution events.
This arrangement records a proposed schedule. The execution boundary must
establish independence and physical event identity before accepting it. -/
structure ForkLedger where
  before : Ledger
  children : List Ledger
  after : Ledger

namespace ForkLedger

/-- Retain physical event occurrences in logical child-publication order. -/
def flattened (receipt : ForkLedger) : Ledger :=
  receipt.before ++ receipt.children.flatten ++ receipt.after

/-- The independent-child profile in which each individual child executes
sequentially. Nested parallel children need their own retained causal
readouts, accepted by the general `WorkSpan.forkJoin` construction. -/
def sequentialChildrenReadout (receipt : ForkLedger) : WorkSpan :=
  WorkSpan.forkJoin (sequentialReadout receipt.before)
    (receipt.children.map sequentialReadout) (sequentialReadout receipt.after)

private theorem snapshot_flatten (children : List Ledger) :
    snapshot children.flatten = (children.map snapshot).sum := by
  induction children with
  | nil => rfl
  | cons child rest ih =>
      simp only [List.flatten_cons, List.map_cons, List.sum_cons]
      rw [snapshot_append, ih]

/-- Work is conserved when sequential children are joined independently. No
physical event is removed to obtain a smaller span. -/
theorem work_eq_flattened (receipt : ForkLedger) :
    receipt.sequentialChildrenReadout.work = (snapshot receipt.flattened).2 := by
  rw [sequentialChildrenReadout, WorkSpan.forkJoin_work]
  simp only [flattened, snapshot_append, snapshot_flatten,
    Prod.snd_add, List.map_map, sequentialReadout]
  have sums : ((receipt.children.map snapshot).sum).2 =
      ((receipt.children.map snapshot).map Prod.snd).sum :=
    map_list_sum (AddMonoidHom.snd (Kind → Nat) Nat) _
  rw [sums]
  simp only [List.map_map, Function.comp_def, sequentialReadout, Nat.add_assoc]

/-- The prefix and suffix lie on the critical path; the slower independent
child determines the middle span in the declared sequential-child profile. -/
theorem span_eq_phases (receipt : ForkLedger) :
    receipt.sequentialChildrenReadout.span = (snapshot receipt.before).2 +
      (receipt.children.map fun child => (snapshot child).2).foldr max 0 +
        (snapshot receipt.after).2 := by
  simp [sequentialChildrenReadout, WorkSpan.forkJoin_span, Function.comp_def, sequentialReadout]

/-- An actual placement retains each child's chronology and causal cost.
The three list levels are phases, workers and successive worker slices.
A nested parallel child's span is retained rather than replaced by its work. -/
def placedReadout (receipt : ForkLedger)
    (phases : List (List (List (Ledger × WorkSpan)))) : WorkSpan :=
  WorkSpan.sequential (sequentialReadout receipt.before)
    (WorkSpan.sequential
      (ParallelCrossover.workerPhases
        (phases.map fun phase => phase.map fun lane => lane.map Prod.snd))
      (sequentialReadout receipt.after))

/-- Child occurrences are neither omitted nor repeated by the placement.
Permutation permits physical scheduling order to differ from publication. -/
def PlacementCovers (receipt : ForkLedger)
    (phases : List (List (List (Ledger × WorkSpan)))) : Prop :=
  (phases.flatten.flatten.map Prod.fst).Perm receipt.children

/-- Causal costs must account for their own complete chronological receipts.
Execution and independence still supply the meaning of the span coordinate. -/
def PlacementMeasured (phases : List (List (List (Ledger × WorkSpan)))) : Prop :=
  ∀ child ∈ phases.flatten.flatten, child.2.work = (snapshot child.1).2

private theorem placed_middle_work (phases : List (List (List (Ledger × WorkSpan))))
    (measured : PlacementMeasured phases) :
    (ParallelCrossover.workerPhases
      (phases.map fun phase => phase.map fun lane => lane.map Prod.snd)).work =
      ((phases.flatten.flatten.map Prod.fst).map fun ledger => (snapshot ledger).2).sum := by
  rw [ParallelCrossover.workerPhases_work_flatten]
  have projections :
      ((phases.flatten.flatten.map Prod.snd).map WorkSpan.work) =
        ((phases.flatten.flatten.map Prod.fst).map fun ledger => (snapshot ledger).2) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro child present
    exact measured child present
  simpa only [List.map_flatten, List.map_map, Function.comp_def] using
    congrArg List.sum projections

/-- Placement preserves the complete execution work, with the inherited
prefix and subsequent join charged once. The hypotheses validate both the
child accounting and the coverage of this particular placement. -/
theorem placed_work_eq_flattened (receipt : ForkLedger)
    (phases : List (List (List (Ledger × WorkSpan))))
    (covered : receipt.PlacementCovers phases) (measured : PlacementMeasured phases) :
    (receipt.placedReadout phases).work = (snapshot receipt.flattened).2 := by
  have middle := placed_middle_work phases measured
  have sameWork := (covered.map (fun ledger => (snapshot ledger).2)).sum_eq
  rw [sameWork] at middle
  rw [placedReadout]
  change (snapshot receipt.before).2 +
    ((ParallelCrossover.workerPhases _).work + (snapshot receipt.after).2) = _
  rw [middle, ← receipt.work_eq_flattened]
  simp [sequentialChildrenReadout, WorkSpan.forkJoin_work, Function.comp_def,
    sequentialReadout, Nat.add_assoc]

/-- Every phase is a barrier. Within it the busiest worker's accumulated
child spans determine the middle cost, including nested parallel children. -/
theorem placed_span_eq (receipt : ForkLedger)
    (phases : List (List (List (Ledger × WorkSpan)))) :
    (receipt.placedReadout phases).span = (snapshot receipt.before).2 +
      (phases.map fun phase =>
        (phase.map fun lane => (lane.map fun child => child.2.span).sum).foldr max 0).sum +
      (snapshot receipt.after).2 := by
  simp [placedReadout, WorkSpan.sequential, ParallelCrossover.workerPhases_span,
    sequentialReadout, List.map_map, Function.comp_def, Nat.add_assoc]

/-- A publication-order fork is the placement with one child per worker in
one phase. Its old readout remains an instance of the shared phase algebra. -/
theorem placed_sequential_children (receipt : ForkLedger) :
    receipt.placedReadout
      [receipt.children.map fun child => [(child, sequentialReadout child)]] =
      receipt.sequentialChildrenReadout := by
  simp [placedReadout, ParallelCrossover.workerPhases, ParallelCrossover.workerPhase,
    sequentialChildrenReadout, WorkSpan.forkJoin, List.map_map, Function.comp_def]

/-- Retaining only event order determines work without determining a
fork-join critical path. This uses the library's common factorization law. -/
theorem work_factors_flattened :
    Mettapedia.GSLT.Core.NonFactorization.Factors flattened
      (fun receipt => receipt.sequentialChildrenReadout.work) :=
  ⟨fun ledger => (snapshot ledger).2, fun receipt => receipt.work_eq_flattened.symm⟩

private def firstEvent : Run := ⟨1, 1, ⟨1, 10, .quantum, 1⟩⟩
private def secondEvent : Run := ⟨2, 1, ⟨2, 20, .quantum, 1⟩⟩

private def independentPair : ForkLedger := ⟨[], [[firstEvent], [secondEvent]], []⟩
private def sequentialPair : ForkLedger := ⟨[], [[firstEvent, secondEvent]], []⟩

private def thirdEvent : Run := ⟨3, 1, ⟨3, 30, .matchNode, 3⟩⟩
private def fourthEvent : Run := ⟨4, 1, ⟨4, 40, .matchNode, 4⟩⟩
private def fifthEvent : Run := ⟨5, 1, ⟨5, 50, .matchNode, 5⟩⟩

private def placedExample : ForkLedger :=
  ⟨[], [[firstEvent, secondEvent], [thirdEvent], [fourthEvent], [fifthEvent]], []⟩

private def examplePlacement : List (List (List (Ledger × WorkSpan))) :=
  [[[([firstEvent, secondEvent], WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩),
      ([thirdEvent], ⟨3, 3⟩)], [([fourthEvent], ⟨4, 4⟩)]],
   [[([fifthEvent], ⟨5, 5⟩)]]]

/-- The example contains every child once, retains the nested child's
parallel span, and charges a later fallback after the first phase. -/
theorem placed_nested_child_and_fallback_control :
    placedExample.PlacementCovers examplePlacement ∧
      PlacementMeasured examplePlacement ∧ Unique placedExample.flattened ∧
      placedExample.placedReadout examplePlacement = ⟨14, 9⟩ := by
  refine ⟨List.Perm.refl _, ?_, ?_, ?_⟩
  · simp only [PlacementMeasured, examplePlacement, List.flatten_cons,
      List.flatten_nil, List.nil_append, List.cons_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false]
    intro child present
    rcases present with rfl | rfl | rfl | rfl <;> decide
  · unfold Unique
    decide
  · decide

/-- Forgetting worker assignments and the fallback barrier reports span
five instead of nine. Replacing a nested child's causal span by its work
also changes the first worker's load; flattened work remains fourteen. -/
theorem placed_omitted_dependencies_control :
    (placedExample.placedReadout examplePlacement).work = 14 ∧
      (placedExample.placedReadout examplePlacement).span ≠
        (WorkSpan.parallelAll
          [WorkSpan.parallel ⟨1, 1⟩ ⟨1, 1⟩, ⟨3, 3⟩, ⟨4, 4⟩, ⟨5, 5⟩]).span ∧
      placedExample.placedReadout examplePlacement ≠
        placedExample.placedReadout
          [[[([firstEvent, secondEvent], ⟨2, 2⟩), ([thirdEvent], ⟨3, 3⟩)],
              [([fourthEvent], ⟨4, 4⟩)]], [[([fifthEvent], ⟨5, 5⟩)]]] := by
  decide

/-- Positive control: independent publication preserves the original two
distinct physical identities while the declared parallel span is one. -/
theorem independent_pair_control :
    Unique independentPair.flattened ∧ identities independentPair.flattened = [1, 2] ∧
      independentPair.sequentialChildrenReadout = ⟨2, 1⟩ := by
  unfold Unique
  decide

/-- Negative control: the same ordered physical events can have different
causal phases. Their spans cannot be reconstructed from the flattened
receipt; its complete ordered occurrence information is still insufficient. -/
theorem span_does_not_factor_flattened :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors flattened
      (fun receipt => receipt.sequentialChildrenReadout.span) := by
  apply Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
    (shadow := flattened) (invariant := fun receipt => receipt.sequentialChildrenReadout.span)
  exact ⟨independentPair, sequentialPair, rfl, by decide⟩

/-- Reusing a child receipt copies physical identities and violates the
one-charge invariant, even if the two owners merely display the same work. -/
theorem duplicated_child_is_not_unique :
    ¬ Unique (flattened ⟨[], [[firstEvent], [firstEvent]], []⟩) := by
  unfold Unique
  decide

end ForkLedger

private def sharedRun : Run := ⟨1, 1, ⟨8, 14, .heapLookup, 1⟩⟩
private def childRun : Run := ⟨2, 1, ⟨9, 15, .equationActivation, 1⟩⟩

/-- Summing overlapping containing ledgers double-counts the nested event. -/
theorem overlapping_scopes_double_count :
    (snapshot [sharedRun, childRun]).2 + (snapshot [childRun]).2 = 3 ∧
      (snapshot [sharedRun, childRun]).2 = 2 := by decide

/-- Disjoint event partitions recover the whole execution charge exactly. -/
theorem disjoint_scope_partition :
    (snapshot [sharedRun]).2 + (snapshot [childRun]).2 =
      (snapshot [sharedRun, childRun]).2 := by decide

theorem saturated_value_is_not_exact : addLowerBound 7 6 4 = (7, true) ∧ 7 < 6 + 4 := by decide

/-- Reading again has a cost; it cannot repeatedly return the old meter. -/
theorem repeated_read_retains_charge :
    (inspect 255 (inspect 255 [sharedRun] 2 8 14).2 3 8 14).1.2 = 2 ∧
      (snapshot (inspect 255 (inspect 255 [sharedRun] 2 8 14).2 3 8 14).2).2 = 3 := by decide

end Mettapedia.Machines.NativeCostLedger


namespace Mettapedia.Machines.NativeCostLedger

namespace IdentityTransport

/-- Event issuance, origin and occurrence are separate identity namespaces.
Destination addresses use a separate scoped-store relation. -/
structure Maps where
  event : Nat → Nat
  origin : Nat → Nat
  occurrence : Nat → Nat

def payload (mapping : Maps) (value : Payload) : Payload :=
  ⟨mapping.origin value.origin, mapping.occurrence value.occurrence, value.kind, value.units⟩

def event (mapping : Maps) (value : Event) : Event :=
  Mettapedia.Algebra.RunLengthEvents.mapEvent mapping.event (payload mapping) value

theorem event_grade (mapping : Maps) (value : Event) :
    eventGrade (event mapping value) = eventGrade value := rfl

theorem totals_preserved (mapping : Maps) (values : List Event) :
    totals (values.map (event mapping)) = totals values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [totals, List.map_cons, List.sum_cons, event_grade] at ih ⊢
      exact congrArg (eventGrade value + ·) ih

theorem event_injective (mapping : Maps)
    (events : Function.Injective mapping.event) (origins : Function.Injective mapping.origin)
    (occurrences : Function.Injective mapping.occurrence) : Function.Injective (event mapping) := by
  apply Mettapedia.Algebra.RunLengthEvents.mapEvent_injective _ _ events
  intro first second same
  have originSame := origins (congrArg Payload.origin same)
  have occurrenceSame := occurrences (congrArg Payload.occurrence same)
  have kindSame := congrArg Payload.kind same
  have unitsSame := congrArg Payload.units same
  cases first
  cases second
  cases originSame
  cases occurrenceSame
  cases kindSame
  cases unitsSame
  rfl

/-- Zero remains a refused reservation, rather than becoming fresh evidence. -/
theorem event_zero_iff (mapping : Maps) (events : Function.Injective mapping.event)
    (zero : mapping.event 0 = 0) (identity : Nat) :
    mapping.event identity = 0 ↔ identity = 0 := by
  constructor
  · intro missing
    exact events (missing.trans zero.symm)
  · rintro rfl
    exact zero

def charge {width : Nat} (mapping : Maps) (value : Recording.Charge width) :
    Recording.Charge width :=
  { value with identity := mapping.event value.identity
               origin := mapping.origin value.origin
               occurrence := mapping.occurrence value.occurrence }

theorem charge_event {width : Nat} (mapping : Maps) (value : Recording.Charge width) :
    (charge mapping value).event = event mapping value.event := rfl

/-- The complete numerical observation and retained chronology agree.
Compressed row shape and its storage expense have their own observer. -/
structure Related {width : Nat} (mapping : Maps)
    (source target : Recording.State width) : Prop where
  counts : target.counts = source.counts
  work : target.work = source.work
  span : target.span = source.span
  parallel : target.parallel = source.parallel
  overflow : target.overflow = source.overflow
  incomplete : target.traceIncomplete = source.traceIncomplete
  chronology : Mettapedia.Algebra.RunLengthEvents.expand target.history =
    (Mettapedia.Algebra.RunLengthEvents.expand source.history).map (event mapping)

/-- The actual bounded account appends commute with identity transport,
including saturation, ignored zero work and incomplete receipt retention.
This does not establish a native identity allocator or storage provider. -/
theorem append_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (sourceMaximum targetMaximum : Nat) (source target : Recording.State width)
    (value : Recording.Charge width) (related : Related mapping source target) :
    Related mapping (Recording.append sourceMaximum source value)
      (Recording.append targetMaximum target (charge mapping value)) := by
  have zeroIdentity : decide ((charge mapping value).identity = 0) =
      decide (value.identity = 0) := by
    change decide (mapping.event value.identity = 0) = decide (value.identity = 0)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact event_zero_iff mapping events zero value.identity
  have sameMissing :
      (target.traceIncomplete || decide ((charge mapping value).identity = 0) ||
        !(charge mapping value).retained) =
      (source.traceIncomplete || decide (value.identity = 0) || !value.retained) := by
    rw [related.incomplete, zeroIdentity]
    rfl
  have sameUnits : (charge mapping value).units = value.units := rfl
  by_cases ignored : value.units = 0
  · simpa only [Recording.append, charge, ignored, if_true] using related
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Recording.append, charge, if_neg ignored, related.counts, related.overflow]
    · simp only [Recording.append, charge, if_neg ignored, related.counts,
        related.work, related.overflow]
    · simp only [Recording.append, charge, if_neg ignored, related.counts,
        related.work, related.span, related.overflow]
    · simp only [Recording.append, charge, if_neg ignored, related.parallel]
    · simp only [Recording.append, charge, if_neg ignored, related.counts,
        related.work, related.span, related.overflow]
    · simp only [Recording.append, sameUnits, if_neg ignored, sameMissing]
    · cases missing : (source.traceIncomplete || decide (value.identity = 0) || !value.retained) with
      | true =>
          simpa only [Recording.append, sameUnits, if_neg ignored,
            sameMissing, missing, if_true] using related.chronology
      | false =>
          simp only [Recording.append, sameUnits, if_neg ignored,
            sameMissing, missing, Bool.false_eq_true, if_false]
          rw [Mettapedia.Algebra.RunLengthEvents.expand_appendEvent,
            Mettapedia.Algebra.RunLengthEvents.expand_appendEvent, List.map_append,
            List.map_singleton, related.chronology, charge_event]

theorem run_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (sourceMaximum targetMaximum : Nat) (values : List (Recording.Charge width))
    (source target : Recording.State width) (related : Related mapping source target) :
    Related mapping (Recording.run sourceMaximum values source)
      (Recording.run targetMaximum (values.map (charge mapping)) target) := by
  induction values generalizing source target with
  | nil => exact related
  | cons value rest ih =>
      exact ih _ _ (append_related mapping events zero sourceMaximum targetMaximum
        source target value related)

/-- Moving ledger locations preserves null destinations and every deliberate
alias. Distinct live locations stay distinct under an injective location map. -/
theorem scoped_membership (locations : Nat → Nat)
    (faithful : Function.Injective locations) (scopes : List (Option Nat)) (location : Nat) :
    some (locations location) ∈ scopes.map (Option.map locations) ↔ some location ∈ scopes := by
  rw [List.mem_map]
  constructor
  · rintro ⟨candidate, present, same⟩
    cases candidate with
    | none => cases same
    | some other =>
        simp only [Option.map_some, Option.some.injEq] at same
        have equal := faithful same
        simpa only [equal] using present
  · intro present
    exact ⟨some location, present, rfl⟩

/-- A bounded comparison needs retention agreement only at destinations
this operation actually reaches. Other source/target service values are inert. -/
theorem chargeScopes_active_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (locations : Nat → Nat) (faithful : Function.Injective locations)
    (sourceMaximum targetMaximum : Nat) (scopes : List (Option Nat))
    (value : Recording.Charge width) (sourceRetained targetRetained : Nat → Bool)
    (retention : ∀ location, some location ∈ scopes →
      targetRetained (locations location) = sourceRetained location)
    (source target : Nat → Recording.State width)
    (related : ∀ location, Related mapping (source location) (target (locations location)))
    (location : Nat) :
    Related mapping
      (Recording.chargeScopes sourceMaximum scopes value sourceRetained source location)
      (Recording.chargeScopes targetMaximum (scopes.map (Option.map locations))
        (charge mapping value) targetRetained target (locations location)) := by
  simp only [Recording.chargeScopes_at,
    scoped_membership locations faithful scopes location]
  by_cases present : some location ∈ scopes
  · simp only [if_pos present]
    have sameCharge :
        Recording.localCharge (charge mapping value) targetRetained (locations location) =
          charge mapping (Recording.localCharge value sourceRetained location) := by
      simp only [Recording.localCharge, charge, retention location present]
    rw [sameCharge]
    exact append_related mapping events zero sourceMaximum targetMaximum
      (source location) (target (locations location))
      (Recording.localCharge value sourceRetained location) (related location)
  · simp only [if_neg present]
    exact related location

/-- The actual scope dispatcher commutes with transport of each complete
containing account. Duplicate frames still deliver once to an aliased ledger;
per-destination retention is compared at the mapped location. -/
theorem chargeScopes_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (locations : Nat → Nat) (faithful : Function.Injective locations)
    (sourceMaximum targetMaximum : Nat) (scopes : List (Option Nat))
    (value : Recording.Charge width) (sourceRetained targetRetained : Nat → Bool)
    (retention : ∀ location, targetRetained (locations location) = sourceRetained location)
    (source target : Nat → Recording.State width)
    (related : ∀ location, Related mapping (source location) (target (locations location)))
    (location : Nat) :
    Related mapping
      (Recording.chargeScopes sourceMaximum scopes value sourceRetained source location)
      (Recording.chargeScopes targetMaximum (scopes.map (Option.map locations))
        (charge mapping value) targetRetained target (locations location)) := by
  exact chargeScopes_active_related mapping events zero locations faithful
    sourceMaximum targetMaximum scopes value sourceRetained targetRetained
    (fun location _ => retention location) source target related location

namespace Controls

def separated : Maps := ⟨fun identity => 10 * identity,
  fun origin => origin + 100, fun occurrence => occurrence + 200⟩

def operation : Recording.Charge 8 := ⟨2, 12, 30, .heapLookup, 3, true⟩

/-- The same physical payload reaches two independent containing accounts,
while a repeated scope at one location remains one delivery. -/
theorem mapped_scopes_keep_aliases_and_independent_destinations :
    let source := Recording.chargeScopes 255 [some 4, none, some 9, some 4]
      operation (fun _ => true) (fun _ => Recording.initial 8)
    let target := Recording.chargeScopes 7 [some 40, none, some 90, some 40]
      (charge separated operation) (fun _ => true) (fun _ => Recording.initial 8)
    (source 4).work = (target 40).work ∧ (source 4).work.toNat = 3 ∧
      (source 9).work = (target 90).work ∧ (target 90).work.toNat = 3 ∧
      (target 50).work.toNat = 0 ∧
      Mettapedia.Algebra.RunLengthEvents.expand (target 40).history =
        (Mettapedia.Algebra.RunLengthEvents.expand (source 4).history).map (event separated) := by
  decide +kernel

/-- Merging two distinct locations invents an alias, so one destination
cannot represent both independent initial accounts. -/
theorem collapsed_locations_lose_accounts :
    let initial : Nat → Recording.State 8 := fun location =>
      { Recording.initial 8 with work := if location = 4 then 2 else 7 }
    (initial 4).work ≠ (initial 9).work ∧
      ¬ ∃ destination : Recording.State 8,
        Related separated (initial 4) destination ∧ Related separated (initial 9) destination := by
  refine ⟨by decide, ?_⟩
  rintro ⟨destination, first, second⟩
  have incompatible := first.work.symm.trans second.work
  exact (by decide : (2 : BitVec 8) ≠ 7) incompatible

/-- Refused identity reservation still pays the operation and permanently
marks the history incomplete; transporting zero may not repair it. -/
theorem zero_identity_refusal_remains_paid_and_incomplete :
    let refused : Recording.Charge 8 := { operation with identity := 0 }
    let target := Recording.append 255 (Recording.initial 8) (charge separated refused)
    target.work.toNat = 3 ∧ target.traceIncomplete = true ∧ target.history = [] := by
  decide +kernel

/-- A zero-unit operation ignores even identity and retention refusal.
The initial paid prefix and flags remain unchanged. -/
theorem zero_units_do_not_change_retained_account :
    let ignored : Recording.Charge 8 := { operation with identity := 0, units := 0, retained := false }
    let before : Recording.State 8 := { Recording.initial 8 with work := 7, span := 7 }
    Recording.append 255 before (charge separated ignored) = before := by
  rfl

end Controls

end IdentityTransport
end Mettapedia.Machines.NativeCostLedger


namespace Mettapedia.Machines.NativeCostLedger.IdentityTransport

/-- An injective location map preserves the original inner-to-outer order
of first live destinations; it may not merge distinct ledger identities. -/
theorem scopeTargets_map (locations : Nat → Nat) (faithful : Function.Injective locations)
    (scopes : List (Option Nat)) :
    scopeTargets (scopes.map (Option.map locations)) = (scopeTargets scopes).map locations := by
  have live : (scopes.map (Option.map locations)).filterMap id =
      (scopes.filterMap id).map locations := by
    induction scopes with
    | nil => rfl
    | cons value rest ih =>
        cases value with
        | none =>
            simpa only [List.map_cons, List.filterMap_cons, Option.map_none, id_eq] using ih
        | some value =>
            simpa only [List.map_cons, List.filterMap_cons, Option.map_some, id_eq] using
              congrArg (List.cons (locations value)) ih
  have inventory := VariableInventory.firstOccurrences_map locations id faithful []
    ((scopes.filterMap id).map fun location => (location, ()))
  simpa only [scopeTargets, live, List.map_nil, List.map_map, Function.comp_def] using
    congrArg (List.map Prod.fst) inventory

theorem charge_injective {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (origins : Function.Injective mapping.origin)
    (occurrences : Function.Injective mapping.occurrence) : Function.Injective (charge (width := width) mapping) := by
  intro first second same
  have identitySame := events (congrArg Recording.Charge.identity same)
  have originSame := origins (congrArg Recording.Charge.origin same)
  have occurrenceSame := occurrences (congrArg Recording.Charge.occurrence same)
  have kindSame := congrArg Recording.Charge.kind same
  have unitsSame := congrArg Recording.Charge.units same
  have retainedSame := congrArg Recording.Charge.retained same
  cases first
  cases second
  cases identitySame
  cases originSame
  cases occurrenceSame
  cases kindSame
  cases unitsSame
  cases retainedSame
  rfl

/-- This finite receipt map retains the full scope chain and each active
retention decision. Operation kinds and units keep their source meaning. -/
def mapReceipt {width : Nat} (mapping : Maps) (locations : Nat → Nat)
    (receipt : Recording.ScopedChargeReceipt width) : Recording.ScopedChargeReceipt width :=
  ⟨receipt.scopes.map (Option.map locations), charge mapping receipt.charge,
    receipt.retention.map (Mettapedia.Algebra.RunLengthEvents.mapEvent locations id)⟩

theorem mapReceipt_injective {width : Nat} (mapping : Maps) (locations : Nat → Nat)
    (events : Function.Injective mapping.event) (origins : Function.Injective mapping.origin)
    (occurrences : Function.Injective mapping.occurrence) (faithful : Function.Injective locations) :
    Function.Injective (mapReceipt (width := width) mapping locations) := by
  have options : Function.Injective (Option.map locations) := by
    intro first second same
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some value => cases same
    | some value =>
        cases second with
        | none => cases same
        | some other =>
            exact congrArg some (faithful (Option.some.inj same))
  have scopeLists := List.map_injective_iff.mpr options
  have destinationLists := List.map_injective_iff.mpr
    (Mettapedia.Algebra.RunLengthEvents.mapEvent_injective locations id faithful
      (Function.injective_id (α := Bool)))
  intro first second same
  have scopesSame := scopeLists (congrArg Recording.ScopedChargeReceipt.scopes same)
  have chargeSame := charge_injective mapping events origins occurrences
    (congrArg Recording.ScopedChargeReceipt.charge same)
  have retentionSame := destinationLists (congrArg Recording.ScopedChargeReceipt.retention same)
  cases first
  cases second
  cases scopesSame
  cases chargeSame
  cases retentionSame
  rfl

/-- Receipt comparison supplies the retention fact at each active mapped
destination. No equality of an unobserved infinite service is assumed. -/
theorem mapped_receipt_retention {width : Nat} (mapping : Maps) (locations : Nat → Nat)
    (first second : Recording.ScopedCharge width)
    (same : second.receipt = mapReceipt mapping locations first.receipt)
    (location : Nat) (present : some location ∈ first.scopes) :
    second.retained (locations location) = first.retained location := by
  have retention := congrArg Recording.ScopedChargeReceipt.retention same
  have entry : (locations location, first.retained location) ∈
      (mapReceipt mapping locations first.receipt).retention :=
    List.mem_map.mpr ⟨(location, first.retained location),
      List.mem_map.mpr ⟨location, (scopeTargets_mem first.scopes location).mpr present, rfl⟩, rfl⟩
  rw [← retention] at entry
  obtain ⟨other, _, sameEntry⟩ := List.mem_map.mp entry
  have locationSame : other = locations location := congrArg Prod.fst sameEntry
  subst other
  exact congrArg Prod.snd sameEntry

/-- Checked finite receipt transport instantiates the actual account step.
The native issuance/owner/service correspondence remains an extra obligation. -/
theorem chargeScopes_receipt_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (locations : Nat → Nat) (faithful : Function.Injective locations)
    (sourceMaximum targetMaximum : Nat) (first second : Recording.ScopedCharge width)
    (same : second.receipt = mapReceipt mapping locations first.receipt)
    (source target : Nat → Recording.State width)
    (related : ∀ location, Related mapping (source location) (target (locations location)))
    (location : Nat) :
    Related mapping
      (Recording.chargeScopes sourceMaximum first.scopes first.charge first.retained source location)
      (Recording.chargeScopes targetMaximum second.scopes second.charge second.retained
        target (locations location)) := by
  have scopes := congrArg Recording.ScopedChargeReceipt.scopes same
  have charges := congrArg Recording.ScopedChargeReceipt.charge same
  change second.scopes = first.scopes.map (Option.map locations) at scopes
  change second.charge = charge mapping first.charge at charges
  rw [scopes, charges]
  exact chargeScopes_active_related mapping events zero locations faithful
    sourceMaximum targetMaximum first.scopes first.charge first.retained second.retained
    (mapped_receipt_retention mapping locations first second same)
    source target related location

/-- A matched ordered sequence of finite receipts transports the whole
containing-account population through every phase and every resumption cut. -/
theorem runScopes_receipts_related {width : Nat} (mapping : Maps)
    (events : Function.Injective mapping.event) (zero : mapping.event 0 = 0)
    (locations : Nat → Nat) (faithful : Function.Injective locations)
    (sourceMaximum targetMaximum : Nat)
    (first second : List (Recording.ScopedCharge width))
    (receipts : List.Forall₂
      (fun source target => target.receipt = mapReceipt mapping locations source.receipt)
      first second)
    (source target : Nat → Recording.State width)
    (related : ∀ location, Related mapping (source location) (target (locations location))) :
    ∀ location, Related mapping (Recording.runScopes sourceMaximum first source location)
      (Recording.runScopes targetMaximum second target (locations location)) := by
  induction receipts generalizing source target with
  | nil => exact related
  | @cons first second restFirst restSecond same remaining ih =>
      exact ih _ _ (chargeScopes_receipt_related mapping events zero locations faithful
        sourceMaximum targetMaximum first second same source target related)

namespace ReceiptControls

def original : Recording.ScopedChargeReceipt 8 :=
  ⟨[some 4, none, some 9, some 4], Controls.operation, [(4, true), (9, false)]⟩

theorem explicit_map_retains_alias_word_and_every_retention :
    mapReceipt Controls.separated (fun location => 10 * location) original =
      ⟨[some 40, none, some 90, some 40], charge Controls.separated Controls.operation,
        [(40, true), (90, false)]⟩ := by decide +kernel

theorem omitted_retention_is_not_a_matching_receipt :
    mapReceipt Controls.separated (fun location => 10 * location) original ≠
      ⟨[some 40, none, some 90, some 40], charge Controls.separated Controls.operation,
        [(40, true)]⟩ := by decide +kernel

theorem phase_role_cannot_be_renamed :
    (charge Controls.separated { Controls.operation with kind := .restore }).kind = .restore ∧
      (charge Controls.separated { Controls.operation with kind := .restore }).kind ≠ .publish := by
  decide +kernel

end ReceiptControls
end Mettapedia.Machines.NativeCostLedger.IdentityTransport


