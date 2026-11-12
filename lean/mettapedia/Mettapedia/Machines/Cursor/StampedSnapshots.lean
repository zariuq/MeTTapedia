import Mathlib.Tactic

/-!
# Stable-slot readers under timestamped retirement

The store allocates occurrence identifiers monotonically. Removal stamps a
record once and leaves its value and slot in place. Readers retain only an
entry timestamp, ceiling and current slot. Adds and removals do not enumerate
or copy reader remainders. The independent reference reader retains a list of
entry slots; the simulation below includes readers opened, copied, rewound,
advanced and closed between arbitrary store writes.

This is a sequential logical-update model. It supplies neither a native
allocation/synchronization proof nor a claim that arbitrary indexes remain
complete after tombstoned rows are removed from them.
The functional slot lookup is an abstract interface, not a constant-time
implementation claim.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.StampedSnapshots

variable {Value : Type}

structure Row (Value : Type) where
  value : Value
  born : Nat
  death : Option Nat
  deriving Repr, DecidableEq

structure Store (Value : Type) where
  clock : Nat
  next : Nat
  row : Nat → Option (Row Value)

def empty : Store Value := ⟨0, 0, fun _ => none⟩

def visible (time : Nat) (row : Row Value) : Bool :=
  decide (row.born ≤ time) && (row.death.map (fun death => decide (time < death))).getD true

def atTime (store : Store Value) (time id : Nat) : Option (Nat × Value) := do
  let row ← store.row id
  if visible time row then some (id, row.value) else none

def add (store : Store Value) (value : Value) : Store Value :=
  ⟨store.clock + 1, store.next + 1,
    Function.update store.row store.next (some ⟨value, store.clock + 1, none⟩)⟩

/-- A retirement time is assigned only to a live row. Repeated removal does
not replace an earlier death with a later one. -/
def remove (store : Store Value) (id : Nat) : Store Value :=
  match store.row id with
  | none => store
  | some row => match row.death with
    | some _ => store
    | none => ⟨store.clock + 1, store.next,
        Function.update store.row id (some { row with death := some (store.clock + 1) })⟩

theorem add_clock (store : Store Value) (value : Value) :
    store.clock ≤ (add store value).clock := by simp [add]

theorem remove_clock (store : Store Value) (id : Nat) :
    store.clock ≤ (remove store id).clock := by
  unfold remove
  split <;> rename_i found
  · exact le_rfl
  · split
    · exact le_rfl
    · simp

@[simp] theorem remove_next (store : Store Value) (id : Nat) :
    (remove store id).next = store.next := by
  unfold remove
  split
  · rfl
  · split <;> rfl

theorem add_keeps_old_slot (store : Store Value) (value : Value) (id : Nat)
    (old : id < store.next) : (add store value).row id = store.row id := by
  simp [add, Function.update_of_ne (Nat.ne_of_lt old)]

theorem remove_keeps_past (store : Store Value) (retired time id : Nat)
    (past : time ≤ store.clock) :
    atTime (remove store retired) time id = atTime store time id := by
  unfold remove
  cases found : store.row retired with
  | none => rfl
  | some row =>
      cases death : row.death with
      | some stamp => simp only [death]
      | none =>
          by_cases same : id = retired
          · subst id
            simp [atTime, Function.update, found, visible, death, show time < store.clock + 1 by omega]
          · simp [death, atTime, Function.update_of_ne same]

theorem remove_keeps_payload (store : Store Value) (retired id : Nat) :
    ((remove store retired).row id).map Row.value = (store.row id).map Row.value := by
  unfold remove
  cases found : store.row retired with
  | none => rfl
  | some row =>
      cases death : row.death with
      | some stamp => simp only [death]
      | none =>
          by_cases same : id = retired
          · subst id
            simp [death, Function.update, found]
          · simp [death, Function.update_of_ne same]

structure Reader where
  time : Nat
  ceiling : Nat
  position : Nat
  deriving Repr, DecidableEq

def start (store : Store Value) : Reader := ⟨store.clock, store.next, 0⟩

def Admissible (store : Store Value) (reader : Reader) : Prop :=
  reader.time ≤ store.clock ∧ reader.ceiling ≤ store.next

/-- Mathematical entry slots, including cells already retired at opening.
This list is not stored in the implementation reader. -/
def snapshot (store : Store Value) (reader : Reader) : List (Option (Nat × Value)) :=
  (List.range reader.ceiling).map (atTime store reader.time)

def remaining (store : Store Value) (reader : Reader) : List (Option (Nat × Value)) :=
  (snapshot store reader).drop reader.position

/-- A representation replacement earns preservation from equal logical slot
records, including their birth/death evidence. Physical addresses or layout
need not agree. A native adapter must establish this slot-level premise. -/
theorem snapshot_of_slot_agreement (before after : Store Value) (reader : Reader)
    (same : ∀ id < reader.ceiling, after.row id = before.row id) :
    snapshot after reader = snapshot before reader := by
  apply List.map_congr_left
  intro id member
  simp only [atTime, same id (List.mem_range.mp member)]

theorem retired_before_reader (store : Store Value) (reader : Reader) (id : Nat)
    (row : Row Value) (found : store.row id = some row) (death : Nat)
    (retired : row.death = some death) (before : death ≤ reader.time) :
    atTime store reader.time id = none := by
  simp [atTime, found, visible, retired, show ¬reader.time < death by omega]

theorem snapshot_add (store : Store Value) (value : Value) (reader : Reader)
    (valid : Admissible store reader) :
    snapshot (add store value) reader = snapshot store reader := by
  apply List.map_congr_left
  intro id member
  have old : id < store.next := lt_of_lt_of_le (List.mem_range.mp member) valid.2
  simp only [atTime, add_keeps_old_slot store value id old]

theorem snapshot_remove (store : Store Value) (id : Nat) (reader : Reader)
    (valid : Admissible store reader) :
    snapshot (remove store id) reader = snapshot store reader := by
  apply List.map_congr_left
  intro row _
  exact remove_keeps_past store id reader.time row valid.1

theorem admissible_add (store : Store Value) (value : Value) (reader : Reader)
    (valid : Admissible store reader) : Admissible (add store value) reader := by
  rcases valid with ⟨time, ceiling⟩
  exact ⟨time.trans (add_clock store value), by simpa [add] using ceiling.trans (Nat.le_succ _)⟩

theorem admissible_remove (store : Store Value) (id : Nat) (reader : Reader)
    (valid : Admissible store reader) : Admissible (remove store id) reader := by
  exact ⟨valid.1.trans (remove_clock store id), by simpa using valid.2⟩

inductive Reply (Value : Type) where
  | missing
  | exhausted
  | skip
  | value (occurrence : Nat) (payload : Value)
  | silent
  deriving Repr, DecidableEq

def slotReply : Option (Nat × Value) → Reply Value
  | none => .skip
  | some (id, value) => .value id value

/-- One internal step tests one stable slot. A rejected or invisible row is
not confused with exhaustion, so a consumer may suspend between such steps. -/
def step (store : Store Value) (reader : Reader) : Reply Value × Reader :=
  if reader.position < reader.ceiling then
    (slotReply (atTime store reader.time reader.position),
      { reader with position := reader.position + 1 })
  else
    (.exhausted, reader)

def referenceStep (slots : List (Option (Nat × Value))) :
    Reply Value × List (Option (Nat × Value)) :=
  match slots with
  | [] => (.exhausted, [])
  | slot :: rest => (slotReply slot, rest)

theorem snapshot_length (store : Store Value) (reader : Reader) :
    (snapshot store reader).length = reader.ceiling := by simp [snapshot]

theorem step_refines (store : Store Value) (reader : Reader) :
    (step store reader).1 = (referenceStep (remaining store reader)).1 ∧
      remaining store (step store reader).2 = (referenceStep (remaining store reader)).2 := by
  by_cases within : reader.position < reader.ceiling
  · have bound : reader.position < (snapshot store reader).length := by
      simpa only [snapshot_length] using within
    have row : (snapshot store reader)[reader.position]'bound =
        atTime store reader.time reader.position := by simp [snapshot]
    have split := List.drop_eq_getElem_cons bound
    rw [row] at split
    simp only [step, if_pos within]
    change slotReply (atTime store reader.time reader.position) =
        (referenceStep (remaining store reader)).1 ∧
      (snapshot store reader).drop (reader.position + 1) =
        (referenceStep (remaining store reader)).2
    rw [show remaining store reader = atTime store reader.time reader.position ::
      (snapshot store reader).drop (reader.position + 1) from split]
    exact ⟨rfl, rfl⟩
  · have emptyRest : remaining store reader = [] :=
      List.drop_eq_nil_of_le (by simpa only [snapshot_length] using Nat.le_of_not_gt within)
    simp [step, within, referenceStep, emptyRest]

theorem step_keeps_snapshot (store : Store Value) (reader : Reader) :
    snapshot store (step store reader).2 = snapshot store reader := by
  simp only [step]
  split <;> rfl

theorem admissible_step (store : Store Value) (reader : Reader)
    (valid : Admissible store reader) : Admissible store (step store reader).2 := by
  unfold step
  split <;> exact valid

structure Captured (Value : Type) where
  slots : List (Option (Nat × Value))
  position : Nat
  deriving Repr, DecidableEq

def capture (store : Store Value) (reader : Reader) : Captured Value :=
  ⟨snapshot store reader, reader.position⟩

def capturedStep (saved : Captured Value) : Reply Value × Captured Value :=
  match saved.slots[saved.position]? with
  | none => (.exhausted, saved)
  | some slot => (slotReply slot, { saved with position := saved.position + 1 })

theorem snapshot_lookup (store : Store Value) (reader : Reader) (position : Nat) :
    (snapshot store reader)[position]? =
      if position < reader.ceiling then some (atTime store reader.time position) else none := by
  by_cases within : position < reader.ceiling <;> simp [snapshot, within]

theorem captured_step (store : Store Value) (reader : Reader) :
    capturedStep (capture store reader) =
      ((step store reader).1, capture store (step store reader).2) := by
  by_cases within : reader.position < reader.ceiling
  · simp [capturedStep, capture, within, step, snapshot]
  · simp [capturedStep, capture, within, step, snapshot]

def rewind (reader : Reader) (back : Bool) : Reader :=
  if back then { reader with position := 0 } else reader

def capturedRewind (saved : Captured Value) (back : Bool) : Captured Value :=
  if back then { saved with position := 0 } else saved

theorem capture_rewind (store : Store Value) (reader : Reader) (back : Bool) :
    capture store (rewind reader back) = capturedRewind (capture store reader) back := by
  cases back <;> rfl

structure Machine (Value : Type) where
  store : Store Value
  readers : Nat → Option Reader

def initial (store : Store Value) : Machine Value := ⟨store, fun _ => none⟩

def ValidReaders (machine : Machine Value) : Prop :=
  ∀ id reader, machine.readers id = some reader → Admissible machine.store reader

def captureAll (machine : Machine Value) : Nat → Option (Captured Value) :=
  fun id => (machine.readers id).map (capture machine.store)

def setReader (machine : Machine Value) (id : Nat) (reader : Option Reader) : Machine Value :=
  { machine with readers := Function.update machine.readers id reader }

theorem valid_initial (store : Store Value) : ValidReaders (initial store) := by
  intro id reader found
  cases found

theorem valid_set (machine : Machine Value) (valid : ValidReaders machine)
    (id : Nat) (reader : Option Reader)
    (allowed : ∀ value, reader = some value → Admissible machine.store value) :
    ValidReaders (setReader machine id reader) := by
  intro other value found
  by_cases same : other = id
  · subst other
    exact allowed value (by simpa [setReader] using found)
  · exact valid other value (by simpa [setReader, Function.update_of_ne same] using found)

theorem captureAll_set (machine : Machine Value) (id : Nat) (reader : Option Reader) :
    captureAll (setReader machine id reader) =
      Function.update (captureAll machine) id (reader.map (capture machine.store)) := by
  funext other
  by_cases same : other = id <;> simp [captureAll, setReader, Function.update, same]

theorem captureAll_add (machine : Machine Value) (valid : ValidReaders machine) (value : Value) :
    captureAll { machine with store := add machine.store value } = captureAll machine := by
  funext id
  cases found : machine.readers id with
  | none => simp [captureAll, found]
  | some reader =>
      simp only [captureAll, found, Option.map_some, capture]
      rw [snapshot_add machine.store value reader (valid id reader found)]

theorem captureAll_remove (machine : Machine Value) (valid : ValidReaders machine) (id : Nat) :
    captureAll { machine with store := remove machine.store id } = captureAll machine := by
  funext other
  cases found : machine.readers other with
  | none => simp [captureAll, found]
  | some reader =>
      simp only [captureAll, found, Option.map_some, capture]
      rw [snapshot_remove machine.store id reader (valid other reader found)]

inductive Event (Value : Type) where
  | add (value : Value)
  | remove (id : Nat)
  | openReader (reader : Nat)
  | read (reader : Nat)
  | clone (source target : Nat) (back : Bool)
  | close (reader : Nat)
  deriving Repr, DecidableEq

def apply (machine : Machine Value) : Event Value → Machine Value × Reply Value
  | .add value => ({ machine with store := add machine.store value }, .silent)
  | .remove id => ({ machine with store := remove machine.store id }, .silent)
  | .openReader id => (setReader machine id (some (start machine.store)), .silent)
  | .read id => match machine.readers id with
    | none => (machine, .missing)
    | some reader =>
        let next := step machine.store reader
        (setReader machine id (some next.2), next.1)
  | .clone source target back =>
      (setReader machine target ((machine.readers source).map (fun reader => rewind reader back)), .silent)
  | .close id => (setReader machine id none, .silent)

/-- The reference performs no visibility checks after opening. It retains
the entry slots themselves and advances or copies that captured list. -/
def referenceApply (store : Store Value) (saved : Nat → Option (Captured Value)) :
    Event Value → (Nat → Option (Captured Value)) × Reply Value
  | .add _ | .remove _ => (saved, .silent)
  | .openReader id => (Function.update saved id (some (capture store (start store))), .silent)
  | .read id => match saved id with
    | none => (saved, .missing)
    | some held =>
        let next := capturedStep held
        (Function.update saved id (some next.2), next.1)
  | .clone source target back =>
      (Function.update saved target ((saved source).map (fun held => capturedRewind held back)), .silent)
  | .close id => (Function.update saved id none, .silent)

theorem valid_apply (machine : Machine Value) (valid : ValidReaders machine) (event : Event Value) :
    ValidReaders (apply machine event).1 := by
  cases event with
  | add value =>
      intro id reader found
      exact admissible_add machine.store value reader (valid id reader found)
  | remove id =>
      intro other reader found
      exact admissible_remove machine.store id reader (valid other reader found)
  | openReader id =>
      apply valid_set machine valid id (some (start machine.store))
      intro reader same
      cases same
      exact ⟨le_rfl, le_rfl⟩
  | close id =>
      apply valid_set machine valid id none
      intro reader same
      cases same
  | clone source target back =>
      apply valid_set machine valid target
      intro reader same
      obtain ⟨old, found, equal⟩ := Option.map_eq_some_iff.mp same
      subst reader
      cases back <;> exact valid source old found
  | read id =>
      cases found : machine.readers id with
      | none => simpa [apply, found] using valid
      | some reader =>
          simp only [apply, found]
          apply valid_set machine valid id (some (step machine.store reader).2)
          intro next same
          cases same
          exact admissible_step machine.store reader (valid id reader found)

theorem apply_refines (machine : Machine Value) (valid : ValidReaders machine) (event : Event Value) :
    captureAll (apply machine event).1 = (referenceApply machine.store (captureAll machine) event).1 ∧
      (apply machine event).2 = (referenceApply machine.store (captureAll machine) event).2 := by
  cases event with
  | add value => exact ⟨captureAll_add machine valid value, rfl⟩
  | remove id => exact ⟨captureAll_remove machine valid id, rfl⟩
  | openReader id => exact ⟨captureAll_set machine id (some (start machine.store)), rfl⟩
  | close id => exact ⟨captureAll_set machine id none, rfl⟩
  | clone source target back =>
      constructor
      · simp only [apply, referenceApply, captureAll_set, captureAll, Option.map_map]
        congr 2
        funext reader
        exact capture_rewind machine.store reader back
      · rfl
  | read id =>
      cases found : machine.readers id with
      | none => simp [apply, referenceApply, captureAll, found]
      | some reader =>
          simp only [apply, found, referenceApply, captureAll, Option.map_some, captured_step]
          exact ⟨captureAll_set machine id (some (step machine.store reader).2), trivial⟩

def storeEvent (store : Store Value) : Event Value → Store Value
  | .add value => add store value
  | .remove id => remove store id
  | .openReader _ | .read _ | .clone _ _ _ | .close _ => store

theorem apply_store (machine : Machine Value) (event : Event Value) :
    (apply machine event).1.store = storeEvent machine.store event := by
  cases event with
  | add value => rfl
  | remove id => rfl
  | openReader id => rfl
  | clone source target back => rfl
  | close id => rfl
  | read id => cases found : machine.readers id <;> simp [apply, found, storeEvent, setReader]

structure Reference (Value : Type) where
  store : Store Value
  readers : Nat → Option (Captured Value)

def referenceInitial (store : Store Value) : Reference Value := ⟨store, fun _ => none⟩

def referenceEvent (reference : Reference Value) (event : Event Value) :
    Reference Value × Reply Value :=
  let result := referenceApply reference.store reference.readers event
  (⟨storeEvent reference.store event, result.1⟩, result.2)

def Related (machine : Machine Value) (reference : Reference Value) : Prop :=
  machine.store = reference.store ∧ captureAll machine = reference.readers ∧ ValidReaders machine

theorem initial_related (store : Store Value) : Related (initial store) (referenceInitial store) := by
  exact ⟨rfl, rfl, valid_initial store⟩

theorem event_related (machine : Machine Value) (reference : Reference Value)
    (related : Related machine reference) (event : Event Value) :
    Related (apply machine event).1 (referenceEvent reference event).1 ∧
      (apply machine event).2 = (referenceEvent reference event).2 := by
  obtain ⟨sameStore, sameReaders, valid⟩ := related
  obtain ⟨captured, reply⟩ := apply_refines machine valid event
  constructor
  · refine ⟨?_, ?_, valid_apply machine valid event⟩
    · rw [apply_store, sameStore]
      rfl
    · rw [captured, sameStore, sameReaders]
      rfl
  · rw [reply, sameStore, sameReaders]
    rfl

def run : Machine Value → List (Event Value) → Machine Value × List (Reply Value)
  | machine, [] => (machine, [])
  | machine, event :: events =>
      let first := apply machine event
      let later := run first.1 events
      (later.1, first.2 :: later.2)

def referenceRun : Reference Value → List (Event Value) → Reference Value × List (Reply Value)
  | reference, [] => (reference, [])
  | reference, event :: events =>
      let first := referenceEvent reference event
      let later := referenceRun first.1 events
      (later.1, first.2 :: later.2)

/-- Every finite interleaving preserves the independently captured entry
views and the exact ordered internal replies, including skip and exhaustion.
There is no restriction on writes by a reader's own body, reader nesting,
reader identity reuse, copies, rewinds, or closing readers out of order. -/
theorem run_related (machine : Machine Value) (reference : Reference Value)
    (related : Related machine reference) (events : List (Event Value)) :
    Related (run machine events).1 (referenceRun reference events).1 ∧
      (run machine events).2 = (referenceRun reference events).2 := by
  induction events generalizing machine reference with
  | nil => exact ⟨related, rfl⟩
  | cons event events ih =>
      obtain ⟨nextRelated, firstReply⟩ := event_related machine reference related event
      obtain ⟨lastRelated, laterReplies⟩ := ih _ _ nextRelated
      exact ⟨lastRelated, by simp only [run, referenceRun, firstReply, laterReplies]⟩

theorem every_schedule_keeps_entry_views (store : Store Value) (events : List (Event Value)) :
    Related (run (initial store) events).1 (referenceRun (referenceInitial store) events).1 ∧
      (run (initial store) events).2 = (referenceRun (referenceInitial store) events).2 :=
  run_related _ _ (initial_related store) events

end Mettapedia.Machines.Cursor.StampedSnapshots
