import Mettapedia.Machines.Cursor.ReaderContraction

/-!
# Joint physical-write and contraction schedules

The finite physical store appends fresh logical IDs, stamps retirement while
retaining payloads, and detaches its registry before dropping retired cells.
The reference captures entry slots at opening and never recomputes them after
a write. This is a sequential reference construction. Its list operations do
not establish constant-time native writes or native allocation/ownership laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderContractionWrites

open StampedSnapshots ReaderContraction

variable {Value : Type}

def Covered (physical : Physical Value) : Prop :=
  ∀ cell ∈ physical.cells, cell.id < physical.next

def add (physical : Physical Value) (value : Value) : Physical Value :=
  ⟨physical.clock + 1, physical.next + 1,
    physical.cells ++ [⟨physical.next, ⟨value, physical.clock + 1, none⟩⟩]⟩

def retireCell (clock id : Nat) (cell : Cell Value) : Cell Value :=
  { cell with record := if cell.id = id then
      match cell.record.death with
      | none => { cell.record with death := some (clock + 1) }
      | some _ => cell.record
    else cell.record }

def remove (physical : Physical Value) (id : Nat) : Physical Value :=
  ⟨physical.clock + 1, physical.next, physical.cells.map (retireCell physical.clock id)⟩

theorem unique_add (physical : Physical Value) (unique : ReaderContraction.Unique physical)
    (covered : Covered physical) (value : Value) : ReaderContraction.Unique (add physical value) := by
  simp only [ReaderContraction.Unique, add, List.map_append, List.map_cons, List.map_nil]
  apply List.Nodup.append unique (by simp)
  intro id old fresh
  obtain ⟨cell, member, same⟩ := List.mem_map.mp old
  have existing := covered cell member
  simp only [List.mem_singleton] at fresh
  omega

theorem covered_add (physical : Physical Value) (covered : Covered physical) (value : Value) :
    Covered (add physical value) := by
  intro cell member
  simp only [add, List.mem_append, List.mem_singleton] at member
  rcases member with old | fresh
  · exact (covered cell old).trans (Nat.lt_succ_self _)
  · cases fresh
    exact Nat.lt_succ_self _

theorem retireCell_id (clock id : Nat) (cell : Cell Value) :
    (retireCell clock id cell).id = cell.id := rfl

theorem retireCell_value (clock id : Nat) (cell : Cell Value) :
    (retireCell clock id cell).record.value = cell.record.value := by
  unfold retireCell
  split
  · split <;> rfl
  · rfl

theorem unique_remove (physical : Physical Value) (unique : ReaderContraction.Unique physical) (id : Nat) :
    ReaderContraction.Unique (remove physical id) := by
  simpa only [ReaderContraction.Unique, remove, List.map_map, Function.comp_def, retireCell_id] using unique

theorem covered_remove (physical : Physical Value) (covered : Covered physical) (id : Nat) :
    Covered (remove physical id) := by
  intro cell member
  obtain ⟨before, found, same⟩ := List.mem_map.mp member
  subst cell
  exact covered before found

theorem covered_compact (physical : Physical Value) (covered : Covered physical) :
    Covered (compact physical) := by
  intro cell member
  have kept : cell ∈ physical.cells.filter (fun cell => visible physical.clock cell.record) := by
    simpa [compact, compactRows_result] using member
  exact covered cell (List.mem_filter.mp kept).1

theorem add_lookup_old (physical : Physical Value) (value : Value) (id : Nat)
    (old : id < physical.next) :
    (logical (add physical value)).row id = (logical physical).row id := by
  dsimp only [logical, add]
  rw [List.find?_append]
  cases found : physical.cells.find? (fun cell => cell.id == id) with
  | none => simp [show physical.next ≠ id by omega]
  | some cell => rfl

theorem visible_retire_past (clock id time : Nat) (cell : Cell Value) (past : time ≤ clock) :
    visible time (retireCell clock id cell).record = visible time cell.record := by
  unfold retireCell
  split
  · cases death : cell.record.death with
    | none => simp [visible, death, show time < clock + 1 by omega]
    | some stamp => rfl
  · rfl

theorem remove_lookup_past (physical : Physical Value) (retired time id : Nat)
    (past : time ≤ physical.clock) :
    atTime (logical (remove physical retired)) time id = atTime (logical physical) time id := by
  simp only [atTime, logical, remove, List.find?_map, Function.comp_def, retireCell_id]
  cases found : physical.cells.find? (fun cell => cell.id == id) with
  | none => rfl
  | some cell =>
      change (if visible time (retireCell physical.clock retired cell).record then
          some (id, (retireCell physical.clock retired cell).record.value) else none) =
        (if visible time cell.record then some (id, cell.record.value) else none)
      rw [visible_retire_past _ _ _ _ past, retireCell_value]

theorem snapshot_add (physical : Physical Value) (value : Value) (reader : Reader)
    (admissible : Admissible (logical physical) reader) :
    snapshot (logical (add physical value)) reader = snapshot (logical physical) reader := by
  apply StampedSnapshots.snapshot_of_slot_agreement
  intro id member
  exact add_lookup_old physical value id (lt_of_lt_of_le member admissible.2)

theorem snapshot_remove (physical : Physical Value) (id : Nat) (reader : Reader)
    (admissible : Admissible (logical physical) reader) :
    snapshot (logical (remove physical id)) reader = snapshot (logical physical) reader := by
  apply List.map_congr_left
  intro other _
  exact remove_lookup_past physical id reader.time other admissible.1

def HandleValid (physical : Physical Value) (entry : Option (Handle Value)) : Prop :=
  ∀ reader, entry = some (.attached reader) → Admissible (logical physical) reader

def ReadersValid (state : Runtime Value) : Prop :=
  ∀ entry ∈ state.readers, HandleValid state.physical entry

theorem valid_set (physical : Physical Value) (readers : List (Option (Handle Value)))
    (valid : ∀ entry ∈ readers, HandleValid physical entry)
    (id : Nat) (entry : Option (Handle Value)) (allowed : HandleValid physical entry) :
    ∀ item ∈ readers.set id entry, HandleValid physical item := by
  intro item member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact valid item old
  · simpa only [same] using allowed

theorem lookup_valid (state : Runtime Value) (valid : ReadersValid state) (id : Nat)
    (handle : Handle Value) (found : lookup state.readers id = some handle) :
    HandleValid state.physical (some handle) := by
  cases cell : state.readers[id]? with
  | none => simp [lookup, cell] at found
  | some entry =>
      cases entry with
      | none => simp [lookup, cell] at found
      | some old =>
          have same : old = handle := by simpa [lookup, cell] using found
          subst old
          exact valid _ (List.mem_of_getElem? cell)

theorem handle_valid_add (physical : Physical Value) (value : Value) (entry : Option (Handle Value))
    (valid : HandleValid physical entry) : HandleValid (add physical value) entry := by
  intro reader same
  obtain ⟨time, ceiling⟩ := valid reader same
  exact ⟨by dsimp [logical, add] at *; omega, by dsimp [logical, add] at *; omega⟩

theorem handle_valid_remove (physical : Physical Value) (id : Nat) (entry : Option (Handle Value))
    (valid : HandleValid physical entry) : HandleValid (remove physical id) entry := by
  intro reader same
  obtain ⟨time, ceiling⟩ := valid reader same
  exact ⟨by dsimp [logical, remove] at *; omega, ceiling⟩

theorem observe_add (physical : Physical Value) (value : Value) (handle : Handle Value)
    (valid : HandleValid physical (some handle)) :
    observe (add physical value) handle = observe physical handle := by
  cases handle with
  | owned saved => rfl
  | attached reader =>
      simp only [observe, capture]
      rw [snapshot_add physical value reader (valid reader rfl)]

theorem observe_remove (physical : Physical Value) (id : Nat) (handle : Handle Value)
    (valid : HandleValid physical (some handle)) :
    observe (remove physical id) handle = observe physical handle := by
  cases handle with
  | owned saved => rfl
  | attached reader =>
      simp only [observe, capture]
      rw [snapshot_remove physical id reader (valid reader rfl)]

theorem observeAll_add (state : Runtime Value) (valid : ReadersValid state) (value : Value) :
    observeAll (add state.physical value) state.readers = observeAll state.physical state.readers := by
  apply List.map_congr_left
  intro entry member
  cases entry with
  | none => rfl
  | some handle =>
      exact congrArg some (observe_add state.physical value handle (valid _ member))

theorem observeAll_remove (state : Runtime Value) (valid : ReadersValid state) (id : Nat) :
    observeAll (remove state.physical id) state.readers = observeAll state.physical state.readers := by
  apply List.map_congr_left
  intro entry member
  cases entry with
  | none => rfl
  | some handle =>
      exact congrArg some (observe_remove state.physical id handle (valid _ member))

theorem detached_readers_valid (before after : Physical Value) (handles : List (Option (Handle Value))) :
    ∀ entry ∈ (detachAll before handles).1, HandleValid after entry := by
  induction handles with
  | nil => simp [detachAll]
  | cons entry rest ih =>
      cases entry with
      | none => simpa [detachAll, HandleValid] using ih
      | some handle => cases handle <;> simpa [detachAll, detach, HandleValid] using ih

theorem readers_valid_operation (state : Runtime Value) (valid : ReadersValid state) (op : Op) :
    ReadersValid (ReaderContraction.apply state op).1 := by
  cases op with
  | compact => exact detached_readers_valid _ _ _
  | close id =>
      apply valid_set state.physical state.readers valid id none
      intro reader same
      cases same
  | openReader id =>
      apply valid_set state.physical state.readers valid id (some (.attached (start (logical state.physical))))
      intro reader same
      cases same
      exact ⟨le_rfl, le_rfl⟩
  | clone source target back =>
      cases found : lookup state.readers source with
      | none =>
          simp only [ReaderContraction.apply, found, Option.map_none]
          apply valid_set state.physical state.readers valid target none
          intro reader same
          cases same
      | some handle =>
          have old := lookup_valid state valid source handle found
          simp only [ReaderContraction.apply, found, Option.map_some]
          apply valid_set state.physical state.readers valid target
          cases handle with
          | owned saved => intro reader same; cases same
          | attached before =>
              intro reader same
              cases same
              cases back <;> exact old before rfl
  | read id =>
      cases found : lookup state.readers id with
      | none => simpa [ReaderContraction.apply, found] using valid
      | some handle =>
          have old := lookup_valid state valid id handle found
          simp only [ReaderContraction.apply, found]
          apply valid_set state.physical state.readers valid id
          cases handle with
          | owned saved => intro reader same; cases same
          | attached before =>
              intro reader same
              cases same
              exact StampedSnapshots.admissible_step _ before (old before rfl)

theorem covered_operation (state : Runtime Value) (covered : Covered state.physical) (op : Op) :
    Covered (ReaderContraction.apply state op).1.physical := by
  cases op with
  | compact => exact covered_compact state.physical covered
  | clone source target back => exact covered
  | close id => exact covered
  | openReader id => exact covered
  | read id => cases found : lookup state.readers id <;> simpa [ReaderContraction.apply, found] using covered

def Valid (state : Runtime Value) : Prop :=
  ReaderContraction.Unique state.physical ∧ Covered state.physical ∧ ReadersValid state

/-- Allocate enough finite registry cells for the requested target. There is
no fixed reader limit and an out-of-range open is not silently dropped. -/
def reserve {Item : Type} (items : List (Option Item)) (target : Nat) : List (Option Item) :=
  items ++ List.replicate (target + 1 - items.length) none

theorem reserve_contains_target {Item : Type} (items : List (Option Item)) (target : Nat) :
    target < (reserve items target).length := by
  simp only [reserve, List.length_append, List.length_replicate]
  omega

theorem observeAll_reserve (physical : Physical Value) (items : List (Option (Handle Value)))
    (target : Nat) :
    observeAll physical (reserve items target) = reserve (observeAll physical items) target := by
  simp [observeAll, reserve, List.map_append, List.map_replicate]

theorem lookup_reserve {Item : Type} (items : List (Option Item)) (target id : Nat) :
    lookup (reserve items target) id = lookup items id := by
  by_cases old : id < items.length
  · simp only [lookup, reserve, List.getElem?_append_left old]
  · simp only [lookup, reserve, List.getElem?_append, if_neg old]
    have absent : items[id]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp only [absent]
    rw [List.getElem?_replicate]
    split <;> rfl

theorem valid_reserve (physical : Physical Value) (items : List (Option (Handle Value)))
    (valid : ∀ entry ∈ items, HandleValid physical entry) (target : Nat) :
    ∀ entry ∈ reserve items target, HandleValid physical entry := by
  intro entry member
  simp only [reserve, List.mem_append, List.mem_replicate] at member
  rcases member with old | allocated
  · exact valid entry old
  · obtain ⟨_, same⟩ := allocated
    rw [same]
    intro reader impossible
    cases impossible

def reserveFor {Item : Type} (items : List (Option Item)) : Op → List (Option Item)
  | .openReader target | .clone _ target _ => reserve items target
  | .read _ | .close _ | .compact => items

def prepare (state : Runtime Value) (op : Op) : Runtime Value :=
  ⟨state.physical, reserveFor state.readers op⟩

theorem prepare_valid (state : Runtime Value) (valid : ReadersValid state) (op : Op) :
    ReadersValid (prepare state op) := by
  cases op with
  | openReader target => exact valid_reserve _ _ valid target
  | clone source target back => exact valid_reserve _ _ valid target
  | read id => exact valid
  | close id => exact valid
  | compact => exact valid

theorem observeAll_prepare (state : Runtime Value) (op : Op) :
    observeAll (prepare state op).physical (prepare state op).readers =
      reserveFor (observeAll state.physical state.readers) op := by
  cases op with
  | openReader target => exact observeAll_reserve _ _ _
  | clone source target back => exact observeAll_reserve _ _ _
  | read id => rfl
  | close id => rfl
  | compact => rfl

inductive Event (Value : Type) where
  | add (value : Value)
  | remove (id : Nat)
  | control (op : Op)
  deriving Repr, DecidableEq

def apply (state : Runtime Value) : Event Value → Runtime Value × Reply Value
  | .add value => (⟨add state.physical value, state.readers⟩, .silent)
  | .remove id => (⟨remove state.physical id, state.readers⟩, .silent)
  | .control op => ReaderContraction.apply (prepare state op) op

theorem open_allocates_target (state : Runtime Value) (target : Nat) :
    (apply state (.control (.openReader target))).1.readers[target]? =
      some (some (.attached (start (logical state.physical)))) := by
  simp only [apply, ReaderContraction.apply, prepare, reserveFor]
  exact List.getElem?_set_self (reserve_contains_target state.readers target)

def nextPhysical (physical : Physical Value) : Event Value → Physical Value
  | .add value => add physical value
  | .remove id => remove physical id
  | .control .compact => compact physical
  | .control _ => physical

/-- The reference keeps each already captured entry unchanged on every write
and contraction. Only opening a new reader consults the then-current store. -/
def referenceApply (physical : Physical Value) (readers : List (Option (Captured Value))) :
    Event Value → List (Option (Captured Value)) × Reply Value
  | .add _ | .remove _ => (readers, .silent)
  | .control op => ReaderContraction.referenceApply (current physical) (reserveFor readers op) op

theorem control_physical (state : Runtime Value) (op : Op) :
    (ReaderContraction.apply state op).1.physical = nextPhysical state.physical (.control op) := by
  cases op with
  | compact => rfl
  | clone source target back => rfl
  | openReader id => rfl
  | close id => rfl
  | read id => cases found : lookup state.readers id <;> simp [ReaderContraction.apply, found, nextPhysical]

theorem event_refines (state : Runtime Value) (valid : Valid state) (event : Event Value) :
    Valid (apply state event).1 ∧
      observeAll (apply state event).1.physical (apply state event).1.readers =
        (referenceApply state.physical (observeAll state.physical state.readers) event).1 ∧
      (apply state event).2 =
        (referenceApply state.physical (observeAll state.physical state.readers) event).2 ∧
      (apply state event).1.physical = nextPhysical state.physical event := by
  obtain ⟨unique, covered, readers⟩ := valid
  cases event with
  | add value =>
      refine ⟨⟨unique_add _ unique covered value, covered_add _ covered value, ?_⟩,
        observeAll_add _ readers value, rfl, rfl⟩
      intro entry member
      exact handle_valid_add _ value entry (readers entry member)
  | remove id =>
      refine ⟨⟨unique_remove _ unique id, covered_remove _ covered id, ?_⟩,
        observeAll_remove _ readers id, rfl, rfl⟩
      intro entry member
      exact handle_valid_remove _ id entry (readers entry member)
  | control op =>
      obtain ⟨nextUnique, _, sameReaders, sameReply⟩ :=
        ReaderContraction.operation_refines (prepare state op) unique op
      rw [observeAll_prepare] at sameReaders sameReply
      exact ⟨⟨nextUnique, covered_operation (prepare state op) covered op,
          readers_valid_operation (prepare state op) (prepare_valid state readers op) op⟩,
        sameReaders, sameReply, control_physical (prepare state op) op⟩

def run : Runtime Value → List (Event Value) → Runtime Value × List (Reply Value)
  | state, [] => (state, [])
  | state, event :: events =>
      let first := apply state event
      let later := run first.1 events
      (later.1, first.2 :: later.2)

def referenceRun : Physical Value → List (Option (Captured Value)) → List (Event Value) →
    List (Option (Captured Value)) × List (Reply Value)
  | _, readers, [] => (readers, [])
  | physical, readers, event :: events =>
      let first := referenceApply physical readers event
      let later := referenceRun (nextPhysical physical event) first.1 events
      (later.1, first.2 :: later.2)

/-- A single joint scheduler now permits arbitrary interleaving of append,
retirement, reads, opens, closes, copies/rewinds and physical contractions.
The concrete finite registry earns exactly the independently captured entry
observations, including original rewind rights and ordered internal replies. -/
theorem every_joint_schedule (state : Runtime Value) (valid : Valid state) (events : List (Event Value)) :
    Valid (run state events).1 ∧
      observeAll (run state events).1.physical (run state events).1.readers =
        (referenceRun state.physical (observeAll state.physical state.readers) events).1 ∧
      (run state events).2 =
        (referenceRun state.physical (observeAll state.physical state.readers) events).2 := by
  induction events generalizing state with
  | nil => exact ⟨valid, rfl, rfl⟩
  | cons event events ih =>
      obtain ⟨nextValid, sameReaders, sameReply, samePhysical⟩ := event_refines state valid event
      obtain ⟨laterValid, laterReaders, laterReplies⟩ := ih (apply state event).1 nextValid
      simp only [run, referenceRun]
      rw [sameReaders, samePhysical] at laterReaders laterReplies
      exact ⟨laterValid, laterReaders, by rw [sameReply, laterReplies]⟩

end Mettapedia.Machines.Cursor.ReaderContractionWrites
