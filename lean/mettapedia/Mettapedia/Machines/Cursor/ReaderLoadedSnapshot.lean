import Mettapedia.Machines.Cursor.StampedSnapshots

/-!
# Pending-aware physical residency over a logical slot store

The authoritative store names logical records; it is not a claim that all
payloads are physically resident. The cache distinguishes an unloaded slot
from a loaded authoritative absence. Loading copies one complete record,
including its original identity and temporal metadata, without adding a
logical occurrence or changing a reader's entry view.

Writes invalidate only their edited cache slot. A loaded read either agrees
with the stamped reader step or reports pending without advancing. Native I/O,
concurrent fetch/publication, packed layouts and memory costs are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderLoadedSnapshot

open StampedSnapshots

variable {Value : Type}

abbrev Cache (Value : Type) := Nat → Option (Option (Row Value))

def CacheValid (store : Store Value) (cache : Cache Value) : Prop :=
  ∀ id value, cache id = some value → value = store.row id

def unloaded : Cache Value := fun _ => none

def load (store : Store Value) (cache : Cache Value) (id : Nat) : Cache Value :=
  Function.update cache id (some (store.row id))

def invalidate (cache : Cache Value) (id : Nat) : Cache Value :=
  Function.update cache id none

theorem valid_unloaded (store : Store Value) : CacheValid store unloaded := by
  intro id value loaded
  cases loaded

theorem valid_load (store : Store Value) (cache : Cache Value)
    (valid : CacheValid store cache) (id : Nat) : CacheValid store (load store cache id) := by
  intro other value loaded
  by_cases same : other = id
  · subst other
    simpa [load] using loaded.symm
  · exact valid other value (by simpa [load, Function.update_of_ne same] using loaded)

theorem load_only_requested (store : Store Value) (cache : Cache Value) (id other : Nat)
    (different : other ≠ id) : load store cache id other = cache other := by
  simp [load, Function.update_of_ne different]

theorem valid_invalidate_of_unchanged (before after : Store Value) (cache : Cache Value)
    (valid : CacheValid before cache) (id : Nat)
    (unchanged : ∀ other, other ≠ id → after.row other = before.row other) :
    CacheValid after (invalidate cache id) := by
  intro other value loaded
  by_cases same : other = id
  · subst other
    simp [invalidate] at loaded
  · rw [unchanged other same]
    exact valid other value (by simpa [invalidate, Function.update_of_ne same] using loaded)

structure State (Value : Type) where
  source : Store Value
  cache : Cache Value

def loadSlot (state : State Value) (id : Nat) : State Value :=
  { state with cache := load state.source state.cache id }

def add (state : State Value) (value : Value) : State Value :=
  ⟨StampedSnapshots.add state.source value, invalidate state.cache state.source.next⟩

def remove (state : State Value) (id : Nat) : State Value :=
  ⟨StampedSnapshots.remove state.source id, invalidate state.cache id⟩

theorem valid_loadSlot (state : State Value) (valid : CacheValid state.source state.cache) (id : Nat) :
    CacheValid (loadSlot state id).source (loadSlot state id).cache := valid_load _ _ valid id

theorem valid_add (state : State Value) (valid : CacheValid state.source state.cache) (value : Value) :
    CacheValid (add state value).source (add state value).cache := by
  apply valid_invalidate_of_unchanged state.source _ state.cache valid state.source.next
  intro other different
  simp [add, StampedSnapshots.add, Function.update_of_ne different]

theorem remove_other_slot (store : Store Value) (id other : Nat) (different : other ≠ id) :
    (StampedSnapshots.remove store id).row other = store.row other := by
  unfold StampedSnapshots.remove
  cases found : store.row id with
  | none => rfl
  | some row =>
      cases death : row.death with
      | some time => simp [death]
      | none => simp [death, Function.update_of_ne different]

theorem valid_remove (state : State Value) (valid : CacheValid state.source state.cache) (id : Nat) :
    CacheValid (remove state id).source (remove state id).cache := by
  apply valid_invalidate_of_unchanged state.source _ state.cache valid id
  exact remove_other_slot state.source id

/-- These are the loader's actual effects. It never assigns a new occurrence
ID or birth timestamp while bringing an existing record into residency. -/
theorem load_preserves_source_and_record (state : State Value) (id : Nat) :
    (loadSlot state id).source = state.source ∧
      (loadSlot state id).cache id = some (state.source.row id) := by
  exact ⟨rfl, by simp [loadSlot, load]⟩

theorem load_preserves_entry_view (state : State Value) (id : Nat) (reader : Reader) :
    snapshot (loadSlot state id).source reader = snapshot state.source reader := rfl

inductive Result (Value : Type) where
  | pending (reader : Reader)
  | ready (reply : Reply Value) (reader : Reader)
  deriving Repr, DecidableEq

/-- This operation reads only the physical cache, not the logical oracle.
Unloaded data suspends at the same position. A loaded absence skips a slot;
only the reader ceiling establishes exhaustion. -/
def step (cache : Cache Value) (reader : Reader) : Result Value :=
  if reader.position < reader.ceiling then
    match cache reader.position with
    | none => .pending reader
    | some row =>
        let answer := do
          let record ← row
          if visible reader.time record then some (reader.position, record.value) else none
        .ready (slotReply answer) { reader with position := reader.position + 1 }
  else .ready .exhausted reader

def Refines (store : Store Value) (reader : Reader) : Result Value → Prop
  | .pending kept => kept = reader
  | .ready reply next => (reply, next) = StampedSnapshots.step store reader

theorem step_refines (store : Store Value) (cache : Cache Value) (valid : CacheValid store cache)
    (reader : Reader) : Refines store reader (step cache reader) := by
  by_cases within : reader.position < reader.ceiling
  · cases loaded : cache reader.position with
    | none => simp [step, within, loaded, Refines]
    | some row =>
        have same := valid reader.position row loaded
        simp only [step, within, if_pos, loaded, Refines, StampedSnapshots.step, atTime]
        rw [same]
  · simp [step, within, Refines, StampedSnapshots.step]

theorem pending_keeps_position (cache : Cache Value) (reader : Reader)
    (within : reader.position < reader.ceiling) (missing : cache reader.position = none) :
    step cache reader = .pending reader := by simp [step, within, missing]

/-- Once this requested slot has loaded, no global residency premise is
needed: the very next step is exactly the logical stamped reader step. -/
theorem step_after_load (store : Store Value) (cache : Cache Value) (reader : Reader) :
    step (load store cache reader.position) reader =
      .ready (StampedSnapshots.step store reader).1 (StampedSnapshots.step store reader).2 := by
  by_cases within : reader.position < reader.ceiling
  · simp [step, load, within, StampedSnapshots.step, atTime]
  · simp [step, within, StampedSnapshots.step]

end Mettapedia.Machines.Cursor.ReaderLoadedSnapshot
