import Mettapedia.Languages.MeTTa.MetavariableFrame

/-!
# Generational indexed stores for metavariable frames

The directory and each frame's values are arrays. A reference carries a
directory handle, allocation generation, and slot; lookup does not inspect
variable names. An outer `none` means an invalid reference, whereas `some none`
means a valid, unbound slot.

The first model uses unbounded natural generations within one store lineage.
Rollback restores a saved directory but retains the current allocation
counter; its invariant requires a snapshot from an earlier counter. The
`Shared` model instead gives branch images one finite-generation allocator,
checked owner-count transitions, and permanent retirement at exhaustion.
Independent allocators do not share an identity namespace. Payloads here are
inductive `Atom` values, not borrowed pointers. Relating either protocol to
runtime pointer ownership, C code, or physical complexity remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrame (Frame Slot FrameEnv)

/-- Coordinates are interpreted only in their owning store lineage. -/
structure Ref where
  handle : Nat
  generation : Nat
  slot : Nat
  deriving DecidableEq, Repr

/-- The authored inventory remains available for the named semantic boundary. -/
structure Entry where
  generation : Nat
  frame : Frame
  values : Array (Option Atom)
  size_eq : values.size = frame.length

structure Store where
  entries : Array (Option Entry)
  nextGeneration : Nat

def empty (capacity : Nat) : Store :=
  ⟨Array.replicate capacity none, 0⟩

def frameAt (store : Store) (handle : Nat) : Option Entry :=
  (store.entries[handle]?).getD none

def lookup (store : Store) (ref : Ref) : Option (Option Atom) := do
  let entry ← frameAt store ref.handle
  if entry.generation = ref.generation then entry.values[ref.slot]? else none

/-- Every installed generation has already been consumed by the allocator. -/
def WellFormed (store : Store) : Prop :=
  ∀ handle entry, frameAt store handle = some entry →
    entry.generation < store.nextGeneration

private def replace (store : Store) (handle : Nat) (entry : Entry) : Store :=
  { store with entries := store.entries.setIfInBounds handle (some entry) }

private theorem frameAt_replace_self (store : Store) (handle : Nat)
    (bound : handle < store.entries.size) (entry : Entry) :
    frameAt (replace store handle entry) handle = some entry := by
  simp [frameAt, replace, Array.getElem?_setIfInBounds_self_of_lt bound]

private theorem frameAt_replace_other (store : Store) (handle other : Nat)
    (distinct : handle ≠ other) (entry : Entry) :
    frameAt (replace store handle entry) other = frameAt store other := by
  simp [frameAt, replace, Array.getElem?_setIfInBounds_ne distinct]

private theorem frameAt_bound {store : Store} {handle : Nat} {entry : Entry}
    (present : frameAt store handle = some entry) : handle < store.entries.size := by
  by_contra outside
  simp [frameAt, Array.getElem?_eq_none (Nat.not_lt.mp outside)] at present

/-- Replace any prior activation at this handle by a fresh allocation. -/
def install (store : Store) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnv frame) : Store :=
  { entries := store.entries.setIfInBounds handle.val
      (some ⟨store.nextGeneration, frame, Array.ofFn env, by simp⟩)
    nextGeneration := store.nextGeneration + 1 }

def allocatedRef (store : Store) (handle : Fin store.entries.size)
    {frame : Frame} (slot : Slot frame) : Ref :=
  ⟨handle.val, store.nextGeneration, slot.val⟩

/-- Convert the concrete array back to the existing semantic frame carrier. -/
def entryEnv (entry : Entry) : FrameEnv entry.frame :=
  fun slot => entry.values[slot.val]'(by rw [entry.size_eq]; exact slot.isLt)

theorem lookup_of_frameAt {store : Store} {ref : Ref} {entry : Entry}
    (present : frameAt store ref.handle = some entry)
    (generation : entry.generation = ref.generation) :
    lookup store ref = entry.values[ref.slot]? := by
  simp [lookup, present, generation]

theorem lookup_stale {store : Store} {ref : Ref} {entry : Entry}
    (present : frameAt store ref.handle = some entry)
    (stale : entry.generation ≠ ref.generation) : lookup store ref = none := by
  simp [lookup, present, stale]

theorem lookup_slot {store : Store} {handle : Nat} {entry : Entry}
    (present : frameAt store handle = some entry) (slot : Slot entry.frame) :
    lookup store ⟨handle, entry.generation, slot.val⟩ = some (entryEnv entry slot) := by
  rw [lookup_of_frameAt present rfl]
  simp [entryEnv]

theorem lookup_named {store : Store} {handle : Nat} {entry : Entry}
    (present : frameAt store handle = some entry) (unique : entry.frame.Nodup)
    (slot : Slot entry.frame) :
    lookup store ⟨handle, entry.generation, slot.val⟩ =
      some (MetavariableFrame.denote (entryEnv entry) (MetavariableFrame.nameOf slot)) := by
  rw [MetavariableFrame.denote_nameOf unique]
  exact lookup_slot present slot

theorem frameAt_install_self (store : Store) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnv frame) :
    frameAt (install store handle frame env) handle.val =
      some ⟨store.nextGeneration, frame, Array.ofFn env, by simp⟩ := by
  simp [frameAt, install]

theorem lookup_install (store : Store) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnv frame) (slot : Slot frame) :
    lookup (install store handle frame env) (allocatedRef store handle slot) =
      some (env slot) := by
  simp [lookup, allocatedRef, frameAt_install_self, slot.isLt]

theorem lookup_install_other (store : Store) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnv frame) (ref : Ref)
    (distinct : handle.val ≠ ref.handle) :
    lookup (install store handle frame env) ref = lookup store ref := by
  simp [lookup, frameAt, install, Array.getElem?_setIfInBounds_ne distinct]

/-- Reusing a handle rejects every older generation, for every slot. -/
theorem lookup_install_stale (store : Store) (handle : Fin store.entries.size)
    (frame : Frame) (env : FrameEnv frame) (generation slot : Nat)
    (older : generation < store.nextGeneration) :
    lookup (install store handle frame env) ⟨handle.val, generation, slot⟩ = none := by
  apply lookup_stale (frameAt_install_self store handle frame env)
  exact Nat.ne_of_gt older

theorem reuse_rejects_old {store : Store} (wellFormed : WellFormed store)
    (handle : Fin store.entries.size) {old : Entry}
    (present : frameAt store handle.val = some old)
    (frame : Frame) (env : FrameEnv frame) (slot : Nat) :
    lookup (install store handle frame env) ⟨handle.val, old.generation, slot⟩ = none :=
  lookup_install_stale store handle frame env old.generation slot
    (wellFormed handle.val old present)

private def updateEntry (entry : Entry) (slot : Nat) (value : Option Atom) : Entry :=
  { entry with
    values := entry.values.setIfInBounds slot value
    size_eq := by simpa using entry.size_eq }

/-- Writes reject missing frames, stale generations, and invalid slots. -/
def write? (store : Store) (ref : Ref) (value : Option Atom) : Option Store := do
  let entry ← frameAt store ref.handle
  if entry.generation = ref.generation ∧ ref.slot < entry.values.size then
    some (replace store ref.handle (updateEntry entry ref.slot value))
  else none

theorem write?_valid {store : Store} {ref : Ref} {entry : Entry}
    (present : frameAt store ref.handle = some entry)
    (generation : entry.generation = ref.generation)
    (bound : ref.slot < entry.values.size) (value : Option Atom) :
    write? store ref value =
      some (replace store ref.handle (updateEntry entry ref.slot value)) := by
  simp [write?, present, generation, bound]

theorem write?_stale {store : Store} {ref : Ref} {entry : Entry}
    (present : frameAt store ref.handle = some entry)
    (stale : entry.generation ≠ ref.generation) (value : Option Atom) :
    write? store ref value = none := by
  simp [write?, present, stale]

private theorem write?_success {store next : Store} {ref : Ref} {value : Option Atom}
    (written : write? store ref value = some next) :
    ∃ entry, frameAt store ref.handle = some entry ∧
      entry.generation = ref.generation ∧ ref.slot < entry.values.size ∧
      next = replace store ref.handle (updateEntry entry ref.slot value) := by
  cases present : frameAt store ref.handle with
  | none => simp [write?, present] at written
  | some entry =>
    simp only [write?, present] at written
    change (if entry.generation = ref.generation ∧ ref.slot < entry.values.size then
      some (replace store ref.handle (updateEntry entry ref.slot value)) else none) =
      some next at written
    split at written
    · next valid =>
      exact ⟨entry, rfl, valid.1, valid.2, (Option.some.inj written).symm⟩
    · simp at written

theorem lookup_write {store next : Store} {ref : Ref} {value : Option Atom}
    (written : write? store ref value = some next) : lookup next ref = some value := by
  obtain ⟨entry, present, generation, bound, rfl⟩ := write?_success written
  rw [lookup_of_frameAt (entry := updateEntry entry ref.slot value)
    (frameAt_replace_self store ref.handle (frameAt_bound present) _) generation]
  simp [updateEntry, Array.getElem?_setIfInBounds_self_of_lt bound]

/-- Every reference with different coordinates retains its old observation. -/
theorem lookup_write_other {store next : Store} {ref other : Ref} {value : Option Atom}
    (written : write? store ref value = some next) (distinct : other ≠ ref) :
    lookup next other = lookup store other := by
  obtain ⟨entry, present, generation, bound, rfl⟩ := write?_success written
  by_cases sameHandle : ref.handle = other.handle
  · have otherPresent : frameAt store other.handle = some entry := sameHandle ▸ present
    have changedPresent :
        frameAt (replace store ref.handle (updateEntry entry ref.slot value)) other.handle =
          some (updateEntry entry ref.slot value) := by
      rw [← sameHandle]
      exact frameAt_replace_self store ref.handle (frameAt_bound present) _
    by_cases sameGeneration : entry.generation = other.generation
    · have differentSlot : ref.slot ≠ other.slot := by
        intro sameSlot
        apply distinct
        cases ref
        cases other
        simp_all
      rw [lookup_of_frameAt changedPresent sameGeneration,
        lookup_of_frameAt otherPresent sameGeneration]
      simp [updateEntry, Array.getElem?_setIfInBounds_ne differentSlot]
    · rw [lookup_stale changedPresent sameGeneration, lookup_stale otherPresent sameGeneration]
  · simp [lookup, frameAt_replace_other store ref.handle other.handle sameHandle]

theorem write_preserves_counter {store next : Store} {ref : Ref} {value : Option Atom}
    (written : write? store ref value = some next) :
    next.nextGeneration = store.nextGeneration := by
  obtain ⟨_, _, _, _, rfl⟩ := write?_success written
  rfl

/-- Snapshot rollback restores all values and identities but not allocation history. -/
def rollback (current saved : Store) : Store :=
  { entries := saved.entries, nextGeneration := current.nextGeneration }

theorem lookup_rollback (current saved : Store) (ref : Ref) :
    lookup (rollback current saved) ref = lookup saved ref := by
  simp [lookup, frameAt, rollback]

theorem rollback_preserves_counter (current saved : Store) :
    (rollback current saved).nextGeneration = current.nextGeneration := rfl

theorem empty_wellFormed (capacity : Nat) : WellFormed (empty capacity) := by
  intro handle entry present
  simp [frameAt, empty, Array.getElem?_replicate] at present
  split at present <;> simp_all

theorem install_wellFormed {store : Store} (wellFormed : WellFormed store)
    (handle : Fin store.entries.size) (frame : Frame) (env : FrameEnv frame) :
    WellFormed (install store handle frame env) := by
  intro other entry present
  by_cases same : handle.val = other
  · subst other
    rw [frameAt_install_self] at present
    cases Option.some.inj present
    exact Nat.lt_succ_self _
  · have oldPresent : frameAt store other = some entry := by
      simpa [frameAt, install, Array.getElem?_setIfInBounds_ne same] using present
    exact Nat.lt_trans (wellFormed other entry oldPresent) (Nat.lt_succ_self _)

theorem write_wellFormed {store next : Store} (wellFormed : WellFormed store)
    {ref : Ref} {value : Option Atom} (written : write? store ref value = some next) :
    WellFormed next := by
  obtain ⟨entry, present, _, _, rfl⟩ := write?_success written
  intro handle found foundPresent
  by_cases same : ref.handle = handle
  · subst handle
    rw [frameAt_replace_self store ref.handle (frameAt_bound present)] at foundPresent
    cases Option.some.inj foundPresent
    exact wellFormed ref.handle entry present
  · rw [frameAt_replace_other store ref.handle handle same] at foundPresent
    exact wellFormed handle found foundPresent

theorem rollback_wellFormed {current saved : Store} (savedValid : WellFormed saved)
    (earlier : saved.nextGeneration ≤ current.nextGeneration) :
    WellFormed (rollback current saved) := by
  intro handle entry present
  exact Nat.lt_of_lt_of_le (savedValid handle entry present) earlier

/-- Undoing a write restores each observation, including the overwritten slot. -/
theorem rollback_write {store next : Store} {ref : Ref} {value : Option Atom}
    (written : write? store ref value = some next) (observed : Ref) :
    lookup (rollback next store) observed = lookup store observed ∧
      (rollback next store).nextGeneration = store.nextGeneration := by
  exact ⟨lookup_rollback next store observed, by
    rw [rollback_preserves_counter, write_preserves_counter written]⟩

/-- An allocation discarded by rollback is not revived by the next reuse. -/
theorem rollback_reallocate_rejects_discarded (saved : Store)
    (handle : Fin saved.entries.size) (oldFrame newFrame : Frame)
    (oldEnv : FrameEnv oldFrame) (newEnv : FrameEnv newFrame) (slot : Slot oldFrame) :
    let speculative := install saved handle oldFrame oldEnv
    let restored := rollback speculative saved
    lookup (install restored handle newFrame newEnv) (allocatedRef saved handle slot) =
      none := by
  apply lookup_install_stale
  exact Nat.lt_succ_self _

/-- Allocation after rollback consumes the current counter, regardless of the saved one. -/
theorem rollback_reallocate_generation (current saved : Store)
    (handle : Fin saved.entries.size) {frame : Frame} (slot : Slot frame) :
    (allocatedRef (rollback current saved) handle slot).generation =
      current.nextGeneration := rfl

/-! ## Concrete canaries

These exercise two slots and two handles, failed writes, handle reuse, and a
discarded speculative generation. All computation is checked by the kernel.
-/

private def sampleFrame : Frame := ["x", "y"]

private def sampleEnv : FrameEnv sampleFrame :=
  fun slot => if slot.val = 0 then some (.symbol "before") else none

private def sampleInitial : Store :=
  install (empty 2) ⟨0, by decide⟩ sampleFrame sampleEnv

private def sampleSpeculative : Store :=
  install sampleInitial ⟨0, by decide⟩ sampleFrame (fun _ => some (.symbol "speculative"))

private def sampleRestored : Store := rollback sampleSpeculative sampleInitial

private def sampleReallocated : Store :=
  install sampleRestored ⟨0, by decide⟩ sampleFrame (fun _ => some (.symbol "new"))

theorem canary_bound_value :
    lookup sampleInitial ⟨0, 0, 0⟩ = some (some (.symbol "before")) := by decide

theorem canary_unbound_is_valid : lookup sampleInitial ⟨0, 0, 1⟩ = some none := by decide

theorem canary_missing_handle : lookup sampleInitial ⟨1, 0, 0⟩ = none := by decide

theorem canary_invalid_slot : lookup sampleInitial ⟨0, 0, 2⟩ = none := by decide

theorem canary_write_changes_value :
    (write? sampleInitial ⟨0, 0, 0⟩ (some (.symbol "after"))).map
      (fun next => lookup next ⟨0, 0, 0⟩) = some (some (some (.symbol "after"))) := by decide

theorem canary_write_preserves_other_slot :
    (write? sampleInitial ⟨0, 0, 0⟩ (some (.symbol "after"))).map
      (fun next => lookup next ⟨0, 0, 1⟩) = some (some none) := by decide

theorem canary_write_clears_value :
    (write? sampleInitial ⟨0, 0, 0⟩ none).map
      (fun next => lookup next ⟨0, 0, 0⟩) = some (some none) := by decide

theorem canary_stale_write_rejected :
    (write? sampleSpeculative ⟨0, 0, 0⟩ (some (.symbol "wrong"))).isSome = false := by decide

theorem canary_invalid_slot_write_rejected :
    (write? sampleInitial ⟨0, 0, 2⟩ (some (.symbol "wrong"))).isSome = false := by decide

theorem canary_second_handle_preserves_first :
    lookup (install sampleInitial ⟨1, by decide⟩ sampleFrame
      (fun _ => some (.symbol "second"))) ⟨0, 0, 0⟩ =
        some (some (.symbol "before")) := by decide

theorem canary_reuse_rejects_old_generation :
    lookup sampleSpeculative ⟨0, 0, 0⟩ = none := by decide

theorem canary_rollback_restores_old_value :
    lookup sampleRestored ⟨0, 0, 0⟩ = some (some (.symbol "before")) := by decide

theorem canary_rollback_discards_speculative_generation :
    lookup sampleRestored ⟨0, 1, 0⟩ = none := by decide

theorem canary_rollback_does_not_rewind_counter : sampleRestored.nextGeneration = 2 := by decide

theorem canary_reallocation_rejects_discarded_generation :
    lookup sampleReallocated ⟨0, 1, 0⟩ = none := by decide

theorem canary_reallocation_uses_fresh_generation :
    lookup sampleReallocated ⟨0, 2, 0⟩ = some (some (.symbol "new")) := by decide

/-- The same coordinates in an independent store can denote a different value:
the caller must retain the owning store lineage along with an escaped reference. -/
theorem canary_coordinates_require_owner :
    lookup sampleInitial ⟨0, 0, 0⟩ ≠
      lookup (install (empty 2) ⟨0, by decide⟩ sampleFrame
        (fun _ => some (.symbol "foreign"))) ⟨0, 0, 0⟩ := by decide

theorem canary_execution_wellFormed : WellFormed sampleReallocated := by
  apply install_wellFormed
  apply rollback_wellFormed
  · exact install_wellFormed (empty_wellFormed 2) _ _ _
  · decide

/-- A future snapshot cannot be installed into an earlier allocation history. -/
theorem canary_future_snapshot_breaks_invariant :
    ¬ WellFormed (rollback (empty 2) sampleInitial) := by
  intro valid
  have impossible := valid 0 ⟨0, sampleFrame, Array.ofFn sampleEnv, by simp⟩ (by
    simp [rollback, frameAt, sampleInitial, install, empty])
  exact Nat.not_lt_zero _ impossible

/-! ## A shared finite-generation allocator

`Shared.Allocator` is one identity authority shared by all branch images.
Owner counts are manipulated by concrete checked retain/release operations.
They model a protocol, not a proof that runtime pointers follow that protocol.
The final release advances the handle's generation; an exhausted handle is
permanently unavailable. Branch rollback never rewinds this allocator.
-/

namespace Shared

structure Token where
  handle : Nat
  generation : Nat
  deriving DecidableEq, Repr

def Token.ref (token : Token) (slot : Nat) : Ref :=
  ⟨token.handle, token.generation, slot⟩

structure Cell where
  generation : Nat
  owners : Nat
  deriving DecidableEq, Repr

structure Allocator where
  cells : Array Cell
  generationBound : Nat
  deriving DecidableEq, Repr

def Allocator.empty (capacity generationBound : Nat) : Allocator :=
  ⟨Array.replicate capacity ⟨0, 0⟩, generationBound⟩

def Live (allocator : Allocator) (token : Token) : Prop :=
  match allocator.cells[token.handle]? with
  | some cell => cell.generation = token.generation ∧ 0 < cell.owners
  | none => False

instance (allocator : Allocator) (token : Token) : Decidable (Live allocator token) := by
  unfold Live
  split <;> infer_instance

def Retired (allocator : Allocator) (handle : Nat) : Prop :=
  match allocator.cells[handle]? with
  | some cell => cell.owners = 0 ∧ allocator.generationBound ≤ cell.generation
  | none => False

instance (allocator : Allocator) (handle : Nat) : Decidable (Retired allocator handle) := by
  unfold Retired
  split <;> infer_instance

/-- The finite bound permits its endpoint only for a retired, unowned cell. -/
def Allocator.WellFormed (allocator : Allocator) : Prop :=
  ∀ (handle : Nat) (cell : Cell), allocator.cells[handle]? = some cell →
    cell.generation ≤ allocator.generationBound ∧
      (0 < cell.owners → cell.generation < allocator.generationBound)

private def put (allocator : Allocator) (handle : Nat) (cell : Cell) : Allocator :=
  { allocator with cells := allocator.cells.setIfInBounds handle cell }

private theorem present_bound {allocator : Allocator} {handle : Nat} {cell : Cell}
    (present : allocator.cells[handle]? = some cell) : handle < allocator.cells.size := by
  obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp present
  exact bound

private theorem put_self {allocator : Allocator} {handle : Nat} {old : Cell}
    (present : allocator.cells[handle]? = some old) (cell : Cell) :
    (put allocator handle cell).cells[handle]? = some cell := by
  exact Array.getElem?_setIfInBounds_self_of_lt (present_bound present)

private theorem put_other (allocator : Allocator) (handle other : Nat)
    (distinct : handle ≠ other) (cell : Cell) :
    (put allocator handle cell).cells[other]? = allocator.cells[other]? := by
  exact Array.getElem?_setIfInBounds_ne distinct

/-- Allocation cannot replace a live incarnation or wrap its generation. -/
def allocate? (allocator : Allocator) (handle : Nat) : Option (Allocator × Token) := do
  let cell ← allocator.cells[handle]?
  if cell.owners = 0 ∧ cell.generation < allocator.generationBound then
    some (put allocator handle { cell with owners := 1 }, ⟨handle, cell.generation⟩)
  else none

private def changeOwners? (allocator : Allocator) (token : Token)
    (change : Cell → Cell) : Option Allocator := do
  let cell ← allocator.cells[token.handle]?
  if cell.generation = token.generation ∧ 0 < cell.owners then
    some (put allocator token.handle (change cell))
  else none

/-- A retained branch or escaped owner shares the existing token. -/
def retain? (allocator : Allocator) (token : Token) : Option Allocator :=
  changeOwners? allocator token (fun cell => { cell with owners := cell.owners + 1 })

private def releasedCell (cell : Cell) : Cell :=
  if cell.owners = 1 then ⟨cell.generation + 1, 0⟩
  else { cell with owners := cell.owners - 1 }

def release? (allocator : Allocator) (token : Token) : Option Allocator :=
  changeOwners? allocator token releasedCell

private theorem live_witness {allocator : Allocator} {token : Token}
    (live : Live allocator token) :
    ∃ cell, allocator.cells[token.handle]? = some cell ∧
      cell.generation = token.generation ∧ 0 < cell.owners := by
  cases present : allocator.cells[token.handle]? with
  | none => simp [Live, present] at live
  | some cell => exact ⟨cell, rfl, by simpa [Live, present] using live⟩

private theorem allocate_success {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    ∃ cell, allocator.cells[handle]? = some cell ∧ cell.owners = 0 ∧
      cell.generation < allocator.generationBound ∧
      next = put allocator handle { cell with owners := 1 } ∧
      token = ⟨handle, cell.generation⟩ := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, present] at allocated
  | some cell =>
    simp only [allocate?, present] at allocated
    change (if cell.owners = 0 ∧ cell.generation < allocator.generationBound then
      some (put allocator handle { cell with owners := 1 }, ⟨handle, cell.generation⟩)
      else none) = some (next, token) at allocated
    split at allocated
    · next valid =>
      obtain ⟨stateEq, tokenEq⟩ := Prod.mk.inj (Option.some.inj allocated)
      exact ⟨cell, rfl, valid.1, valid.2, stateEq.symm, tokenEq.symm⟩
    · simp at allocated

private theorem changeOwners_success {allocator next : Allocator} {token : Token}
    {change : Cell → Cell} (changed : changeOwners? allocator token change = some next) :
    ∃ cell, allocator.cells[token.handle]? = some cell ∧
      cell.generation = token.generation ∧ 0 < cell.owners ∧
      next = put allocator token.handle (change cell) := by
  cases present : allocator.cells[token.handle]? with
  | none => simp [changeOwners?, present] at changed
  | some cell =>
    simp only [changeOwners?, present] at changed
    change (if cell.generation = token.generation ∧ 0 < cell.owners then
      some (put allocator token.handle (change cell)) else none) = some next at changed
    split at changed
    · next valid =>
      exact ⟨cell, rfl, valid.1, valid.2, (Option.some.inj changed).symm⟩
    · simp at changed

theorem allocated_live {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) : Live next token := by
  obtain ⟨cell, present, _, _, rfl, rfl⟩ := allocate_success allocated
  simp [Live, put_self present]

/-- Distinct live tokens must occupy distinct handles in the shared authority. -/
theorem live_handle_unique {allocator : Allocator} {left right : Token}
    (leftLive : Live allocator left) (rightLive : Live allocator right)
    (sameHandle : left.handle = right.handle) : left = right := by
  obtain ⟨leftCell, leftPresent, leftGeneration, _⟩ := live_witness leftLive
  obtain ⟨rightCell, rightPresent, rightGeneration, _⟩ := live_witness rightLive
  rw [← sameHandle, leftPresent] at rightPresent
  cases Option.some.inj rightPresent
  cases left
  cases right
  simp_all

theorem live_prevents_allocation {allocator : Allocator} {token : Token}
    (live : Live allocator token) : allocate? allocator token.handle = none := by
  obtain ⟨cell, present, _, owned⟩ := live_witness live
  simp [allocate?, present, Nat.ne_of_gt owned]

/-- A new allocation cannot use any handle that was live immediately beforehand. -/
theorem fresh_allocation_distinct_handle {allocator next : Allocator} {handle : Nat}
    {fresh old : Token} (allocated : allocate? allocator handle = some (next, fresh))
    (oldLive : Live allocator old) : fresh.handle ≠ old.handle := by
  obtain ⟨_, _, _, _, _, rfl⟩ := allocate_success allocated
  intro same
  change handle = old.handle at same
  rw [same, live_prevents_allocation oldLive] at allocated
  contradiction

/-- A successful new allocation and every previously live allocation remain
simultaneously live with distinct handles and distinct tokens. Multiple owners
of one allocation intentionally share its token instead. -/
theorem allocation_separates_live {allocator next : Allocator} {handle : Nat}
    {fresh old : Token} (allocated : allocate? allocator handle = some (next, fresh))
    (oldLive : Live allocator old) :
    Live next fresh ∧ Live next old ∧ fresh.handle ≠ old.handle ∧ fresh ≠ old := by
  have distinct := fresh_allocation_distinct_handle allocated oldLive
  have freshLive := allocated_live allocated
  have oldStays : Live next old := by
    obtain ⟨cell, _, _, _, rfl, rfl⟩ := allocate_success allocated
    simpa [Live, put_other allocator handle old.handle distinct] using oldLive
  exact ⟨freshLive, oldStays, distinct, fun same => distinct (congrArg Token.handle same)⟩

theorem retired_prevents_allocation {allocator : Allocator} {handle : Nat}
    (retired : Retired allocator handle) : allocate? allocator handle = none := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, present]
  | some cell =>
    have bounds : allocator.generationBound ≤ cell.generation :=
      (by simpa [Retired, present] using retired :
        cell.owners = 0 ∧ allocator.generationBound ≤ cell.generation).2
    simp [allocate?, present, Nat.not_lt.mpr bounds]

theorem retain_live {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) : Live next token := by
  obtain ⟨cell, present, generation, _, rfl⟩ := changeOwners_success retained
  simp [Live, put_self present, generation]

theorem retain_increments_owners {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) :
    ∃ before after, allocator.cells[token.handle]? = some before ∧
      next.cells[token.handle]? = some after ∧
      after.generation = before.generation ∧ after.owners = before.owners + 1 := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success retained
  exact ⟨cell, _, present, put_self present _, rfl, rfl⟩

/-- Strictly older incarnations are invalid even if their handle is currently owned. -/
theorem older_generation_not_live {allocator : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell)
    (older : token.generation < cell.generation) : ¬ Live allocator token := by
  simp [Live, present, Nat.ne_of_gt older]

/-- Generation progress is defined independently of token validity. -/
def GenerationsLE (before after : Allocator) : Prop :=
  ∀ (handle : Nat) (cell : Cell), before.cells[handle]? = some cell →
    ∃ next : Cell, after.cells[handle]? = some next ∧ cell.generation ≤ next.generation

private theorem put_generationsLE {allocator : Allocator} {handle : Nat} {old : Cell}
    (present : allocator.cells[handle]? = some old) (cell : Cell)
    (monotone : old.generation ≤ cell.generation) :
    GenerationsLE allocator (put allocator handle cell) := by
  intro other before beforePresent
  by_cases same : handle = other
  · subst other
    rw [present] at beforePresent
    cases Option.some.inj beforePresent
    exact ⟨cell, put_self present cell, monotone⟩
  · exact ⟨before, by rw [put_other allocator handle other same]; exact beforePresent,
      Nat.le_refl _⟩

theorem allocate_generationsLE {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl, _⟩ := allocate_success allocated
  exact put_generationsLE present _ (Nat.le_refl _)

theorem retain_generationsLE {allocator next : Allocator} {token : Token}
    (retained : retain? allocator token = some next) : GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success retained
  exact put_generationsLE present _ (Nat.le_refl _)

theorem release_generationsLE {allocator next : Allocator} {token : Token}
    (released : release? allocator token = some next) : GenerationsLE allocator next := by
  obtain ⟨cell, present, _, _, rfl⟩ := changeOwners_success released
  apply put_generationsLE present
  simp only [releasedCell]
  split <;> simp

/-- Only successful operations advance a shared allocator trace. -/
inductive Step : Allocator → Allocator → Prop where
  | allocate {before after : Allocator} {handle : Nat} {token : Token}
      (success : allocate? before handle = some (after, token)) : Step before after
  | retain {before after : Allocator} {token : Token}
      (success : retain? before token = some after) : Step before after
  | release {before after : Allocator} {token : Token}
      (success : release? before token = some after) : Step before after

inductive Trace : Allocator → Allocator → Prop where
  | refl (allocator : Allocator) : Trace allocator allocator
  | next {before middle after : Allocator} (history : Trace before middle)
      (step : Step middle after) : Trace before after

theorem Step.generationsLE {before after : Allocator} (step : Step before after) :
    GenerationsLE before after := by
  cases step with
  | allocate success => exact allocate_generationsLE success
  | retain success => exact retain_generationsLE success
  | release success => exact release_generationsLE success

theorem Trace.generationsLE {before after : Allocator} (trace : Trace before after) :
    GenerationsLE before after := by
  induction trace with
  | refl => exact fun _ cell present => ⟨cell, present, Nat.le_refl _⟩
  | next history step ih =>
    intro handle cell present
    obtain ⟨middle, middlePresent, first⟩ := ih handle cell present
    obtain ⟨last, lastPresent, second⟩ := step.generationsLE handle middle middlePresent
    exact ⟨last, lastPresent, Nat.le_trans first second⟩

/-- No sequence of allocation, retention, and release revives an old incarnation. -/
theorem stale_forever {before after : Allocator} {token : Token} {cell : Cell}
    (present : before.cells[token.handle]? = some cell)
    (older : token.generation < cell.generation) (trace : Trace before after) :
    ¬ Live after token := by
  obtain ⟨last, lastPresent, monotone⟩ := trace.generationsLE token.handle cell present
  exact older_generation_not_live lastPresent (Nat.lt_of_lt_of_le older monotone)

theorem final_release_advances {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (lastOwner : cell.owners = 1)
    (released : release? allocator token = some next) :
    next.cells[token.handle]? = some ⟨cell.generation + 1, 0⟩ := by
  obtain ⟨found, foundPresent, _, _, rfl⟩ := changeOwners_success released
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  simpa [releasedCell, lastOwner] using put_self present (releasedCell cell)

theorem final_release_never_revives {allocator released final : Allocator} {token : Token}
    {cell : Cell} (present : allocator.cells[token.handle]? = some cell)
    (lastOwner : cell.owners = 1) (success : release? allocator token = some released)
    (trace : Trace released final) : ¬ Live final token := by
  obtain ⟨found, foundPresent, generation, _, _⟩ := changeOwners_success success
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  apply stale_forever (final_release_advances present lastOwner success) _ trace
  simp [generation]

theorem release_shared_stays_live {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (shared : 1 < cell.owners)
    (released : release? allocator token = some next) : Live next token := by
  obtain ⟨found, foundPresent, generation, _, rfl⟩ := changeOwners_success released
  rw [present] at foundPresent
  cases Option.some.inj foundPresent
  have notLast : cell.owners ≠ 1 := Nat.ne_of_gt shared
  have remaining : 0 < cell.owners - 1 := Nat.sub_pos_of_lt shared
  simp [Live, put_self present, releasedCell, notLast, generation, remaining]

private theorem put_wellFormed {allocator : Allocator} (valid : allocator.WellFormed)
    (handle : Nat) (cell : Cell) (bounded : cell.generation ≤ allocator.generationBound)
    (liveBound : 0 < cell.owners → cell.generation < allocator.generationBound) :
    (put allocator handle cell).WellFormed := by
  intro other found present
  by_cases same : handle = other
  · subst other
    by_cases inBounds : handle < allocator.cells.size
    · change (allocator.cells.setIfInBounds handle cell)[handle]? = some found at present
      rw [Array.getElem?_setIfInBounds_self_of_lt inBounds] at present
      cases Option.some.inj present
      exact ⟨bounded, liveBound⟩
    · have missing : (put allocator handle cell).cells[handle]? = none := by
        apply Array.getElem?_eq_none
        simpa [put] using Nat.not_lt.mp inBounds
      rw [missing] at present
      contradiction
  · rw [put_other allocator handle other same] at present
    exact valid other found present

theorem Allocator.empty_wellFormed (capacity generationBound : Nat) :
    (Allocator.empty capacity generationBound).WellFormed := by
  intro handle cell present
  obtain ⟨bound, cellEq⟩ := Array.getElem?_eq_some_iff.mp present
  have same : cell = ⟨0, 0⟩ := by simpa [Allocator.empty] using cellEq.symm
  subst cell
  simp [Allocator.empty]

theorem allocate_wellFormed {allocator next : Allocator} {handle : Nat} {token : Token}
    (valid : allocator.WellFormed)
    (allocated : allocate? allocator handle = some (next, token)) : next.WellFormed := by
  obtain ⟨cell, _, _, bound, rfl, _⟩ := allocate_success allocated
  exact put_wellFormed valid _ _ (Nat.le_of_lt bound) (fun _ => bound)

theorem retain_wellFormed {allocator next : Allocator} {token : Token}
    (valid : allocator.WellFormed) (retained : retain? allocator token = some next) :
    next.WellFormed := by
  obtain ⟨cell, present, _, owned, rfl⟩ := changeOwners_success retained
  have bounds := valid token.handle cell present
  exact put_wellFormed valid _ _ bounds.1 (fun _ => bounds.2 owned)

theorem release_wellFormed {allocator next : Allocator} {token : Token}
    (valid : allocator.WellFormed) (released : release? allocator token = some next) :
    next.WellFormed := by
  obtain ⟨cell, present, _, owned, rfl⟩ := changeOwners_success released
  have bounds := valid token.handle cell present
  by_cases lastOwner : cell.owners = 1
  · simp only [releasedCell, if_pos lastOwner]
    exact put_wellFormed valid _ _ (Nat.succ_le_of_lt (bounds.2 owned)) (by simp)
  · simp only [releasedCell, if_neg lastOwner]
    exact put_wellFormed valid _ _ bounds.1 (fun _ => bounds.2 owned)

theorem Step.wellFormed {before after : Allocator} (step : Step before after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases step with
  | allocate success => exact allocate_wellFormed valid success
  | retain success => exact retain_wellFormed valid success
  | release success => exact release_wellFormed valid success

theorem Trace.wellFormed {before after : Allocator} (trace : Trace before after)
    (valid : before.WellFormed) : after.WellFormed := by
  induction trace with
  | refl => exact valid
  | next history step ih => exact step.wellFormed ih

theorem Step.bound_eq {before after : Allocator} (step : Step before after) :
    after.generationBound = before.generationBound := by
  cases step with
  | allocate success =>
    obtain ⟨_, _, _, _, rfl, _⟩ := allocate_success success
    rfl
  | retain success =>
    obtain ⟨_, _, _, _, rfl⟩ := changeOwners_success success
    rfl
  | release success =>
    obtain ⟨_, _, _, _, rfl⟩ := changeOwners_success success
    rfl

theorem Trace.bound_eq {before after : Allocator} (trace : Trace before after) :
    after.generationBound = before.generationBound := by
  induction trace with
  | refl => rfl
  | next history step ih => exact step.bound_eq.trans ih

theorem retirement_permanent {before after : Allocator} {handle : Nat}
    (retired : Retired before handle) (trace : Trace before after) :
    allocate? after handle = none := by
  cases present : before.cells[handle]? with
  | none => simp [Retired, present] at retired
  | some cell =>
    have exhausted : before.generationBound ≤ cell.generation :=
      (by simpa [Retired, present] using retired :
        cell.owners = 0 ∧ before.generationBound ≤ cell.generation).2
    obtain ⟨last, lastPresent, monotone⟩ := trace.generationsLE handle cell present
    have exhaustedAfter : ¬ last.generation < after.generationBound := by
      rw [trace.bound_eq]
      exact Nat.not_lt.mpr (Nat.le_trans exhausted monotone)
    simp [allocate?, lastPresent, exhaustedAfter]

theorem allocated_generation_bounded {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    token.generation < allocator.generationBound := by
  obtain ⟨_, _, _, bound, _, rfl⟩ := allocate_success allocated
  exact bound

theorem final_generation_retires {allocator next : Allocator} {token : Token} {cell : Cell}
    (present : allocator.cells[token.handle]? = some cell) (lastOwner : cell.owners = 1)
    (lastGeneration : cell.generation + 1 = allocator.generationBound)
    (released : release? allocator token = some next) : Retired next token.handle := by
  have advanced := final_release_advances present lastOwner released
  have boundEq := (Step.release released).bound_eq
  simp [Retired, advanced, boundEq, lastGeneration]

/-! ## Branch values under a shared identity authority

An image has no allocation counter. Publishing uses a token from the shared
allocator; capturing one frame performs a checked retain and preserves its
original handle. Publication transfers an already-held owner into an image;
it does not mint another owner. Whole-image ownership accounting, arbitrary
image destruction, and correspondence to actual runtime pointers are outside
this per-frame capture model.
-/

structure Image where
  entries : Array (Option Entry)

def Image.empty (capacity : Nat) : Image := ⟨Array.replicate capacity none⟩

private def Image.toStore (image : Image) : Store := ⟨image.entries, 0⟩

def Image.frameAt (image : Image) (handle : Nat) : Option Entry :=
  MetavariableFrameStore.frameAt image.toStore handle

def Image.lookup (image : Image) (ref : Ref) : Option (Option Atom) :=
  MetavariableFrameStore.lookup image.toStore ref

/-- Observation checked against the shared authority, even for an old value image. -/
def Image.lookupOwned (allocator : Allocator) (image : Image) (ref : Ref) : Option (Option Atom) :=
  if Live allocator ⟨ref.handle, ref.generation⟩ then image.lookup ref else none

def Image.write? (image : Image) (ref : Ref) (value : Option Atom) : Option Image :=
  (MetavariableFrameStore.write? image.toStore ref value).map (fun store => ⟨store.entries⟩)

/-- Publish a previously owned token without changing its handle or generation. -/
def Image.publish? (allocator : Allocator) (image : Image) (token : Token)
    (frame : Frame) (env : FrameEnv frame) : Option Image :=
  if Live allocator token ∧ token.handle < image.entries.size then
    some ⟨image.entries.setIfInBounds token.handle
      (some ⟨token.generation, frame, Array.ofFn env, by simp⟩)⟩
  else none

private def Image.projectFrame (image : Image) (handle : Nat) (entry : Entry) : Image :=
  ⟨(Array.replicate image.entries.size none).setIfInBounds handle (some entry)⟩

/-- Retain one selected frame and project it into a new branch at the same handle. -/
def Image.capture? (allocator : Allocator) (image : Image) (token : Token) :
    Option (Allocator × Image) := do
  let entry ← image.frameAt token.handle
  if entry.generation = token.generation then
    let next ← retain? allocator token
    some (next, image.projectFrame token.handle entry)
  else none

theorem Image.lookup_publish {allocator : Allocator} {image result : Image}
    {token : Token} {frame : Frame} {env : FrameEnv frame}
    (published : image.publish? allocator token frame env = some result) (slot : Slot frame) :
    result.lookup (token.ref slot.val) = some (env slot) := by
  unfold Image.publish? at published
  split at published
  · next valid =>
    cases Option.some.inj published
    simp [Image.lookup, Image.toStore, Token.ref, MetavariableFrameStore.lookup, MetavariableFrameStore.frameAt,
      Array.getElem?_setIfInBounds_self_of_lt valid.2, slot.isLt]
  · simp at published

theorem Image.lookup_write {image next : Image} {ref : Ref} {value : Option Atom}
    (written : image.write? ref value = some next) : next.lookup ref = some value := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [Image.write?, result] at written
  | some store =>
    simp only [Image.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    simpa [Image.lookup, Image.toStore, MetavariableFrameStore.lookup, MetavariableFrameStore.frameAt] using
      MetavariableFrameStore.lookup_write result

theorem Image.write_preserves_identity {image next : Image} {ref : Ref} {value : Option Atom}
    (written : image.write? ref value = some next) :
    ∃ before after, image.frameAt ref.handle = some before ∧
      next.frameAt ref.handle = some after ∧
      before.generation = ref.generation ∧ after.generation = ref.generation := by
  cases result : MetavariableFrameStore.write? image.toStore ref value with
  | none => simp [Image.write?, result] at written
  | some store =>
    simp only [Image.write?, result, Option.map_some, Option.some.injEq] at written
    cases written
    obtain ⟨entry, present, generation, _, rfl⟩ := write?_success result
    refine ⟨entry, updateEntry entry ref.slot value, present, ?_, generation, generation⟩
    simpa [Image.frameAt, Image.toStore, MetavariableFrameStore.frameAt, replace] using
      frameAt_replace_self image.toStore ref.handle (frameAt_bound present)
        (updateEntry entry ref.slot value)

private theorem Image.capture_success {allocator next : Allocator} {image captured : Image}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ entry, image.frameAt token.handle = some entry ∧
      entry.generation = token.generation ∧ retain? allocator token = some next ∧
      captured = image.projectFrame token.handle entry := by
  cases present : image.frameAt token.handle with
  | none => simp [Image.capture?, present] at success
  | some entry =>
    by_cases generation : entry.generation = token.generation
    · cases retained : retain? allocator token with
      | none => simp [Image.capture?, present, retained] at success
      | some after =>
        have equal : after = next ∧ image.projectFrame token.handle entry = captured := by
          simpa [Image.capture?, present, generation, retained] using success
        exact ⟨entry, rfl, generation, congrArg some equal.1, equal.2.symm⟩
    · simp [Image.capture?, present, generation] at success

theorem Image.capture_retains_owner {allocator next : Allocator} {image captured : Image}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ before after, allocator.cells[token.handle]? = some before ∧
      next.cells[token.handle]? = some after ∧
      after.generation = before.generation ∧ after.owners = before.owners + 1 := by
  obtain ⟨_, _, _, retained, _⟩ := Image.capture_success success
  exact retain_increments_owners retained

theorem Image.capture_live {allocator next : Allocator} {image captured : Image}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    Live next token := by
  obtain ⟨_, _, _, retained, _⟩ := Image.capture_success success
  exact retain_live retained

theorem Image.capture_preserves_identity {allocator next : Allocator} {image captured : Image}
    {token : Token} (success : image.capture? allocator token = some (next, captured)) :
    ∃ entry, image.frameAt token.handle = some entry ∧
      captured.frameAt token.handle = some entry ∧ entry.generation = token.generation := by
  obtain ⟨entry, present, generation, _, rfl⟩ := Image.capture_success success
  refine ⟨entry, present, ?_, generation⟩
  have bound : token.handle < image.entries.size := frameAt_bound present
  simp [Image.frameAt, Image.projectFrame, Image.toStore, MetavariableFrameStore.frameAt, bound]

theorem Image.capture_preserves_lookup {allocator next : Allocator} {image captured : Image}
    {token : Token} (success : image.capture? allocator token = some (next, captured))
    (slot : Nat) : captured.lookup (token.ref slot) = image.lookup (token.ref slot) := by
  obtain ⟨entry, before, after, generation⟩ := Image.capture_preserves_identity success
  have first := lookup_of_frameAt (ref := token.ref slot) before generation
  have second := lookup_of_frameAt (ref := token.ref slot) after generation
  exact second.trans first.symm

theorem Image.stale_owned_lookup {before after : Allocator} {token : Token} {cell : Cell}
    (present : before.cells[token.handle]? = some cell) (older : token.generation < cell.generation)
    (trace : Trace before after) (image : Image) (slot : Nat) :
    image.lookupOwned after (token.ref slot) = none := by
  have stale := stale_forever present older trace
  change (if Live after token then image.lookup (token.ref slot) else none) = none
  exact if_neg stale

/-! ## Shared-allocation canaries

The allocator has two handles and only two permitted generations per handle.
The selected frame occupies handle one, making a rebase to zero observable.
-/

private def firstAllocation : Allocator × Token :=
  (allocate? (Allocator.empty 2 2) 1).get (by decide)

private def retainedAllocation : Allocator :=
  (retain? firstAllocation.1 firstAllocation.2).get (by decide)

private def oneReleased : Allocator :=
  (release? retainedAllocation firstAllocation.2).get (by decide)

private def allReleased : Allocator :=
  (release? oneReleased firstAllocation.2).get (by decide)

private def secondAllocation : Allocator × Token :=
  (allocate? allReleased 1).get (by decide)

private def exhaustedAllocator : Allocator :=
  (release? secondAllocation.1 secondAllocation.2).get (by decide)

private def originalImage : Image :=
  (Image.publish? firstAllocation.1 (Image.empty 2) firstAllocation.2 sampleFrame sampleEnv).get
    (by decide)

private def capturedImage : Allocator × Image :=
  (originalImage.capture? firstAllocation.1 firstAllocation.2).get (by decide)

private def writtenImage : Image :=
  (capturedImage.2.write? (firstAllocation.2.ref 0) (some (.symbol "branch"))).get (by decide)

theorem canary_first_allocation_live : Live firstAllocation.1 firstAllocation.2 := by decide

theorem canary_live_handle_cannot_be_allocated :
    allocate? firstAllocation.1 1 = none := by decide

theorem canary_another_live_allocation_uses_other_handle :
    (allocate? firstAllocation.1 0).map (fun result => result.2) = some ⟨0, 0⟩ ∧
      firstAllocation.2 = ⟨1, 0⟩ := by decide

theorem canary_retain_counts_both_owners :
    retainedAllocation.cells[1]? = some ⟨0, 2⟩ := by decide

theorem canary_one_release_keeps_identity_live :
    Live oneReleased firstAllocation.2 ∧ allocate? oneReleased 1 = none := by decide

theorem canary_final_release_invalidates_identity :
    ¬ Live allReleased firstAllocation.2 ∧ allReleased.cells[1]? = some ⟨1, 0⟩ := by decide

theorem canary_handle_reuse_changes_incarnation :
    secondAllocation.2 = ⟨1, 1⟩ ∧ Live secondAllocation.1 secondAllocation.2 ∧
      ¬ Live secondAllocation.1 firstAllocation.2 := by decide

theorem canary_stale_retain_rejected :
    retain? secondAllocation.1 firstAllocation.2 = none := by decide

theorem canary_stale_release_rejected :
    release? secondAllocation.1 firstAllocation.2 = none := by decide

theorem canary_exhaustion_retires_handle :
    Retired exhaustedAllocator 1 ∧ allocate? exhaustedAllocator 1 = none := by decide

theorem canary_retired_generation_does_not_wrap :
    exhaustedAllocator.cells[1]? = some ⟨2, 0⟩ ∧
      ¬ Live exhaustedAllocator ⟨1, 0⟩ ∧ ¬ Live exhaustedAllocator ⟨1, 1⟩ := by decide

theorem canary_zero_generation_bound_rejects_allocation :
    allocate? (Allocator.empty 2 0) 1 = none := by decide

theorem canary_capture_retains_shared_token :
    capturedImage.1.cells[1]? = some ⟨0, 2⟩ ∧
      capturedImage.2.lookup (firstAllocation.2.ref 0) = some (some (.symbol "before")) ∧
      capturedImage.2.lookup ⟨0, 0, 0⟩ = none := by decide

/-- Equal identity does not imply equal values in different branch images. -/
theorem canary_same_live_variable_different_branch_values :
    Live capturedImage.1 firstAllocation.2 ∧
      originalImage.lookupOwned capturedImage.1 (firstAllocation.2.ref 0) =
        some (some (.symbol "before")) ∧
      writtenImage.lookupOwned capturedImage.1 (firstAllocation.2.ref 0) =
        some (some (.symbol "branch")) := by decide

/-- Old image contents alone are not an ownership certificate. -/
theorem canary_released_image_requires_authority :
    writtenImage.lookup (firstAllocation.2.ref 0) = some (some (.symbol "branch")) ∧
      writtenImage.lookupOwned allReleased (firstAllocation.2.ref 0) = none := by decide

theorem canary_reused_handle_cannot_validate_old_image :
    writtenImage.lookupOwned secondAllocation.1 (firstAllocation.2.ref 0) = none := by decide

theorem canary_exhaustion_follows_protocol : Trace (Allocator.empty 2 2) exhaustedAllocator := by
  have first : Step (Allocator.empty 2 2) firstAllocation.1 :=
    .allocate (handle := 1) (token := firstAllocation.2) (by decide)
  have retained : Step firstAllocation.1 retainedAllocation :=
    .retain (token := firstAllocation.2) (by decide)
  have releasedOne : Step retainedAllocation oneReleased :=
    .release (token := firstAllocation.2) (by decide)
  have releasedAll : Step oneReleased allReleased :=
    .release (token := firstAllocation.2) (by decide)
  have reused : Step allReleased secondAllocation.1 :=
    .allocate (handle := 1) (token := secondAllocation.2) (by decide)
  have exhausted : Step secondAllocation.1 exhaustedAllocator :=
    .release (token := secondAllocation.2) (by decide)
  exact (((((Trace.refl _).next first).next retained).next releasedOne).next releasedAll).next reused
    |>.next exhausted

theorem canary_exhausted_allocator_wellFormed : exhaustedAllocator.WellFormed :=
  canary_exhaustion_follows_protocol.wellFormed (Allocator.empty_wellFormed 2 2)

end Shared

end Mettapedia.Languages.MeTTa.MetavariableFrameStore
