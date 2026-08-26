import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

/-!
# Authoritative dense slots with value-restoring undo trails

`FiniteEnvironmentCompilation` proves that a duplicate-free finite key
inventory may be represented by dense slots without changing the decoded
source environment.  This module adds the destructive update discipline needed
when those slots are the authoritative runtime binding state rather than a
derived cache.

Every write records the slot's complete previous value before overwriting it.
Rolling back to a saved trail length therefore restores the exact pre-mark
slot state, including nested transactions and repeated writes to one slot.
The proofs are independent of the key and value languages.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation

open FiniteEnvironmentCompilation

universe uKey uValue

/-- One destructive slot write can be undone only when its previous value is
retained.  Entries are stored newest first. -/
structure UndoEntry {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) where
  slot : inventory.Slot
  previous : Option Value

/-- The dense slots are authoritative; the trail contains only information
needed to restore earlier authoritative states. -/
structure State {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) where
  slots : DenseEnvironment inventory Value
  trail : List (UndoEntry inventory Value)

/-- A choice point is the current number of retained undo entries. -/
def mark (state : State inventory Value) : Nat := state.trail.length

/-- Restore one slot from a retained previous value. -/
def restoreEntry [DecidableEq Key] (inventory : Inventory Key)
    (environment : DenseEnvironment inventory Value)
    (entry : UndoEntry inventory Value) : DenseEnvironment inventory Value :=
  fun candidate =>
    if candidate = entry.slot then entry.previous else environment candidate

/-- Perform one authoritative write and retain exactly the overwritten value. -/
def write [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (update : DenseWrite inventory Value) :
    State inventory Value :=
  { slots := writeDense inventory state.slots update
    trail := ⟨update.1, state.slots update.1⟩ :: state.trail }

/-- Undo the newest authoritative write.  An empty trail fails closed. -/
def undoOne? [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) : Option (State inventory Value) :=
  match state.trail with
  | [] => none
  | entry :: rest =>
      some { slots := restoreEntry inventory state.slots entry, trail := rest }

/-- A freshly written slot is restored exactly, not merely cleared. -/
theorem undoOne?_write [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (update : DenseWrite inventory Value) :
    undoOne? inventory (write inventory state update) = some state := by
  apply congrArg some
  cases state with
  | mk environment trail =>
      simp only [write]
      congr 1
      funext candidate
      by_cases same : candidate = update.1
      · subst candidate
        simp [restoreEntry]
      · simp [restoreEntry, writeDense, same]

/-- Undo a fixed number of writes. -/
def rollbackN [DecidableEq Key] (inventory : Inventory Key) :
    Nat -> State inventory Value -> Option (State inventory Value)
  | 0, state => some state
  | steps + 1, state => do
      let previous <- undoOne? inventory state
      rollbackN inventory steps previous

/-- Consecutive rollback counts compose in execution order. -/
theorem rollbackN_add [DecidableEq Key] (inventory : Inventory Key)
    (first second : Nat) (state : State inventory Value) :
    rollbackN inventory (first + second) state =
      (rollbackN inventory first state).bind
        (rollbackN inventory second) := by
  induction first generalizing state with
  | zero => simp [rollbackN]
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, rollbackN]
      cases undone : undoOne? inventory state with
      | none => simp
      | some previous =>
          exact inductionHypothesis previous

/-- Execute dense writes in source order using authoritative slots. -/
def run [DecidableEq Key] (inventory : Inventory Key) :
    State inventory Value -> List (DenseWrite inventory Value) ->
      State inventory Value
  | state, [] => state
  | state, update :: updates => run inventory (write inventory state update) updates

/-- The authoritative slot contents are exactly the existing dense execution;
the undo trail is semantically invisible until rollback. -/
theorem run_slots [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (updates : List (DenseWrite inventory Value)) :
    (run inventory state updates).slots =
      runDenseFrom inventory state.slots updates := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      simpa [run, write, runDenseFrom] using
        inductionHypothesis (write inventory state update)

/-- Execution adds exactly one undo entry per authoritative write. -/
theorem run_trail_length [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (updates : List (DenseWrite inventory Value)) :
    (run inventory state updates).trail.length =
      state.trail.length + updates.length := by
  induction updates generalizing state with
  | nil => simp [run]
  | cons update updates inductionHypothesis =>
      rw [run]
      rw [inductionHypothesis]
      simp only [write, List.length_cons]
      omega

/-- Undoing exactly the writes performed by one transaction restores the
complete starting state, including any older trail prefix. -/
theorem rollbackN_run [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (updates : List (DenseWrite inventory Value)) :
    rollbackN inventory updates.length (run inventory state updates) =
      some state := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      rw [run]
      rw [show (update :: updates).length = updates.length + 1 by simp]
      rw [rollbackN_add]
      rw [inductionHypothesis]
      simp [rollbackN, undoOne?_write]

/-- Roll back to a choice-point mark.  A mark beyond the current trail fails
closed instead of fabricating a state. -/
def rollbackTo? [DecidableEq Key] (inventory : Inventory Key)
    (savedMark : Nat) (state : State inventory Value) :
    Option (State inventory Value) :=
  if savedMark <= state.trail.length then
    rollbackN inventory (state.trail.length - savedMark) state
  else
    none

/-- Every rollback count bounded by the retained trail is executable. -/
theorem rollbackN_available [DecidableEq Key] (inventory : Inventory Key)
    (steps : Nat) (state : State inventory Value)
    (bounded : steps ≤ state.trail.length) :
    exists restored, rollbackN inventory steps state = some restored := by
  induction steps generalizing state with
  | zero => exact ⟨state, rfl⟩
  | succ steps inductionHypothesis =>
      cases state with
      | mk slots trail =>
          cases trail with
          | nil => simp at bounded
          | cons entry rest =>
              have restBounded : steps ≤ rest.length := by
                simpa using bounded
              let previous : State inventory Value :=
                { slots := restoreEntry inventory slots entry
                  trail := rest }
              obtain ⟨restored, restoredEq⟩ :=
                inductionHypothesis previous restBounded
              refine ⟨restored, ?_⟩
              simpa [rollbackN, undoOne?, previous] using restoredEq

/-- A valid activation checkpoint therefore always has a concrete rollback
state; invalid future checkpoints remain rejected by `rollbackTo?`. -/
theorem rollbackTo?_available [DecidableEq Key] (inventory : Inventory Key)
    (savedMark : Nat) (state : State inventory Value)
    (bounded : savedMark ≤ state.trail.length) :
    exists restored, rollbackTo? inventory savedMark state = some restored := by
  unfold rollbackTo?
  simp only [bounded, ↓reduceIte]
  exact rollbackN_available inventory (state.trail.length - savedMark) state
    (Nat.sub_le state.trail.length savedMark)

/-- A transaction followed by rollback to its entry mark is observationally
and physically the identity. -/
theorem rollbackTo?_run [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value) (updates : List (DenseWrite inventory Value)) :
    rollbackTo? inventory (mark state) (run inventory state updates) =
      some state := by
  unfold rollbackTo? mark
  rw [run_trail_length]
  have bounded : state.trail.length <= state.trail.length + updates.length :=
    Nat.le_add_right state.trail.length updates.length
  simp only [bounded, ↓reduceIte]
  rw [Nat.add_sub_cancel_left]
  exact rollbackN_run inventory state updates

/-- Nested transactions restore the inner mark without disturbing the outer
transaction's authoritative bindings or trail. -/
theorem rollbackTo?_nested [DecidableEq Key] (inventory : Inventory Key)
    (state : State inventory Value)
    (outer inner : List (DenseWrite inventory Value)) :
    rollbackTo? inventory (mark (run inventory state outer))
        (run inventory (run inventory state outer) inner) =
      some (run inventory state outer) :=
  rollbackTo?_run inventory (run inventory state outer) inner

/-- Authoritative execution inherits the existing key-to-slot semantics
theorem: decoding its hot slots gives exactly the authored source execution. -/
theorem run_refines_source [DecidableEq Key] (inventory : Inventory Key)
    (source : List (SourceWrite Key Value))
    (compiled : List (DenseWrite inventory Value))
    (accepted : compileWrites? inventory source = some compiled)
    (sourceEnvironment : SourceEnvironment Key Value)
    (state : State inventory Value)
    (related : decodeDense inventory state.slots = sourceEnvironment) :
    decodeDense inventory (run inventory state compiled).slots =
      runSourceFrom sourceEnvironment source := by
  rw [run_slots]
  exact runDenseFrom_refines_runSourceFrom inventory source compiled accepted
    sourceEnvironment state.slots related

/-! ## Positive and negative witnesses -/

private inductive Register where
  | left
  | right
deriving DecidableEq

private def registers : Inventory Register where
  keys := [.left, .right]
  nodup := by decide

private def emptyState : State registers Nat :=
  { slots := emptyDenseEnvironment registers, trail := [] }

/-- Repeated writes to one slot restore the intermediate value at the inner
mark and the empty state at the outer mark. -/
example :
    let left : registers.Slot := ⟨0, by decide⟩
    let outer := run registers emptyState [(left, 3)]
    let inner := run registers outer [(left, 5), (left, 8)]
    rollbackTo? registers (mark outer) inner = some outer ∧
      rollbackTo? registers (mark emptyState) outer = some emptyState := by
  simp only
  constructor
  · exact rollbackTo?_run registers
      (run registers emptyState [(⟨0, by decide⟩, 3)])
      [(⟨0, by decide⟩, 5), (⟨0, by decide⟩, 8)]
  · exact rollbackTo?_run registers emptyState [(⟨0, by decide⟩, 3)]

/-- A future trail mark is invalid and fails closed. -/
example : rollbackTo? registers 1 emptyState = none := by
  decide

private def oneRegister : Inventory Unit where
  keys := [()]
  nodup := by decide

private def uniformOneSlot (value : Option Nat) :
    DenseEnvironment oneRegister Nat := fun _ => value

/-- If an undo operation receives only the overwritten slot and current dense
state, it cannot restore two different previous values that produce the same
post-write state.  The previous value is therefore essential trail data. -/
theorem previous_value_is_necessary
    (undo : DenseEnvironment oneRegister Nat -> oneRegister.Slot ->
      DenseEnvironment oneRegister Nat)
    (slot : oneRegister.Slot)
    (restoresThree :
      undo (writeDense oneRegister (uniformOneSlot (some 3)) (slot, 7)) slot =
        uniformOneSlot (some 3))
    (restoresFive :
      undo (writeDense oneRegister (uniformOneSlot (some 5)) (slot, 7)) slot =
        uniformOneSlot (some 5)) : False := by
  have sameAfter :
      writeDense oneRegister (uniformOneSlot (some 3)) (slot, 7) =
        writeDense oneRegister (uniformOneSlot (some 5)) (slot, 7) := by
    funext candidate
    have sameSlot : candidate = slot := by
      apply Fin.ext
      have candidateBound := candidate.isLt
      change candidate.val < 1 at candidateBound
      have slotBound := slot.isLt
      change slot.val < 1 at slotBound
      omega
    simp [writeDense, sameSlot]
  have sameBefore : uniformOneSlot (some 3) = uniformOneSlot (some 5) := by
    calc
      uniformOneSlot (some 3) =
          undo (writeDense oneRegister (uniformOneSlot (some 3)) (slot, 7)) slot :=
        restoresThree.symm
      _ = undo (writeDense oneRegister (uniformOneSlot (some 5)) (slot, 7)) slot :=
        congrArg (fun environment => undo environment slot) sameAfter
      _ = uniformOneSlot (some 5) := restoresFive
  have impossible := congrFun sameBefore slot
  simp [uniformOneSlot] at impossible

end Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation
