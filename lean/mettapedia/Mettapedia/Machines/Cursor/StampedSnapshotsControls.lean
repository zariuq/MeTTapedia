import Mettapedia.Machines.Cursor.StampedSnapshots

/-!
# Schedules distinguishing stable-slot snapshots from live reads

The positive controls execute the store/reader machine. The negative controls
use independently implemented faulty mutations or candidate enumeration:
refreshing a death stamp, reusing an issued slot, physically deleting a row,
and clearing the only historical candidate from an index. All expectations
are kernel-checked, not obtained from native store output.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.StampedSnapshots.Controls

def emitted (replies : List (Reply Nat)) : List (Nat × Nat) :=
  replies.filterMap fun reply => match reply with
    | .value id value => some (id, value)
    | _ => none

def outputs (events : List (Event Nat)) : List (Nat × Nat) :=
  emitted (run (initial empty) events).2

def oldAndNewReaders : List (Event Nat) :=
  [.add 7, .add 7, .add 9, .openReader 0, .read 0,
    .remove 1, .add 99, .openReader 1,
    .read 0, .read 0, .read 0,
    .read 1, .read 1, .read 1, .read 1, .read 1]

/-- The old reader still sees both original copies of 7, then 9. The new
reader sees the removal and the appended 99. Equal payloads keep distinct IDs. -/
theorem old_and_new_readers : outputs oldAndNewReaders =
    [(0, 7), (1, 7), (2, 9), (0, 7), (2, 9), (3, 99)] := by decide

def copiedReaders : List (Event Nat) :=
  [.add 7, .add 8, .openReader 0, .read 0, .remove 0,
    .clone 0 1 false, .clone 0 2 true,
    .read 1, .read 2, .close 0, .read 0,
    .read 1, .read 2, .read 2]

/-- A copy may keep the position or rewind the same entry snapshot, even
after the store has removed a row that snapshot still contains. -/
theorem copies_keep_entry_view : outputs copiedReaders =
    [(0, 7), (1, 8), (0, 7), (1, 8)] := by decide

theorem closed_reader_is_missing :
    ((run (initial empty) copiedReaders).2)[10]? = some (.missing : Reply Nat) := by decide

def churn : List (Event Nat) :=
  [.add 1, .openReader 0, .remove 0, .add 2, .remove 1, .add 3,
    .openReader 1, .read 0, .read 0,
    .read 1, .read 1, .read 1, .read 1]

theorem long_reader_survives_churn : outputs churn = [(0, 1), (2, 3)] := by decide

theorem skipped_row_is_not_exhaustion :
    ((run (initial empty) churn).2)[9]? = some (.skip : Reply Nat) ∧
      ((run (initial empty) churn).2)[10]? = some (.skip : Reply Nat) ∧
      ((run (initial empty) churn).2)[12]? = some (.exhausted : Reply Nat) := by decide

def nestedReaders : List (Event Nat) :=
  [.add 10, .add 20, .openReader 0, .read 0,
    .remove 1, .add 30, .openReader 1,
    .read 1, .read 1, .read 1, .close 1,
    .read 0, .read 0]

theorem nesting_does_not_adopt_inner_view : outputs nestedReaders =
    [(0, 10), (0, 10), (2, 30), (1, 20)] := by decide

def singleton : Store Nat := add empty 7
def retired : Store Nat := remove singleton 0
def old : Reader := start singleton
def late : Reader := start retired

/-- This mutation is wrong: it changes a death which had already occurred
before a later reader opened. -/
def refreshDeath (store : Store Nat) (id : Nat) : Store Nat :=
  match store.row id with
  | none => store
  | some row =>
      ⟨store.clock + 1, store.next,
        Function.update store.row id (some { row with death := some (store.clock + 1) })⟩

theorem refreshing_death_resurrects :
    atTime retired late.time 0 = none ∧
      atTime (remove retired 0) late.time 0 = none ∧
      atTime (refreshDeath retired 0) late.time 0 = some (0, 7) := by decide

/-- Reusing the retired slot with a fresh birth stamp makes the old row
disappear from the reader which is still entitled to it. -/
def reuseSlot (store : Store Nat) (id : Nat) (value : Nat) : Store Nat :=
  ⟨store.clock + 1, store.next,
    Function.update store.row id (some ⟨value, store.clock + 1, none⟩)⟩

theorem reuse_breaks_old_reader :
    atTime retired old.time 0 = some (0, 7) ∧
      atTime (reuseSlot retired 0 99) old.time 0 = none := by decide

def eraseSlot (store : Store Nat) (id : Nat) : Store Nat :=
  { store with row := Function.update store.row id none }

theorem physical_deletion_breaks_old_reader :
    snapshot retired old = [some (0, 7)] ∧
      snapshot (eraseSlot retired 0) old = [none] := by decide

def advanced : Reader := (step singleton old).2

/-- Passing a row does not release the right to clone this still-open entry
view in rewound form. An optimization using only current residuals loses it. -/
theorem reclaiming_passed_row_breaks_rewind :
    advanced.position = 1 ∧
      atTime retired (rewind advanced true).time 0 = some (0, 7) ∧
      atTime (eraseSlot retired 0) (rewind advanced true).time 0 = none := by decide

def indexedRead (store : Store Nat) (reader : Reader) (candidates : List Nat) :
    List (Nat × Nat) := candidates.filterMap (atTime store reader.time)

/-- Keeping the payload and its correct stamps is insufficient if removal
also clears the sole chain node or bit which enumerated that occurrence. -/
theorem clearing_historical_candidate_breaks_reader :
    indexedRead retired old [0] = [(0, 7)] ∧
      indexedRead retired old [] = [] := by decide

theorem rereading_live_view_breaks_reader :
    atTime retired old.time 0 = some (0, 7) ∧
      atTime retired retired.clock 0 = none := by decide

theorem writes_leave_reader_coordinates :
    let before := (run (initial empty) [.add 7, .openReader 0]).1
    let after := (run before [.remove 0, .add 99]).1
    before.readers 0 = some ⟨1, 1, 0⟩ ∧ after.readers 0 = before.readers 0 := by decide

#print axioms remove_keeps_past
#print axioms snapshot_add
#print axioms snapshot_remove
#print axioms step_refines
#print axioms apply_refines
#print axioms every_schedule_keeps_entry_views

end Mettapedia.Machines.Cursor.StampedSnapshots.Controls
