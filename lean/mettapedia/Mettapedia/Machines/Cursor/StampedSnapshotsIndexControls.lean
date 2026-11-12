import Mettapedia.Machines.Cursor.StampedSnapshotsIndex

/-!
# Historical-chain, bit-vector and incremental-load controls

The good indexes are built by the incremental slot loader. Faulty indexes
independently unlink a row, clear its bit, or rebuild from current-live rows.
The expectations retain identified tuples, so duplicate payloads cannot hide
missing or repeated occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.StampedSnapshotsIndex.Controls

open StampedSnapshots

def original : Store (Tuple Nat) :=
  add (add (add StampedSnapshots.empty [1, 7]) [1, 8]) [2, 9]

def built : Index Nat := load original original.next empty
def entry : Reader := start original
def retired : Store (Tuple Nat) := remove original 1
def afterWrite : Store (Tuple Nat) := add retired [1, 10]

theorem old_chain_view : query false retired built entry 0 1 =
    .complete [(0, [1, 7]), (1, [1, 8])] := by decide

theorem old_bit_view : query true retired built entry 0 1 =
    .complete [(0, [1, 7]), (1, [1, 8])] := by decide

theorem new_chain_view : query false retired built (start retired) 0 1 =
    .complete [(0, [1, 7])] := by decide

theorem new_bit_view : query true retired built (start retired) 0 1 =
    .complete [(0, [1, 7])] := by decide

/-- Rebuilding from all issued records after removal remains sound for the
reader that opened before removal. -/
theorem rebuilt_after_removal :
    query false retired (load retired retired.next empty) entry 0 1 =
      .complete [(0, [1, 7]), (1, [1, 8])] ∧
    query true retired (load retired retired.next empty) entry 0 1 =
      .complete [(0, [1, 7]), (1, [1, 8])] := by decide

def unlink (index : Index Nat) (id : Nat) : Index Nat :=
  { index with chain := fun column key => (index.chain column key).filter (· != id) }

theorem live_chain_unlink_loses_old_row :
    query false retired (unlink built 1) entry 0 1 = .complete [(0, [1, 7])] ∧
      query false retired (unlink built 1) entry 0 1 ≠ query false retired built entry 0 1 := by decide

def clearBit (index : Index Nat) (id : Nat) : Index Nat :=
  { index with bits := fun column key => (index.bits column key).set id false }

theorem live_bit_clear_loses_old_row :
    query true retired (clearBit built 1) entry 0 1 = .complete [(0, [1, 7])] ∧
      query true retired (clearBit built 1) entry 0 1 ≠ query true retired built entry 0 1 := by decide

/-- A superficially complete loader which drops dead rows is wrong for
older readers, even when it preserves the slot count. -/
def liveOnlyLoad (store : Store (Tuple Nat)) : Nat → Index Nat → Index Nat
  | 0, index => index
  | count + 1, index =>
      let tuple := (atTime store store.clock index.coverage).map Prod.snd
      liveOnlyLoad store count (append index tuple)

theorem live_only_rebuild_loses_old_row :
    query true retired (liveOnlyLoad retired retired.next empty) entry 0 1 =
      .complete [(0, [1, 7])] ∧
    query false retired (liveOnlyLoad retired retired.next empty) entry 0 1 =
      .complete [(0, [1, 7])] := by decide

theorem prefix_can_serve_old_reader :
    query true afterWrite built entry 0 1 = .complete [(0, [1, 7]), (1, [1, 8])] := by decide

theorem incomplete_index_is_pending :
    query true afterWrite built (start afterWrite) 0 1 = .pending ∧
      query false afterWrite built (start afterWrite) 0 1 = .pending := by decide

theorem caught_up_reader :
    query true afterWrite (load afterWrite 1 built) (start afterWrite) 0 1 =
      .complete [(0, [1, 7]), (3, [1, 10])] := by decide

theorem unloaded_absence_is_not_an_answer :
    query true afterWrite built (start afterWrite) 0 99 = .pending ∧
    query true afterWrite (load afterWrite 1 built) (start afterWrite) 0 99 =
      .complete [] := by decide

theorem all_columns_are_indexed :
    query true retired built entry 1 8 = .complete [(1, [1, 8])] ∧
      query true retired built (start retired) 1 8 = .complete [] := by decide

theorem load_continues_across_writes :
    let loadingIndex := load original 1 empty
    let caughtUp := load afterWrite 8 loadingIndex
    query true afterWrite caughtUp entry 0 1 = .complete [(0, [1, 7]), (1, [1, 8])] ∧
      query true afterWrite caughtUp (start afterWrite) 0 1 =
        .complete [(0, [1, 7]), (3, [1, 10])] := by decide

#print axioms valid_extend
#print axioms valid_load
#print axioms valid_under_add
#print axioms valid_under_remove
#print axioms chain_query_exact
#print axioms bit_query_exact
#print axioms query_complete_correct
#print axioms source_query_under_write

end Mettapedia.Machines.Cursor.StampedSnapshotsIndex.Controls
