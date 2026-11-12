import Mettapedia.Machines.Cursor.StampedSnapshots
import Mettapedia.Machines.Step.ResidualReader

/-!
# The row-order store is an ordered index whose key is the slot

`Cursor.StampedSnapshots` keeps rows in stable slots with a birth stamp and a
write-once death stamp, and reads them in slot order.  Read as an ordered index
(`ofStore`: the occupied slots as keys, each with its row's stamps), it is
an instance of the index of `ResidualReader`.

* `visible_iff`: the two notions of visibility agree on every row.
* `mem_view_ofStore`: the view a residual reader of time `t` is owed is exactly
  the slots whose entry in the store's snapshot at `t` is occupied.
* `mem_drain_ofStore`: so the residual reader over the slots yields exactly the
  occupied slots of that snapshot, ascending, each once.

The laws proved of the residual reader over an abstract index therefore hold
of a reader in row order whose state is the slot reached and the entry time.

Positive example: `Controls.live_rows_are_viewed`.  Negative example:
`Controls.dead_row_leaves_later_views` (a row removed at tick `3` is in the
view of time `2` and not in the view of time `3`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.ReaderOverRows

open Mettapedia.Machines.Cursor.StampedSnapshots

variable {α : Type}

/-- The store as an ordered index of its occupied slots. -/
def ofStore (s : Store α) : Index Nat where
  clock := s.clock
  held := (Finset.range s.next).filter fun id => (s.row id).isSome
  born id := ((s.row id).map Row.born).getD 0
  died id := (s.row id).bind Row.death

/-- The two notions of visibility agree on a row. -/
theorem visible_iff (t : Nat) (r : Row α) :
    visible t r = true ↔ r.born ≤ t ∧ ∀ d ∈ r.death, t < d := by
  unfold visible
  cases h : r.death with
  | none => simp
  | some d => simp

/-- **The view of the index is the occupied part of the store's snapshot.** -/
theorem mem_view_ofStore (s : Store α) (t id : Nat) (issued : id < s.next) :
    id ∈ Index.view (ofStore s) t ↔ ∃ v, atTime s t id = some (id, v) := by
  rw [Index.view, Finset.mem_filter]
  change (id ∈ (Finset.range s.next).filter fun id => (s.row id).isSome) ∧
      (((s.row id).map Row.born).getD 0 ≤ t ∧ ∀ d ∈ (s.row id).bind Row.death, t < d) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  unfold atTime
  cases h : s.row id with
  | none => simp
  | some r =>
    have vis := visible_iff t r
    simp only [Option.map_some, Option.getD_some, Option.bind_some, Option.isSome_some, issued,
      true_and]
    constructor
    · intro hv
      exact ⟨r.value, by simp [vis.mpr hv]⟩
    · rintro ⟨v, hv⟩
      by_cases seen : visible t r = true
      · exact vis.mp seen
      · simp [seen] at hv

/-- **The residual reader over the slots yields the occupied slots of the
snapshot**, whatever index of the slots it searches. -/
theorem mem_drain_ofStore (s : Store α) (t id : Nat) (issued : id < s.next) :
    id ∈ (readerSeeker (ofStore s) t).drain .all ↔ ∃ v, atTime s t id = some (id, v) := by
  rw [Seeker.mem_drain, readerSeeker_keys, mem_view_ofStore s t id issued]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

namespace Controls

/-- Rows `7` and `8`, then the first removed at tick `3`. -/
def store : Store Nat := remove (add (add empty 7) 8) 0

/-- Positive: the reader of time `2` is owed both slots. -/
theorem live_rows_are_viewed : Index.view (ofStore store) 2 = {0, 1} := by
  decide

/-- Negative: the reader of time `3` is not owed the removed slot. -/
theorem dead_row_leaves_later_views : Index.view (ofStore store) 3 = {1} := by
  decide

end Controls

end Mettapedia.Machines.Step.ReaderOverRows
