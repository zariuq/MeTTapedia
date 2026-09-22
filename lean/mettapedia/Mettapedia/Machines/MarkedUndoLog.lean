import Mathlib.Data.List.Basic

/-!
# Coalescing chronological undo logs at marked boundaries

An entry stores a slot and its complete old payload. The list is chronological;
rollback executes its entries in reverse. Within one interval, only the first
old payload for each slot affects rollback to the interval's beginning.

The executable transformation below retains those first entries. Applied
separately between marks, it preserves rollback to every marked boundary, with
new offsets computed from the retained prefix lengths. It is not safe to merge
across a mark, as the final counterexample shows.

The list-based seen-slot scan is a constructive reference transformation, not a
claim about optimal indexing or a proof of any C implementation. Slot identity
alone needs decidable equality; payloads are arbitrary and never compared.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MarkedUndoLog

universe u v

variable {Slot : Type u} {Payload : Type v} [DecidableEq Slot]

/-- Restore the complete saved payload at one slot. -/
def restore (entry : Slot × Payload) (store : Slot → Payload) : Slot → Payload :=
  fun slot => if slot = entry.1 then entry.2 else store slot

/-- The oldest entry is applied last: this is reverse execution of a
chronological log, not forward replay of updates. -/
def rollback (log : List (Slot × Payload)) (store : Slot → Payload) : Slot → Payload :=
  log.foldr restore store

theorem rollback_reverse_foldl (log : List (Slot × Payload))
    (store : Slot → Payload) :
    rollback log store = log.reverse.foldl (fun state entry => restore entry state) store := by
  simp [rollback]

theorem rollback_append (older newer : List (Slot × Payload))
    (store : Slot → Payload) :
    rollback (older ++ newer) store = rollback older (rollback newer store) := by
  simp [rollback, List.foldr_append]

/-- Scan from oldest to newest, retaining an entry only at the first occurrence
of its slot. `seen` contains slots already retained in the current interval. -/
def coalesceFrom (seen : List Slot) : List (Slot × Payload) → List (Slot × Payload)
  | [] => []
  | entry :: rest =>
      if entry.1 ∈ seen then coalesceFrom seen rest
      else entry :: coalesceFrom (entry.1 :: seen) rest

def coalesce (log : List (Slot × Payload)) : List (Slot × Payload) :=
  coalesceFrom [] log

/-- Dropping entries already represented by an earlier interval-local write
does not change any slot outside `seen`. This is the induction invariant; it
does not assume that the desired complete rollback equation already holds. -/
theorem rollback_coalesceFrom_of_not_mem
    (log : List (Slot × Payload)) (seen : List Slot)
    (store : Slot → Payload) (slot : Slot) (fresh : slot ∉ seen) :
    rollback (coalesceFrom seen log) store slot = rollback log store slot := by
  induction log generalizing seen with
  | nil => rfl
  | cons entry rest ih =>
      by_cases already : entry.1 ∈ seen
      · have different : slot ≠ entry.1 := by
          intro same
          exact fresh (same ▸ already)
        simpa [coalesceFrom, already, rollback, restore, different] using
          ih seen fresh
      · by_cases same : slot = entry.1
        · simp [coalesceFrom, already, rollback, restore, same]
        · have newFresh : slot ∉ entry.1 :: seen := by
            simp [same, fresh]
          simpa [coalesceFrom, already, rollback, restore, same] using
            ih (entry.1 :: seen) newFresh

/-- One interval can be coalesced for every current store, including stores
not produced by the logged writes. The complete slot payload is preserved. -/
theorem rollback_coalesce (log : List (Slot × Payload))
    (store : Slot → Payload) :
    rollback (coalesce log) store = rollback log store := by
  funext slot
  exact rollback_coalesceFrom_of_not_mem log [] store slot (by simp)

theorem coalesceFrom_length_le (log : List (Slot × Payload)) (seen : List Slot) :
    (coalesceFrom seen log).length ≤ log.length := by
  induction log generalizing seen with
  | nil => simp [coalesceFrom]
  | cons entry rest ih =>
      by_cases already : entry.1 ∈ seen
      · simpa [coalesceFrom, already] using
          Nat.le_trans (ih seen) (Nat.le_succ rest.length)
      · simpa [coalesceFrom, already] using Nat.succ_le_succ (ih (entry.1 :: seen))

theorem coalesce_length_le (log : List (Slot × Payload)) :
    (coalesce log).length ≤ log.length :=
  coalesceFrom_length_le log []

/-- Coalescing only removes whole historical entries, preserving the order and
complete payloads of those retained. -/
theorem coalesceFrom_sublist (log : List (Slot × Payload)) (seen : List Slot) :
    List.Sublist (coalesceFrom seen log) log := by
  induction log generalizing seen with
  | nil => exact .refl []
  | cons entry rest ih =>
      by_cases already : entry.1 ∈ seen
      · simpa [coalesceFrom, already] using (ih seen).cons entry
      · simpa [coalesceFrom, already] using (ih (entry.1 :: seen)).cons_cons entry

theorem coalesceFrom_excludes_seen (log : List (Slot × Payload)) (seen : List Slot)
    (entry : Slot × Payload) (member : entry ∈ coalesceFrom seen log) :
    entry.1 ∉ seen := by
  induction log generalizing seen with
  | nil => simp [coalesceFrom] at member
  | cons head rest ih =>
      by_cases already : head.1 ∈ seen
      · exact ih seen (by simpa [coalesceFrom, already] using member)
      · simp only [coalesceFrom, already, ↓reduceIte, List.mem_cons] at member
        rcases member with same | tail
        · simpa [same] using already
        · intro inSeen
          exact ih (head.1 :: seen) tail (List.mem_cons_of_mem _ inSeen)

theorem coalesceFrom_distinct_slots (log : List (Slot × Payload)) (seen : List Slot) :
    (coalesceFrom seen log).Pairwise (fun left right => left.1 ≠ right.1) := by
  induction log generalizing seen with
  | nil => simp [coalesceFrom]
  | cons head rest ih =>
      by_cases already : head.1 ∈ seen
      · simpa [coalesceFrom, already] using ih seen
      · simp only [coalesceFrom, already, ↓reduceIte, List.pairwise_cons]
        refine ⟨?_, ih (head.1 :: seen)⟩
        intro entry member same
        exact coalesceFrom_excludes_seen rest (head.1 :: seen) entry member
          (by simp [same])

/-- Each interval is transformed independently. Empty intervals retain repeated
marks; the transformation never silently combines neighboring intervals. -/
def coalesceIntervals (intervals : List (List (Slot × Payload))) :
    List (List (Slot × Payload)) :=
  intervals.map coalesce

theorem rollback_coalesceIntervals (intervals : List (List (Slot × Payload)))
    (store : Slot → Payload) :
    rollback (coalesceIntervals intervals).flatten store =
      rollback intervals.flatten store := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
      simp only [coalesceIntervals, List.map_cons, List.flatten_cons, rollback_append]
      rw [rollback_coalesce]
      exact congrArg (rollback interval) ih

/-- A mark is the number of entries before an interval boundary. -/
def boundaryMark (intervals : List (List (Slot × Payload))) (boundary : Nat) : Nat :=
  ((intervals.take boundary).flatten).length

/-- Store observation after undoing the suffix. The correspondence theorems
use computed in-bounds marks; an invalid raw runtime mark is not modeled. -/
def rollbackAt (log : List (Slot × Payload)) (mark : Nat)
    (store : Slot → Payload) : Slot → Payload :=
  rollback (log.drop mark) store

omit [DecidableEq Slot] in
theorem drop_boundaryMark (intervals : List (List (Slot × Payload))) (boundary : Nat) :
    intervals.flatten.drop (boundaryMark intervals boundary) =
      (intervals.drop boundary).flatten := by
  have split : (intervals.take boundary).flatten ++ (intervals.drop boundary).flatten =
      intervals.flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  unfold boundaryMark
  rw [← split]
  simp

omit [DecidableEq Slot] in
theorem boundaryMark_le (intervals : List (List (Slot × Payload))) (boundary : Nat) :
    boundaryMark intervals boundary ≤ intervals.flatten.length := by
  have split : (intervals.take boundary).flatten ++ (intervals.drop boundary).flatten =
      intervals.flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  unfold boundaryMark
  rw [← split, List.length_append]
  exact Nat.le_add_right _ _

/-- All marked rollback boundaries survive, using the actually computed new
prefix lengths. No hypothesis supplies a target/source agreement theorem. -/
theorem rollbackAt_coalesceIntervals (intervals : List (List (Slot × Payload)))
    (boundary : Nat) (store : Slot → Payload) :
    rollbackAt (coalesceIntervals intervals).flatten
        (boundaryMark (coalesceIntervals intervals) boundary) store =
      rollbackAt intervals.flatten (boundaryMark intervals boundary) store := by
  simp only [rollbackAt, drop_boundaryMark, coalesceIntervals, ← List.map_drop]
  exact rollback_coalesceIntervals (intervals.drop boundary) store

/-- Additional writes after compaction can be undone before rolling back any
older marked interval. -/
theorem rollback_coalesceIntervals_append
    (intervals : List (List (Slot × Payload))) (later : List (Slot × Payload))
    (store : Slot → Payload) :
    rollback ((coalesceIntervals intervals).flatten ++ later) store =
      rollback (intervals.flatten ++ later) store := by
  simp only [rollback_append]
  exact rollback_coalesceIntervals intervals (rollback later store)

/-- New writes after compaction also preserve every older marked rollback,
not only the oldest interval boundary. -/
theorem rollbackAt_coalesceIntervals_append
    (intervals : List (List (Slot × Payload))) (boundary : Nat)
    (later : List (Slot × Payload)) (store : Slot → Payload) :
    rollbackAt ((coalesceIntervals intervals).flatten ++ later)
        (boundaryMark (coalesceIntervals intervals) boundary) store =
      rollbackAt (intervals.flatten ++ later) (boundaryMark intervals boundary) store := by
  simp only [rollbackAt,
    List.drop_append_of_le_length (boundaryMark_le _ _), rollback_append]
  exact rollbackAt_coalesceIntervals intervals boundary (rollback later store)

/-- Positive control: repeated writes within one interval really disappear. -/
example : coalesce ([(0, 7), (1, 4), (0, 9)] : List (Nat × Nat)) = [(0, 7), (1, 4)] := by
  decide

/-- Two intervals retain both saved values of a repeatedly written slot. -/
example : coalesceIntervals ([[(0, 0)], [(0, 1)]] : List (List (Nat × Nat))) =
    [[(0, 0)], [(0, 1)]] := by
  decide

/-- Global coalescing preserves the outer rollback, but cannot preserve an
inner mark: old value 0, then old value 1, with current value 2. No offset in
the globally coalesced log recovers the required inner value 1. -/
theorem global_coalescing_loses_inner_boundary (mark : Nat) :
    rollbackAt (coalesce ([(0, 0), (0, 1)] : List (Nat × Nat))) mark (fun _ => 2) 0 ≠
      rollbackAt [(0, 0), (0, 1)] 1 (fun _ => 2) 0 := by
  cases mark <;> simp [coalesce, coalesceFrom, rollbackAt, rollback, restore]

/-! ## Forgetting slots outside the live rollback support

An older choice observes only its protected prefix. Entries for slots outside
every live choice's prefix may therefore be removed, but the theorem is now
restricted to that support, not equality of all initialized storage. Current
goals must remain separately rooted; this operation changes only the undo log.
-/

/-- Retain only history for slots observable by the remaining rollback clients. -/
def retainLive (live : Slot → Bool) (log : List (Slot × Payload)) :
    List (Slot × Payload) :=
  log.filter (fun entry => live entry.1)

/-- Restoring a slot never consults the current payload of another slot. -/
theorem rollback_congr_at (log : List (Slot × Payload))
    (left right : Slot → Payload) (slot : Slot) (same : left slot = right slot) :
    rollback log left slot = rollback log right slot := by
  induction log with
  | nil => exact same
  | cons entry rest ih =>
      by_cases hit : slot = entry.1
      · simp [rollback, restore, hit]
      · simpa [rollback, restore, hit] using ih

theorem rollback_retainLive (live : Slot → Bool) (log : List (Slot × Payload))
    (store : Slot → Payload) (slot : Slot) (observed : live slot = true) :
    rollback (retainLive live log) store slot = rollback log store slot := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
      by_cases kept : live entry.1 = true
      · by_cases hit : slot = entry.1
        · simp [retainLive, kept, rollback, restore, hit]
        · simpa [retainLive, kept, rollback, restore, hit] using ih
      · have different : slot ≠ entry.1 := by
          intro same
          exact kept (same ▸ observed)
        simpa [retainLive, kept, rollback, restore, different] using ih

/-- Drop dead-slot history and coalesce separately within each marked interval. -/
def compactLiveIntervals (live : Slot → Bool)
    (intervals : List (List (Slot × Payload))) : List (List (Slot × Payload)) :=
  intervals.map (fun interval => coalesce (retainLive live interval))

theorem rollback_compactLiveIntervals (live : Slot → Bool)
    (intervals : List (List (Slot × Payload))) (store : Slot → Payload)
    (slot : Slot) (observed : live slot = true) :
    rollback (compactLiveIntervals live intervals).flatten store slot =
      rollback intervals.flatten store slot := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
      simp only [compactLiveIntervals, List.map_cons, List.flatten_cons, rollback_append]
      rw [rollback_coalesce, rollback_retainLive live interval _ slot observed]
      exact rollback_congr_at interval _ _ slot ih

/-- Every retained marked rollback has exactly the same observed slots after
filtering and coalescing. Marks are translated by actual retained lengths. -/
theorem rollbackAt_compactLiveIntervals (live : Slot → Bool)
    (intervals : List (List (Slot × Payload))) (boundary : Nat)
    (store : Slot → Payload) (slot : Slot) (observed : live slot = true) :
    rollbackAt (compactLiveIntervals live intervals).flatten
        (boundaryMark (compactLiveIntervals live intervals) boundary) store slot =
      rollbackAt intervals.flatten (boundaryMark intervals boundary) store slot := by
  simp only [rollbackAt, drop_boundaryMark, compactLiveIntervals, ← List.map_drop]
  exact rollback_compactLiveIntervals live (intervals.drop boundary) store slot observed

/-- Undoing arbitrary later writes before an older retained boundary keeps the
same live-slot guarantee; no assumption restricts which slots later writes use. -/
theorem rollbackAt_compactLiveIntervals_append (live : Slot → Bool)
    (intervals : List (List (Slot × Payload))) (boundary : Nat)
    (later : List (Slot × Payload)) (store : Slot → Payload)
    (slot : Slot) (observed : live slot = true) :
    rollbackAt ((compactLiveIntervals live intervals).flatten ++ later)
        (boundaryMark (compactLiveIntervals live intervals) boundary) store slot =
      rollbackAt (intervals.flatten ++ later)
        (boundaryMark intervals boundary) store slot := by
  simp only [rollbackAt,
    List.drop_append_of_le_length (boundaryMark_le _ _), rollback_append]
  exact rollbackAt_compactLiveIntervals live intervals boundary
    (rollback later store) slot observed

/-- Specialization to a live goal-stack prefix; an individual choice can
observe any shorter prefix without requiring equality above its height. -/
theorem rollbackAt_compact_prefix
    (intervals : List (List (Nat × Payload))) (boundary protectedHeight choiceHeight : Nat)
    (store : Nat → Payload) (choiceBound : choiceHeight ≤ protectedHeight)
    (slot : Nat) (belowChoice : slot < choiceHeight) :
    rollbackAt (compactLiveIntervals (fun index => decide (index < protectedHeight))
        intervals).flatten
        (boundaryMark (compactLiveIntervals (fun index => decide (index < protectedHeight))
          intervals) boundary) store slot =
      rollbackAt intervals.flatten (boundaryMark intervals boundary) store slot := by
  exact rollbackAt_compactLiveIntervals _ intervals boundary store slot
    (by simpa using Nat.lt_of_lt_of_le belowChoice choiceBound)

/-- A future mark is relative to the new log end. Undoing only subsequent
writes does not inspect older history at all, including discarded high slots. -/
theorem rollbackAt_append_future (older later : List (Slot × Payload))
    (offset : Nat) (store : Slot → Payload) :
    rollbackAt (older ++ later) (older.length + offset) store =
      rollbackAt later offset store := by
  simp [rollbackAt, List.drop_append, List.drop_eq_nil_of_le, Nat.le_add_right]

/-- Replacement of any older history preserves a future marked rollback on
the entire store, even if future choices protect a larger prefix. -/
theorem rollbackAt_future_history_independent
    (oldHistory newHistory later : List (Slot × Payload))
    (offset : Nat) (store : Slot → Payload) :
    rollbackAt (newHistory ++ later) (newHistory.length + offset) store =
      rollbackAt (oldHistory ++ later) (oldHistory.length + offset) store := by
  rw [rollbackAt_append_future, rollbackAt_append_future]

/-- A necessary scope control: dropping slot 1 preserves prefix [0,1), but
does not preserve rollback's value at the discarded slot itself. -/
example :
    rollback (retainLive (fun index => decide (index < 1))
      ([(0, 4), (1, 7)] : List (Nat × Nat))) (fun _ => 9) 1 = 9 ∧
    rollback [(0, 4), (1, 7)] (fun _ => 9) 1 = 7 := by
  decide

end Mettapedia.Machines.MarkedUndoLog
