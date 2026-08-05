import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Dedup

/-!
# Counted PathMap batch-mutation refinement

A counted PathMap stores a finite bag of logical rows.  The native batch path
aggregates a caller-ordered list of additions or removals on a private snapshot
and publishes the resulting bag once.  The oracle path applies the same list
one occurrence at a time.

This module proves the semantic seam between those implementations.  It keeps
revision publication separate from bag contents: the batch and oracle have the
same final multiplicities, while a nonempty successful batch advances the
public revision at most once.  Failed preflight leaves both bag and revision
unchanged.

Both positive and negative witnesses are included.  Duplicate additions and
removal of absent rows behave exactly like singular updates; projecting to a
set does not, so presence-only storage cannot implement this contract.
-/

namespace Mettapedia.OSLF.PathMap.CountedBatchRefinement

variable {Row : Type}

/-- Apply a caller-ordered addition list through the singular occurrence API. -/
def sequentialAdd (initial : Multiset Row) (rows : List Row) : Multiset Row :=
  rows.foldl (fun bag row => bag + {row}) initial

/-- Apply a caller-ordered removal list through the singular occurrence API.
Each update removes at most one occurrence; an absent row is a no-op. -/
def sequentialRemove [DecidableEq Row]
    (initial : Multiset Row) (rows : List Row) : Multiset Row :=
  rows.foldl Multiset.erase initial

/-- The counted batch-add result: aggregate the packet's occurrence bag. -/
def batchAdd (initial : Multiset Row) (rows : List Row) : Multiset Row :=
  initial + (rows : Multiset Row)

/-- The counted batch-remove result: truncated pointwise subtraction. -/
def batchRemove [DecidableEq Row]
    (initial : Multiset Row) (rows : List Row) : Multiset Row :=
  initial - (rows : Multiset Row)

/-- A counted batch addition has exactly the singular oracle's final bag. -/
theorem batchAdd_eq_sequentialAdd (initial : Multiset Row) (rows : List Row) :
    batchAdd initial rows = sequentialAdd initial rows := by
  induction rows generalizing initial with
  | nil => simp [batchAdd, sequentialAdd]
  | cons row rest ih =>
      change batchAdd initial (row :: rest) =
        sequentialAdd (initial + {row}) rest
      rw [← ih]
      change initial + (row ::ₘ (rest : Multiset Row)) =
        (initial + {row}) + (rest : Multiset Row)
      rw [← Multiset.singleton_add, ← Multiset.add_assoc]

/-- A counted batch removal has exactly the singular oracle's final bag,
including repeated removals and absent-row no-ops. -/
theorem batchRemove_eq_sequentialRemove [DecidableEq Row]
    (initial : Multiset Row) (rows : List Row) :
    batchRemove initial rows = sequentialRemove initial rows := by
  induction rows generalizing initial with
  | nil => simp [batchRemove, sequentialRemove]
  | cons row rest ih =>
      change batchRemove initial (row :: rest) =
        sequentialRemove (initial.erase row) rest
      rw [← ih]
      change initial - (row ::ₘ (rest : Multiset Row)) =
        initial.erase row - (rest : Multiset Row)
      exact Multiset.sub_cons row initial (rest : Multiset Row)

/-- Public state records the logical bag and the revision visible to readers. -/
structure PublishedStore (Row : Type) where
  bag : Multiset Row
  revision : Nat
deriving DecidableEq

/-- Publish one completed add transaction.  Empty packets are semantic no-ops
and therefore do not create a revision. -/
def publishAdd (store : PublishedStore Row) (rows : List Row) : PublishedStore Row :=
  if rows.isEmpty then store
  else { bag := batchAdd store.bag rows, revision := store.revision + 1 }

/-- Publish one completed remove transaction.  A packet that removes no live
occurrence is a semantic no-op and does not create a revision. -/
def publishRemove [DecidableEq Row]
    (store : PublishedStore Row) (rows : List Row) : PublishedStore Row :=
  let next := batchRemove store.bag rows
  if next = store.bag then store
  else { bag := next, revision := store.revision + 1 }

/-- A successful nonempty add batch advances exactly one public revision. -/
theorem publishAdd_revision_once (store : PublishedStore Row) {rows : List Row}
    (nonempty : rows ≠ []) :
    (publishAdd store rows).revision = store.revision + 1 := by
  simp [publishAdd, List.isEmpty_iff, nonempty]

/-- The bag published by a nonempty add batch is the singular oracle's bag. -/
theorem publishAdd_bag_eq_oracle (store : PublishedStore Row) {rows : List Row}
    (nonempty : rows ≠ []) :
    (publishAdd store rows).bag = sequentialAdd store.bag rows := by
  simp [publishAdd, List.isEmpty_iff, nonempty, batchAdd_eq_sequentialAdd]

/-- A remove batch that changes the bag advances exactly one public revision. -/
theorem publishRemove_revision_once [DecidableEq Row]
    (store : PublishedStore Row) (rows : List Row)
    (changed : batchRemove store.bag rows ≠ store.bag) :
    (publishRemove store rows).revision = store.revision + 1 := by
  simp [publishRemove, changed]

/-- The bag published by a changing remove batch is the singular oracle's bag. -/
theorem publishRemove_bag_eq_oracle [DecidableEq Row]
    (store : PublishedStore Row) (rows : List Row)
    (changed : batchRemove store.bag rows ≠ store.bag) :
    (publishRemove store rows).bag = sequentialRemove store.bag rows := by
  have changed' : sequentialRemove store.bag rows ≠ store.bag := by
    simpa [batchRemove_eq_sequentialRemove] using changed
  simp [publishRemove, batchRemove_eq_sequentialRemove, changed']

/-- Preflight and snapshot mutation are modelled as a transaction result. -/
def transactAdd (valid : Row → Bool) (store : PublishedStore Row)
    (rows : List Row) : PublishedStore Row × Bool :=
  if rows.all valid then (publishAdd store rows, true) else (store, false)

/-- A rejected packet cannot expose a partially changed bag or revision. -/
theorem transactAdd_failure_rollback (valid : Row → Bool)
    (store : PublishedStore Row) (rows : List Row)
    (rejected : rows.all valid = false) :
    transactAdd valid store rows = (store, false) := by
  simp [transactAdd, rejected]

/-- A fully valid packet publishes the complete batch, never a prefix. -/
theorem transactAdd_success (valid : Row → Bool)
    (store : PublishedStore Row) (rows : List Row)
    (accepted : rows.all valid = true) :
    transactAdd valid store rows = (publishAdd store rows, true) := by
  simp [transactAdd, accepted]

/-! ## Positive and negative discriminators -/

private def duplicateStore : Multiset Nat := {7, 7, 9}

/-- Duplicate and absent-row behavior agrees on a concrete packet. -/
example :
    batchRemove duplicateStore [7, 5, 7, 7]
      = sequentialRemove duplicateStore [7, 5, 7, 7] := by
  exact batchRemove_eq_sequentialRemove _ _

example : Multiset.count 7 (batchAdd duplicateStore [7, 7]) = 4 := by
  decide

example : Multiset.count 7 (batchRemove duplicateStore [7, 5]) = 1 := by
  decide

/-- **Negative witness.**  A presence-only carrier collapses duplicate
occurrences and therefore cannot refine counted batch addition. -/
theorem support_projection_loses_batch_multiplicity :
    (batchAdd (0 : Multiset Nat) [7, 7]).dedup.card
      ≠ (batchAdd (0 : Multiset Nat) [7, 7]).card := by
  decide

end Mettapedia.OSLF.PathMap.CountedBatchRefinement
