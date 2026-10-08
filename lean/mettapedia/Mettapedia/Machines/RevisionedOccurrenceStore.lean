import Mettapedia.Machines.OccurrenceMachine
import Mathlib.Data.List.Perm.Basic

/-!
# Revision-scoped occurrence identities

An evaluator store carries several kinds of identity that must not be
interchanged.  A payload identifies a term value; a logical position identifies
one admitted occurrence of that payload; a store identity and revision delimit
the snapshot in which that position is meaningful.

This module states the small, policy-neutral contract needed at a dispatch/store
boundary.  It does not choose candidate order, matching semantics, or an
evaluation strategy.  An optimized candidate list may permute the exhaustive
list while retaining its occurrence bag, but that is deliberately weaker than
ordered equality.

The definitions are a mathematical contract for a checked native boundary;
they are not by themselves a refinement proof for a particular runtime.
-/

namespace Mettapedia.Machines

/-- A read-only view of one store revision. -/
structure RevisionedStoreView (StoreId Revision Entry : Type) where
  storeId : StoreId
  revision : Revision
  entries : List Entry

/-- A token for one live store revision. -/
structure StoreReadToken (StoreId Revision : Type) where
  storeId : StoreId
  revision : Revision
deriving DecidableEq

/-- Identity of one logical occurrence within one store revision. -/
structure StoreOccurrenceId (StoreId Revision : Type) where
  read : StoreReadToken StoreId Revision
  logicalIndex : Nat
deriving DecidableEq

namespace RevisionedStoreView

variable {StoreId Revision Entry : Type}

private theorem getElem?_eq_some_of_mem_zipIdx {entries : List Entry}
    {entry : Entry} {logicalIndex : Nat}
    (member : (entry, logicalIndex) ∈ entries.zipIdx) :
    entries[logicalIndex]? = some entry := by
  have located := List.exists_mem_zipIdx'.mp
    (show ∃ item ∈ entries.zipIdx, item = (entry, logicalIndex) from
      ⟨_, member, rfl⟩)
  obtain ⟨foundIndex, foundBound, pairEquality⟩ := located
  have indexEquality : foundIndex = logicalIndex :=
    (Prod.ext_iff.mp pairEquality).2
  subst indexEquality
  rw [List.getElem?_eq_getElem foundBound]
  exact congrArg some (Prod.ext_iff.mp pairEquality).1

/-- Capture the identity and revision of the current view. -/
def readToken (view : RevisionedStoreView StoreId Revision Entry) :
    StoreReadToken StoreId Revision :=
  ⟨view.storeId, view.revision⟩

/-- Name one logical position in the current view. -/
def occurrenceId (view : RevisionedStoreView StoreId Revision Entry)
    (logicalIndex : Nat) : StoreOccurrenceId StoreId Revision :=
  ⟨view.readToken, logicalIndex⟩

/-- Resolve an occurrence only when both its store and revision agree with the
current view. -/
def resolve [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision) : Option Entry :=
  if id.read.storeId = view.storeId ∧ id.read.revision = view.revision then
    view.entries[id.logicalIndex]?
  else
    none

@[simp] theorem resolve_current [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry) (logicalIndex : Nat) :
    view.resolve (view.occurrenceId logicalIndex) =
      view.entries[logicalIndex]? := by
  simp [resolve, occurrenceId, readToken]

@[simp] theorem resolve_wrong_store [DecidableEq StoreId]
    [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision)
    (wrongStore : id.read.storeId ≠ view.storeId) :
    view.resolve id = none := by
  simp [resolve, wrongStore]

@[simp] theorem resolve_stale [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (id : StoreOccurrenceId StoreId Revision)
    (stale : id.read.revision ≠ view.revision) :
    view.resolve id = none := by
  simp [resolve, stale]

/-- Replace the entries and explicitly advance to a caller-supplied revision.
The contract requires freshness; it does not prescribe a concrete counter. -/
def replaceRevision
    (view : RevisionedStoreView StoreId Revision Entry)
    (nextRevision : Revision) (nextEntries : List Entry) :
    RevisionedStoreView StoreId Revision Entry :=
  ⟨view.storeId, nextRevision, nextEntries⟩

/-- Any genuinely different revision rejects occurrence IDs captured from the
old revision, independently of the new payload list. -/
theorem old_occurrence_rejected_after_revision_change
    [DecidableEq StoreId] [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    (nextRevision : Revision) (nextEntries : List Entry)
    (changed : nextRevision ≠ view.revision) (logicalIndex : Nat) :
    (view.replaceRevision nextRevision nextEntries).resolve
        (view.occurrenceId logicalIndex) = none := by
  simp [resolve, replaceRevision, occurrenceId, readToken, changed.symm]

/-- Enumerate every logical occurrence in store order.  `zipIdx` ensures that
two equal payloads at different positions retain different identities. -/
def occurrences (view : RevisionedStoreView StoreId Revision Entry) :
    List (StoreOccurrenceId StoreId Revision × Entry) :=
  view.entries.zipIdx.map fun (entry, logicalIndex) =>
    (view.occurrenceId logicalIndex, entry)

@[simp] theorem occurrences_payloads
    (view : RevisionedStoreView StoreId Revision Entry) :
    view.occurrences.map Prod.snd = view.entries := by
  simp [occurrences, Function.comp_def, List.zipIdx_map_fst]

@[simp] theorem occurrences_length
    (view : RevisionedStoreView StoreId Revision Entry) :
    view.occurrences.length = view.entries.length := by
  simp [occurrences]

/-- Every enumerated occurrence resolves to the payload paired with it. -/
theorem resolve_of_mem_occurrences [DecidableEq StoreId]
    [DecidableEq Revision]
    (view : RevisionedStoreView StoreId Revision Entry)
    {id : StoreOccurrenceId StoreId Revision} {entry : Entry}
    (member : (id, entry) ∈ view.occurrences) :
    view.resolve id = some entry := by
  obtain ⟨⟨found, logicalIndex⟩, zipped, pairEquality⟩ :=
    List.mem_map.mp member
  cases pairEquality
  rw [resolve_current]
  exact getElem?_eq_some_of_mem_zipIdx zipped

/-- Equal payloads do not collapse two distinct logical occurrence IDs. -/
theorem occurrenceId_injective
    (view : RevisionedStoreView StoreId Revision Entry) {left right : Nat}
    (different : left ≠ right) :
    view.occurrenceId left ≠ view.occurrenceId right := by
  intro equalIds
  exact different (congrArg StoreOccurrenceId.logicalIndex equalIds)

/-- Exhaustive candidate equivalence forgets order but retains occurrence
multiplicity and identity. -/
def ExhaustiveCandidateRefinement
    (reference contender :
      List (StoreOccurrenceId StoreId Revision × Entry)) : Prop :=
  contender.Perm reference

/-- Exhaustive refinement transports to the payload bag. -/
theorem ExhaustiveCandidateRefinement.payloads
    {reference contender :
      List (StoreOccurrenceId StoreId Revision × Entry)}
    (refines : ExhaustiveCandidateRefinement reference contender) :
    (contender.map Prod.snd).Perm (reference.map Prod.snd) :=
  refines.map Prod.snd

end RevisionedStoreView

/-! ## Captured child views and owned enumeration

The child carries a captured parent observation and a separate live identity.
Materialization changes its storage mode; writes advance only the child's view.
The cursor captures a view rather than looking up a mutable store at each step.
These are model laws for those native boundaries, not verification of C memory.
-/

namespace OwnedFork

variable {StoreId Entry : Type}

structure Child (StoreId Entry : Type) where
  captured : RevisionedStoreView StoreId Nat Entry
  storeId : StoreId
  revision : Nat
  privateRows : Option (List Entry)

def Child.rows (child : Child StoreId Entry) : List Entry :=
  child.privateRows.getD child.captured.entries

def capture (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId) :
    Child StoreId Entry := ⟨parent, childId, 0, none⟩

def Child.materialize (child : Child StoreId Entry) : Child StoreId Entry :=
  match child.privateRows with
  | none => { child with privateRows := some child.captured.entries }
  | some _ => child

def Child.write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    Child StoreId Entry :=
  let owned := child.materialize
  { owned with privateRows := some (update owned.rows), revision := owned.revision + 1 }

def Child.view (child : Child StoreId Entry) : RevisionedStoreView StoreId Nat Entry :=
  ⟨child.storeId, child.revision, child.rows⟩

@[simp] theorem rows_materialize (child : Child StoreId Entry) :
    child.materialize.rows = child.rows := by
  cases h : child.privateRows <;> simp [Child.materialize, Child.rows, h]

@[simp] theorem captured_materialize (child : Child StoreId Entry) :
    child.materialize.captured = child.captured := by
  cases h : child.privateRows <;> simp [Child.materialize, h]

@[simp] theorem rows_write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    (child.write update).rows = update child.rows := by
  change update child.materialize.rows = update child.rows
  rw [rows_materialize]

@[simp] theorem captured_write (child : Child StoreId Entry) (update : List Entry → List Entry) :
    (child.write update).captured = child.captured := by
  simp [Child.write]

/-- Any finite sequence of local operations agrees with applying those operations
to a private ordered row list, while preserving the complete captured parent. -/
theorem write_sequence (child : Child StoreId Entry)
    (updates : List (List Entry → List Entry)) :
    (updates.foldl Child.write child).rows = updates.foldl (fun rows update => update rows) child.rows ∧
      (updates.foldl Child.write child).captured = child.captured := by
  induction updates generalizing child with
  | nil => exact ⟨rfl, rfl⟩
  | cons update rest ih =>
    simpa [List.foldl_cons] using ih (child.write update)

/-- A child's row list retains repeated occurrences; no set conversion occurs. -/
theorem capture_occurrences (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId) :
    (capture parent childId).view.occurrences.map Prod.snd = parent.entries := by
  simp [capture, Child.view, Child.rows]

/-- Capturing a parent revision gives that revision's entries even if the live
parent later replaces its contents. The old token cannot name the new parent. -/
theorem parent_revision_isolation [DecidableEq StoreId]
    (parent : RevisionedStoreView StoreId Nat Entry) (childId : StoreId)
    (next : Nat) (rows : List Entry) (changed : next ≠ parent.revision) (index : Nat) :
    (capture parent childId).rows = parent.entries ∧
      (parent.replaceRevision next rows).resolve (parent.occurrenceId index) = none := by
  exact ⟨rfl, parent.old_occurrence_rejected_after_revision_change next rows changed index⟩

structure Cursor (StoreId Entry : Type) where
  captured : RevisionedStoreView StoreId Nat Entry
  next : Nat

def Cursor.step (cursor : Cursor StoreId Entry) : Option (Entry × Cursor StoreId Entry) :=
  cursor.captured.entries[cursor.next]?.map fun row => (row, { cursor with next := cursor.next + 1 })

def Cursor.read (cursor : Cursor StoreId Entry) : Nat → List Entry
  | 0 => []
  | count + 1 => match cursor.step with
    | none => []
    | some (row, rest) => row :: rest.read count

/-- The iterative cursor returns exactly the captured prefix at its current
position, including repeated payloads and an empty prefix at exhaustion. -/
theorem cursor_prefix (cursor : Cursor StoreId Entry) (count : Nat) :
    cursor.read count = (cursor.captured.entries.drop cursor.next).take count := by
  induction count generalizing cursor with
  | zero => simp [Cursor.read]
  | succ count ih =>
    cases h : cursor.captured.entries[cursor.next]? with
    | none =>
      have beyond : cursor.captured.entries.length ≤ cursor.next := by
        exact List.getElem?_eq_none_iff.mp h
      simp [Cursor.read, Cursor.step, h, List.drop_eq_nil_of_le beyond]
    | some row =>
      obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp h
      rw [List.drop_eq_getElem_cons bound]
      simp [Cursor.read, Cursor.step, h, ih, equal]

/-- Reading a pinned cursor after a write does not renew its token's currency.
The cursor returns old rows while the new live child rejects its occurrence ID. -/
theorem cursor_write_separates_read_and_currency [DecidableEq StoreId]
    (child : Child StoreId Entry) (update : List Entry → List Entry) (index count : Nat) :
    (Cursor.mk child.view index).read count = (child.rows.drop index).take count ∧
      (child.write update).view.resolve (child.view.occurrenceId index) = none := by
  constructor
  · exact cursor_prefix _ count
  · cases h : child.privateRows <;>
      simp [Child.write, Child.materialize, Child.view, RevisionedStoreView.resolve,
        RevisionedStoreView.occurrenceId, RevisionedStoreView.readToken, h]

example : (capture (⟨0, 7, [42, 42]⟩ : RevisionedStoreView Nat Nat Nat) 1).rows = [42, 42] := rfl
example : (Cursor.mk (⟨1, 0, [42, 42]⟩ : RevisionedStoreView Nat Nat Nat) 0).read 2 = [42, 42] := rfl

end OwnedFork

/-! ## Positive and negative discriminators -/

private def duplicateView : RevisionedStoreView Unit Nat Nat :=
  ⟨(), 7, [42, 42]⟩

example : duplicateView.resolve (duplicateView.occurrenceId 0) = some 42 := by
  rfl

example : duplicateView.occurrenceId 0 ≠ duplicateView.occurrenceId 1 := by
  exact duplicateView.occurrenceId_injective (by decide)

example :
    (duplicateView.replaceRevision 8 [42]).resolve
      (duplicateView.occurrenceId 0) = none := by
  exact duplicateView.old_occurrence_rejected_after_revision_change
    8 [42] (by decide) 0

/-- Candidate permutation is sufficient for an exhaustive occurrence bag,
but not for ordered or finite-prefix observations. -/
example :
    [duplicateView.occurrenceId 0, duplicateView.occurrenceId 1].Perm
      [duplicateView.occurrenceId 1, duplicateView.occurrenceId 0] := by
  exact List.Perm.swap _ _ []

example :
    [duplicateView.occurrenceId 0, duplicateView.occurrenceId 1] ≠
      [duplicateView.occurrenceId 1, duplicateView.occurrenceId 0] := by
  simp [RevisionedStoreView.occurrenceId,
    RevisionedStoreView.readToken, duplicateView]

end Mettapedia.Machines
