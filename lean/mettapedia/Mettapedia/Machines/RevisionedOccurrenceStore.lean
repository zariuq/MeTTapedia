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
