import Mettapedia.Machines.RelationIdReuse
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.CapturedRowReaders

/-!
# Fact, descriptor and captured-view root support

Column ownership does not account for descriptor fields or other readers.
This bridge names those separate owners and connects their direct root
support to the existing finite-heap reachability model. Reuse is checked
against the complete protected footprint, not just the direct root set.

These sets describe reachability support, not callback multiplicity. They do
not prove that retaining a descriptor is the optimal cache policy, or that a
native tracer has discovered all roots.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationRootOwners

open RelationColumnOwnership RelationIdReuse
variable {Id Value : Type} [DecidableEq Id]

inductive Owner | columns | descriptor | captured
  deriving DecidableEq

structure OtherOwners (Id : Type) where
  descriptor : Finset Id
  captured : Finset Id

def needed (state : State Id) (others : OtherOwners Id) : Finset Id :=
  state.counters.owned ∪ others.descriptor ∪ others.captured

def roots (state : State Id) (others : OtherOwners Id) : ResourceOwnership.Roots Owner Id :=
  state.counters.owned.image (fun id => (Owner.columns, id)) ∪
  others.descriptor.image (fun id => (Owner.descriptor, id)) ∪
  others.captured.image (fun id => (Owner.captured, id))

theorem roots_addresses (state : State Id) (others : OtherOwners Id) :
    ResourceOwnership.rootAddresses (roots state others) = needed state others := by
  simp [ResourceOwnership.rootAddresses, roots, needed, Finset.image_union, Finset.image_image]

theorem needed_iff (state : State Id) (valid : state.Valid) (others : OtherOwners Id) (id : Id) :
    id ∈ needed state others ↔ (∃ row ∈ state.rows, id ∈ row) ∨
      id ∈ others.descriptor ∨ id ∈ others.captured := by
  simp [needed, owned_iff_live_column state valid]

theorem roots_valid (state : State Id) (others : OtherOwners Id) (heap : ResourceOwnership.Heap Id Value)
    (allocated : needed state others ⊆ heap.allocated) : ResourceOwnership.ValidRoots heap (roots state others) := by
  apply (ResourceOwnership.rootAddresses_subset_iff_validRoots heap _).mp
  simpa [roots_addresses] using allocated

theorem needed_in_footprint (state : State Id) (others : OtherOwners Id) (heap : ResourceOwnership.Heap Id Value)
    (allocated : needed state others ⊆ heap.allocated) :
    needed state others ⊆ ResourceOwnership.footprint heap (roots state others) := by
  intro id member
  apply (ResourceOwnership.mem_footprint _ _ _).mpr
  exact .root ⟨allocated member, by simpa [roots_addresses] using member⟩

def heapLookup (heap : ResourceOwnership.Heap Id Value) : Lookup Id Value :=
  fun id => (heap.lookup id).map ResourceOwnership.Cell.value

theorem live_columns_resolve (state : State Id) (valid : state.Valid) (others : OtherOwners Id)
    (heap : ResourceOwnership.Heap Id Value) (allocated : needed state others ⊆ heap.allocated)
    (row : List Id) (member : row ∈ state.rows) (id : Id) (column : id ∈ row) :
    ∃ value, heapLookup heap id = some value := by
  have held := (owned_iff_live_column state valid id).mpr ⟨row, member, column⟩
  have present := allocated (show id ∈ needed state others by simp [needed, held])
  obtain ⟨cell, found⟩ := (heap.allocated_iff id).mp present
  exact ⟨cell.value, by simp [heapLookup, found]⟩

theorem protected_reuse_preserves_all_reads (state : State Id) (valid : state.Valid)
    (others : OtherOwners Id) (heap : ResourceOwnership.Heap Id Value)
    (allocated : needed state others ⊆ heap.allocated)
    (before after : Lookup Id Value) (id : Id) (value : Value)
    (accepted : reuse (ResourceOwnership.footprint heap (roots state others)) before id value = some after) :
    denote before state.rows = denote after state.rows ∧
      (∀ key ∈ others.descriptor, before key = after key) ∧
      (∀ key ∈ others.captured, before key = after key) := by
  have covers := needed_in_footprint state others heap allocated
  have stable := reuse_preserves _ before id value after accepted
  refine ⟨reuse_preserves_rows state valid _ ?_ before after id value accepted, ?_, ?_⟩
  · intro key member
    exact covers (by simp [needed, member])
  · intro key member
    exact stable key (covers (by simp [needed, member]))
  · intro key member
    exact stable key (covers (by simp [needed, member]))

def captureRoots (store : CapturedRowReaders.Store Id) (reader : CapturedRowReaders.Cursor Id) : Option (Finset Id) :=
  (CapturedRowReaders.rows store reader).map List.toFinset

def readCaptured (store : CapturedRowReaders.Store Id) (reader : CapturedRowReaders.Cursor Id)
    (lookup : Lookup Id Value) : Option (List (Option Value)) :=
  (CapturedRowReaders.remaining store reader).map (List.map lookup)

theorem captured_roots_preserve_values (store : CapturedRowReaders.Store Id)
    (reader : CapturedRowReaders.Cursor Id) (held : Finset Id)
    (captured : captureRoots store reader = some held)
    (before after : Lookup Id Value) (stable : Preserves held before after) :
    readCaptured store reader before = readCaptured store reader after := by
  obtain ⟨saved, found, same⟩ := Option.map_eq_some_iff.mp captured
  subst held
  simp only [readCaptured, CapturedRowReaders.remaining, found, Option.map_some]
  congr 1
  apply List.map_congr_left
  intro id member
  exact stable id (by simpa using List.mem_of_mem_drop member)

namespace Controls

theorem empty_facts_do_not_imply_empty_root_support :
    (empty : State Nat).rows = [] ∧ needed empty (⟨{3}, {7}⟩ : OtherOwners Nat) = {3, 7} := by decide

theorem column_release_keeps_descriptor_and_reader_roots :
    let state : State Nat := (removeRow (insertRow empty [7]) [7]).2
    state.counters.owned = ∅ ∧ needed state (⟨{7}, {7}⟩ : OtherOwners Nat) = {7} := by decide

end Controls
end Mettapedia.Machines.RelationRootOwners
