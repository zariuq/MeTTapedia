import Mettapedia.Languages.VibeITP.Native.TermHeapTargetEffects
import Mettapedia.Languages.VibeITP.Native.TermHeapAllocationControls

/-! Exact target-memory writes, allocation and missing-cell refusals. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeapTargetControls

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeSystemAllocation NativeWord64
open HeapCells TermHeap TermHeapControls

def targetMemory : TargetMemory :=
  ⟨fun storage index => (memory.cells storage index).map encodeValue,
   fun storage => (memory.owned storage).map encode⟩

theorem memory_related : MemoryRelated memory targetMemory := ⟨fun _ _ => rfl, fun _ => rfl⟩

def countAfter : TargetMemory :=
  targetStoreCell targetMemory 101 0 { rootCell with references := 2 }.targetValue

theorem target_count_write : targetWrite targetMemory ⟨101, 0, [6]⟩ (.word 2) = some countAfter := rfl

theorem target_count_write_has_same_independent_term :
    ∃ sourceAfter, MemoryRelated sourceAfter countAfter ∧ ArrayBaseDiscipline.Memory sourceAfter ∧
      At sourceAfter signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  obtain ⟨sourceAfter, _, related, valid, meaning⟩ := target_term_count_write_preserves_meaning
    memory_related HeapArrayDisciplineControls.ordinary_memory_has_discipline
    101 0 rootCell 2 rfl target_count_write shared_application_represented
  exact ⟨sourceAfter, related, valid, meaning⟩

theorem missing_target_count_cell_is_refused : targetWrite targetMemory ⟨103, 0, [6]⟩ (.word 2) = none := rfl

def allocationAfter : TargetMemory := targetInstall targetMemory 200 2 (fun _ => some (.word 0))

theorem target_allocation : TargetMalloc 2 (fun _ => some (.word 0))
    targetMemory (some ⟨200, 0, []⟩) allocationAfter := .success ⟨fun _ => rfl, rfl⟩

theorem target_allocation_has_same_independent_term :
    ∃ sourceAfter, MemoryRelated sourceAfter allocationAfter ∧ ArrayBaseDiscipline.Memory sourceAfter ∧
      At sourceAfter signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  have initialValid : ∀ index value, TermHeapAllocationControls.initial index = some value →
      ArrayBaseDiscipline.value value = true := by intro index value same; cases same; rfl
  obtain ⟨sourceAfter, _, related, valid, meaning⟩ := target_allocation_preserves_meaning
    memory_related HeapArrayDisciplineControls.ordinary_memory_has_discipline
    2 TermHeapAllocationControls.initial initialValid _ target_allocation shared_application_represented
  exact ⟨sourceAfter, related, valid, meaning⟩

theorem target_allocator_cannot_reuse_live_child (after : TargetMemory) :
    ¬ TargetMalloc 2 (fun _ => some (.word 0)) targetMemory (some childAddress) after := by
  intro allocated
  obtain ⟨sourceAfter, sourceAllocated, _⟩ := malloc_backward memory targetMemory memory_related
    2 TermHeapAllocationControls.initial (some childAddress) after allocated
  exact TermHeapAllocationControls.live_child_storage_cannot_be_reused sourceAfter sourceAllocated

end Mettapedia.Languages.VibeITP.Native.TermHeapTargetControls
