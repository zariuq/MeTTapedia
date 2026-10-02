import Mettapedia.Languages.VibeITP.Native.TermHeapAllocation
import Mettapedia.Languages.VibeITP.Native.HeapArrayDisciplineControls

/-! Successful and failed allocations on the concrete shared-term heap. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeapAllocationControls

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeSystemAllocation
open HeapCells TermHeap TermHeapControls

def initial : Nat → Option SourceValue := fun _ => some (.word 0)
def allocatedMemory : SourceMemory := sourceInstall memory 200 2 initial

theorem fresh_allocation : SourceMalloc 2 initial memory (some ⟨200, 0, []⟩) allocatedMemory :=
  .success ⟨rfl, fun _ => rfl⟩

theorem allocation_preserves_shared_graph :
    At allocatedMemory signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  allocation_preserves_term fresh_allocation shared_application_represented

theorem allocation_preserves_literal_bytes :
    At allocatedMemory signature markers literalAddress (.lit [65, 66]) :=
  allocation_preserves_term fresh_allocation literal_represented

theorem allocation_preserves_array_profile : ArrayBaseDiscipline.Memory allocatedMemory := by
  apply ArrayAllocation.malloc_discipline HeapArrayDisciplineControls.ordinary_memory_has_discipline
    (allocated := fresh_allocation)
  intro index value present
  cases present
  rfl

theorem allocated_extent_exact :
    allocatedMemory.owned 200 = some 2 ∧
    allocatedMemory.cells 200 0 = some (.word 0) ∧
    allocatedMemory.cells 200 1 = some (.word 0) ∧ allocatedMemory.cells 200 2 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem failure_preserves_shared_graph :
    SourceMalloc 2 initial memory none memory ∧
    At memory signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  ⟨.failure memory, allocation_preserves_term (extent := 2) (initial := initial)
    (.failure memory) shared_application_represented⟩

theorem live_child_storage_cannot_be_reused (after : SourceMemory) :
    ¬ SourceMalloc 2 initial memory (some childAddress) after := by
  intro allocated
  exact (represented_term_avoids_new_storage allocated child_represented) rfl

theorem allocator_cannot_return_count_field (after : SourceMemory) :
    ¬ SourceMalloc 2 initial memory (some ⟨200, 0, [6]⟩) after :=
  ArrayAllocation.success_cannot_return_interior_pointer 2 initial memory after _ (by decide)

theorem null_cannot_initialize_nonempty_array (after : SourceMemory) :
    ¬ SourceInitialize none 2 (.word 0) memory after := by
  intro initialized
  cases initialized

def firstInitialized : SourceMemory := sourceStoreCell allocatedMemory 200 0 (.word 0)
def fullyInitialized : SourceMemory := sourceStoreCell firstInitialized 200 1 (.word 0)

theorem initializes_both_cells :
    SourceInitialize (some ⟨200, 0, []⟩) 2 (.word 0) allocatedMemory fullyInitialized :=
  .next rfl (.next rfl (.empty _ _ _))

theorem initialized_allocation_preserves_shared_graph :
    At fullyInitialized signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  allocation_initialization_preserves_term fresh_allocation initializes_both_cells shared_application_represented

theorem initialized_allocation_preserves_array_profile : ArrayBaseDiscipline.Memory fullyInitialized :=
  ArrayAllocation.zero_initialize_discipline allocation_preserves_array_profile
    (interface := ⟨[], [], [], []⟩) .word initializes_both_cells

end Mettapedia.Languages.VibeITP.Native.TermHeapAllocationControls
