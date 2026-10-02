import Mettapedia.Languages.VibeITP.Native.TermHeapCountFrames
import Mettapedia.Languages.VibeITP.Native.TermHeapAllocation

/-!
# Independent target-memory effects preserve represented Vibe terms

Target writes and allocations are the separately defined operational effects.
Their backward correspondence constructs source post-memory before applying
the term-meaning laws. This boundary concerns the admitted IR memory model;
physical pointers and ABI execution require their own realization relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeSystemAllocation
open NativeWord64 (Word encode)
open HeapCells

theorem target_term_count_write_preserves_meaning {source : SourceMemory} {target after : TargetMemory}
    (related : MemoryRelated source target) (valid : ArrayBaseDiscipline.Memory source)
    (storage element : Nat) (cell : TermCell) (count : Word)
    (stored : source.cells storage element = some cell.sourceValue)
    (written : targetWrite target ⟨storage, element, [6]⟩ (.word (encode count)) = some after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At source signature markers address term) :
    ∃ sourceAfter, sourceWrite source ⟨storage, element, [6]⟩ (.word count) = some sourceAfter ∧
      MemoryRelated sourceAfter after ∧ ArrayBaseDiscipline.Memory sourceAfter ∧
      At sourceAfter signature markers address term := by
  obtain ⟨sourceAfter, wrote, states⟩ := memory_write_backward source target related
    ⟨storage, element, [6]⟩ (.word count) after written
  exact ⟨sourceAfter, wrote, states, reference_count_write_keeps_array_discipline valid _ count wrote,
    term_count_write_preserves_meaning valid storage element cell count stored wrote represented⟩

theorem target_symbol_count_write_preserves_meaning {source : SourceMemory} {target after : TargetMemory}
    (related : MemoryRelated source target) (valid : ArrayBaseDiscipline.Memory source)
    (storage element : Nat) (cell : SymbolCell) (count : Word)
    (stored : source.cells storage element = some cell.sourceValue)
    (written : targetWrite target ⟨storage, element, [4]⟩ (.word (encode count)) = some after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At source signature markers address term) :
    ∃ sourceAfter, sourceWrite source ⟨storage, element, [4]⟩ (.word count) = some sourceAfter ∧
      MemoryRelated sourceAfter after ∧ ArrayBaseDiscipline.Memory sourceAfter ∧
      At sourceAfter signature markers address term := by
  obtain ⟨sourceAfter, wrote, states⟩ := memory_write_backward source target related
    ⟨storage, element, [4]⟩ (.word count) after written
  exact ⟨sourceAfter, wrote, states, reference_count_write_keeps_array_discipline valid _ count wrote,
    symbol_count_write_preserves_meaning valid storage element cell count stored wrote represented⟩

theorem target_allocation_preserves_meaning {source : SourceMemory} {target after : TargetMemory}
    (related : MemoryRelated source target) (valid : ArrayBaseDiscipline.Memory source)
    (extent : Word) (initial : Nat → Option SourceValue)
    (initialValid : ∀ index value, initial index = some value → ArrayBaseDiscipline.value value = true)
    (pointer : Option Address)
    (allocated : TargetMalloc (encode extent) (fun index => (initial index).map encodeValue)
      target pointer after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At source signature markers address term) :
    ∃ sourceAfter, SourceMalloc extent initial source pointer sourceAfter ∧
      MemoryRelated sourceAfter after ∧ ArrayBaseDiscipline.Memory sourceAfter ∧
      At sourceAfter signature markers address term := by
  obtain ⟨sourceAfter, allocation, states⟩ := malloc_backward source target related extent initial pointer after allocated
  exact ⟨sourceAfter, allocation, states, ArrayAllocation.malloc_discipline valid initialValid allocation,
    allocation_preserves_term allocation represented⟩

end Mettapedia.Languages.VibeITP.Native.TermHeap
