import Mettapedia.GSLT.LanguageDef.NativeOpsArrayAllocation
import Mettapedia.Languages.VibeITP.Native.TermHeapExtension

/-! System allocation preserves previously represented symbols and term graphs. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeSystemAllocation

theorem allocation_preserves_term {memory after : SourceMemory}
    {extent : NativeWord64.Word} {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial memory pointer after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) : At after signature markers address term :=
  extension (ArrayAllocation.malloc_extends allocated) represented

theorem allocation_preserves_symbol {memory after : SourceMemory}
    {extent : NativeWord64.Word} {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial memory pointer after)
    {address : Address} {symbol : Spec.SymId} {info : Spec.SymInfo}
    (represented : SymbolHeap.At memory address symbol info) : SymbolHeap.At after address symbol info :=
  symbol_at_extension (ArrayAllocation.malloc_extends allocated) represented

theorem represented_term_avoids_new_storage {memory after : SourceMemory}
    {extent : NativeWord64.Word} {initial : Nat → Option SourceValue} {pointer : Address}
    (allocated : SourceMalloc extent initial memory (some pointer) after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) : address.storage ≠ pointer.storage := by
  obtain ⟨cell, read, _, _⟩ := stored_cache represented
  exact source_success_avoids_live_read extent initial memory after pointer address cell.sourceValue allocated read

theorem allocation_initialization_preserves_term {memory allocatedMemory after : SourceMemory}
    {extent : NativeWord64.Word} {initial : Nat → Option SourceValue} {pointer : Option Address}
    (allocated : SourceMalloc extent initial memory pointer allocatedMemory)
    {count : Nat} {value : SourceValue}
    (initialized : SourceInitialize pointer count value allocatedMemory after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) : At after signature markers address term :=
  extension (ArrayAllocation.malloc_initialize_extends allocated initialized) represented

end Mettapedia.Languages.VibeITP.Native.TermHeap
