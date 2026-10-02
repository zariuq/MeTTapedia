import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryExtension
import Mettapedia.Languages.VibeITP.Native.TermHeap

/-! Filling absent cells preserves existing symbol and term interpretations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

theorem symbol_meaning_extension {before after : SourceMemory}
    (preserves : MemoryExtension.Extends before after) {cell : SymbolCell}
    {symbol : Spec.SymId} {info : Spec.SymInfo}
    (meaning : SymbolHeap.Meaning before cell symbol info) :
    SymbolHeap.Meaning after cell symbol info := by
  rcases meaning with ⟨kind, arity, binders, digits, identity, value⟩
  exact ⟨kind, arity, MemoryExtension.typed_view .word _ preserves _ _ binders,
    digits, MemoryExtension.typed_view .word _ preserves _ _ identity, value⟩

theorem symbol_at_extension {before after : SourceMemory}
    (preserves : MemoryExtension.Extends before after) {address : Address}
    {symbol : Spec.SymId} {info : Spec.SymInfo}
    (represented : SymbolHeap.At before address symbol info) : SymbolHeap.At after address symbol info := by
  obtain ⟨cell, read, meaning⟩ := represented
  exact ⟨cell, MemoryExtension.successful_read preserves read, symbol_meaning_extension preserves meaning⟩

theorem extension {before after : SourceMemory} (preserves : MemoryExtension.Extends before after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At before signature markers address term) : At after signature markers address term := by
  refine At.rec (motive_1 := fun address term _ => At after signature markers address term)
    (motive_2 := fun addresses terms _ => ListAt after signature markers addresses terms)
    ?_ ?_ ?_ ?_ ?_ represented
  · intro address cell marker stored symbol markerStored kind depth free noLiteral noArguments
    exact .bvar (MemoryExtension.successful_read preserves stored) symbol
      (MemoryExtension.successful_read preserves markerStored) kind depth free noLiteral noArguments
  · intro address cell marker bytes stored symbol markerStored kind contents bounded depth free noArguments
    exact .lit (MemoryExtension.successful_read preserves stored) symbol
      (MemoryExtension.successful_read preserves markerStored) kind
      (MemoryExtension.byte_view preserves _ _ _ contents) bounded depth free noArguments
  · intro address symbolAddress cell symbol info addresses terms stored head symbolStored declared
      contents children arity depth free noLiteral representedChildren
    exact .app (MemoryExtension.successful_read preserves stored) head
      (symbol_at_extension preserves symbolStored) declared
      (MemoryExtension.typed_view (.ref (.named "Term")) _ preserves _ _ contents)
      representedChildren arity depth free noLiteral
  · exact .nil
  · intro address term addresses terms head tail representedHead representedTail
    exact .cons representedHead representedTail

theorem fresh_store_preserves_term {memory : SourceMemory} {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At memory signature markers address term)
    (storage element : Nat) (value : SourceValue) (fresh : memory.cells storage element = none) :
    At (sourceStoreCell memory storage element value) signature markers address term :=
  extension (MemoryExtension.fresh_cell_store memory storage element value fresh) represented

end Mettapedia.Languages.VibeITP.Native.TermHeap
