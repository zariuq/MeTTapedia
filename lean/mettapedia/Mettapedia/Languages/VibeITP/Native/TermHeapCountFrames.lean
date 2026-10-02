import Mettapedia.Languages.VibeITP.Native.HeapCountReads
import Mettapedia.Languages.VibeITP.Native.TermHeap

/-!
# Count changes preserve the independent meaning of stored term graphs

The memory relation below records primitive reads and count-only record
updates. Both constructors are proved for the actual store operation. The
interpretation theorem follows the complete finite graph, retaining sharing
and ordered arrays. It does not justify deallocation or reference ownership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeap

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.GSLT.LanguageDef.NativeWord64 (Word)
open HeapCells

structure CountFrame (before after : SourceMemory) : Prop where
  termRead : ∀ (address : Address) (cell : TermCell), sourceRead before address = some cell.sourceValue →
    ∃ count, sourceRead after address = some ({ cell with references := count } : TermCell).sourceValue
  symbolRead : ∀ (address : Address) (cell : SymbolCell), sourceRead before address = some cell.sourceValue →
    ∃ count, sourceRead after address = some ({ cell with references := count } : SymbolCell).sourceValue
  wordRead : ∀ array : ArrayCell, array.Rooted → words after array = words before array
  referenceRead : ∀ array : ArrayCell, array.Rooted → references after array = references before array
  byteRead : ∀ array : ArrayCell, array.Rooted → literal after array = literal before array

theorem term_count_store_frame (memory : SourceMemory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue) :
    CountFrame memory (sourceStoreCell memory storage element { cell with references := count }.sourceValue) where
  termRead := term_count_store_term_read memory storage element cell count stored
  symbolRead := by
    intro address observed read
    exact ⟨observed.references, term_count_store_symbol_read memory storage element cell count stored
      address observed read⟩
  wordRead := fun array rooted => (term_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).1
  referenceRead := fun array rooted => (term_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).2.1
  byteRead := fun array rooted => (term_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).2.2

theorem symbol_count_store_frame (memory : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue) :
    CountFrame memory (sourceStoreCell memory storage element { cell with references := count }.sourceValue) where
  termRead := by
    intro address observed read
    exact ⟨observed.references, symbol_count_store_term_read memory storage element cell count stored
      address observed read⟩
  symbolRead := symbol_count_store_symbol_read memory storage element cell count stored
  wordRead := fun array rooted => (symbol_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).1
  referenceRead := fun array rooted => (symbol_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).2.1
  byteRead := fun array rooted => (symbol_count_store_preserves_root_arrays memory storage element
    cell count stored array rooted).2.2

theorem symbol_at_count_frame {before after : SourceMemory} (valid : ArrayBaseDiscipline.Memory before)
    (frame : CountFrame before after) {address : Address} {symbol : Spec.SymId} {info : Spec.SymInfo}
    (represented : SymbolHeap.At before address symbol info) : SymbolHeap.At after address symbol info := by
  obtain ⟨cell, read, kind, arity, binders, digits, identity, meaning⟩ := represented
  obtain ⟨count, updated⟩ := frame.symbolRead address cell read
  have rooted := symbol_arrays_from_memory valid read
  exact ⟨{ cell with references := count }, updated, kind, arity,
    (frame.wordRead cell.binders rooted.1).trans binders, digits,
    (frame.wordRead cell.identity rooted.2).trans identity, meaning⟩

theorem count_frame {before after : SourceMemory} (valid : ArrayBaseDiscipline.Memory before)
    (frame : CountFrame before after) {signature : Spec.Sig} {markers : Markers}
    {address : Address} {term : Spec.Term} (represented : At before signature markers address term) :
    At after signature markers address term := by
  refine At.rec (motive_1 := fun address term _ => At after signature markers address term)
    (motive_2 := fun addresses terms _ => ListAt after signature markers addresses terms)
    ?_ ?_ ?_ ?_ ?_ represented
  · intro address cell marker stored symbol markerStored kind depth free noLiteral noArguments
    obtain ⟨count, updated⟩ := frame.termRead address cell stored
    obtain ⟨markerCount, updatedMarker⟩ := frame.symbolRead markers.boundVariable marker markerStored
    exact .bvar (cell := { cell with references := count })
      (marker := { marker with references := markerCount }) updated symbol updatedMarker kind
      depth free noLiteral noArguments
  · intro address cell marker bytes stored symbol markerStored kind contents bounded depth free noArguments
    obtain ⟨count, updated⟩ := frame.termRead address cell stored
    obtain ⟨markerCount, updatedMarker⟩ := frame.symbolRead markers.literal marker markerStored
    have rooted := term_arrays_from_memory valid stored
    exact .lit (cell := { cell with references := count })
      (marker := { marker with references := markerCount }) updated symbol updatedMarker kind
      ((frame.byteRead cell.literal rooted.1).trans contents) bounded depth free noArguments
  · intro address symbolAddress cell symbol info addresses terms stored head symbolStored declared
      contents children arity depth free noLiteral representedChildren
    obtain ⟨count, updated⟩ := frame.termRead address cell stored
    have rooted := term_arrays_from_memory valid stored
    exact .app (cell := { cell with references := count }) updated head
      (symbol_at_count_frame valid frame symbolStored) declared
      ((frame.referenceRead cell.arguments rooted.2).trans contents)
      representedChildren arity depth free noLiteral
  · exact .nil
  · intro address term addresses terms head tail representedHead representedTail
    exact .cons representedHead representedTail

theorem term_count_store_preserves_meaning {memory : SourceMemory}
    (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat) (cell : TermCell) (count : Word)
    (stored : memory.cells storage element = some cell.sourceValue)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) :
    At (sourceStoreCell memory storage element { cell with references := count }.sourceValue)
      signature markers address term :=
  count_frame valid (term_count_store_frame memory storage element cell count stored) represented

theorem symbol_count_store_preserves_meaning {memory : SourceMemory}
    (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat) (cell : SymbolCell) (count : Word)
    (stored : memory.cells storage element = some cell.sourceValue)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) :
    At (sourceStoreCell memory storage element { cell with references := count }.sourceValue)
      signature markers address term :=
  count_frame valid (symbol_count_store_frame memory storage element cell count stored) represented

theorem term_count_write_preserves_meaning {memory after : SourceMemory}
    (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat) (cell : TermCell) (count : Word)
    (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [6]⟩ (.word count) = some after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) : At after signature markers address term := by
  have same := Option.some.inj ((term_reference_write memory storage element cell count stored).symm.trans written)
  cases same
  exact term_count_store_preserves_meaning valid storage element cell count stored represented

theorem symbol_count_write_preserves_meaning {memory after : SourceMemory}
    (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat) (cell : SymbolCell) (count : Word)
    (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [4]⟩ (.word count) = some after)
    {signature : Spec.Sig} {markers : Markers} {address : Address} {term : Spec.Term}
    (represented : At memory signature markers address term) : At after signature markers address term := by
  have same := Option.some.inj ((symbol_reference_write memory storage element cell count stored).symm.trans written)
  cases same
  exact symbol_count_store_preserves_meaning valid storage element cell count stored represented

end Mettapedia.Languages.VibeITP.Native.TermHeap
