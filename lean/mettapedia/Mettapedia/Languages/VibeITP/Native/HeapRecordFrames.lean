import Mettapedia.GSLT.LanguageDef.NativeOpsRecordScalarFrame
import Mettapedia.Languages.VibeITP.Native.HeapCells

/-!
# Reference-count writes preserve scalar arrays with root addresses

The address discipline is explicit. Establishing it for reached guest states
remains a separate obligation; allocation counts alone do not establish it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapCells

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.GSLT.LanguageDef.NativeWord64 (Word)

def ArrayCell.Rooted (cell : ArrayCell) : Prop :=
  ∀ base, cell.address = some base → base.fields = []

theorem record_store_preserves_root_arrays (memory : SourceMemory) (storage element : Nat)
    (name : String) (before after : List SourceValue)
    (stored : memory.cells storage element = some (.record name before))
    (array : ArrayCell) (rooted : array.Rooted) :
    words (sourceStoreCell memory storage element (.record name after)) array = words memory array ∧
    references (sourceStoreCell memory storage element (.record name after)) array = references memory array ∧
    literal (sourceStoreCell memory storage element (.record name after)) array = literal memory array :=
  ⟨RecordScalarFrame.word_view memory storage element name before after stored _ _ rooted,
   RecordScalarFrame.reference_view (.named "Term") memory storage element name before after stored _ _ rooted,
   RecordScalarFrame.byte_view memory storage element name before after stored _ _ rooted⟩

theorem term_count_store_preserves_root_arrays (memory : SourceMemory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (array : ArrayCell) (rooted : array.Rooted) :
    let after := sourceStoreCell memory storage element { cell with references := count }.sourceValue
    words after array = words memory array ∧ references after array = references memory array ∧
      literal after array = literal memory array :=
  record_store_preserves_root_arrays memory storage element "Term" _ _ stored array rooted

theorem symbol_count_store_preserves_root_arrays (memory : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (array : ArrayCell) (rooted : array.Rooted) :
    let after := sourceStoreCell memory storage element { cell with references := count }.sourceValue
    words after array = words memory array ∧ references after array = references memory array ∧
      literal after array = literal memory array :=
  record_store_preserves_root_arrays memory storage element "Symbol" _ _ stored array rooted

theorem term_count_write_preserves_root_arrays (memory after : SourceMemory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [6]⟩ (.word count) = some after)
    (array : ArrayCell) (rooted : array.Rooted) :
    words after array = words memory array ∧ references after array = references memory array ∧
      literal after array = literal memory array := by
  have same := Option.some.inj ((term_reference_write memory storage element cell count stored).symm.trans written)
  cases same
  exact term_count_store_preserves_root_arrays memory storage element cell count stored array rooted

theorem symbol_count_write_preserves_root_arrays (memory after : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [4]⟩ (.word count) = some after)
    (array : ArrayCell) (rooted : array.Rooted) :
    words after array = words memory array ∧ references after array = references memory array ∧
      literal after array = literal memory array := by
  have same := Option.some.inj ((symbol_reference_write memory storage element cell count stored).symm.trans written)
  cases same
  exact symbol_count_store_preserves_root_arrays memory storage element cell count stored array rooted

end Mettapedia.Languages.VibeITP.Native.HeapCells
