import Mettapedia.GSLT.LanguageDef.NativeOpsArrayBaseDiscipline
import Mettapedia.Languages.VibeITP.Native.HeapRecordFrames

/-! Extract array-base discipline from actual stored guest cells. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapCells

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.GSLT.LanguageDef.NativeWord64 (Word)

theorem array_value_discipline_iff (cell : ArrayCell) (element : NativeType) :
    ArrayBaseDiscipline.value (cell.sourceValue element) = true ↔ cell.Rooted := by
  cases cell with
  | mk address length =>
    cases address with
    | none =>
        constructor
        · intro _ base impossible; cases impossible
        · intro _; rfl
    | some address =>
        constructor
        · intro valid base same
          cases same
          exact ArrayBaseDiscipline.array_base valid
        · intro valid
          have empty := valid address rfl
          change address.fields.isEmpty = true
          rw [empty]
          rfl

theorem symbol_value_discipline_iff (cell : SymbolCell) :
    ArrayBaseDiscipline.value cell.sourceValue = true ↔ cell.binders.Rooted ∧ cell.identity.Rooted := by
  simp only [SymbolCell.sourceValue, ArrayBaseDiscipline.value, ArrayBaseDiscipline.fields,
    Bool.and_eq_true, true_and, and_true, array_value_discipline_iff]

theorem term_value_discipline_iff (cell : TermCell) :
    ArrayBaseDiscipline.value cell.sourceValue = true ↔ cell.literal.Rooted ∧ cell.arguments.Rooted := by
  simp only [TermCell.sourceValue, ArrayBaseDiscipline.value, ArrayBaseDiscipline.fields,
    Bool.and_eq_true, true_and, and_true, array_value_discipline_iff]

theorem symbol_arrays_from_memory {memory : SourceMemory} (valid : ArrayBaseDiscipline.Memory memory)
    {address : Address} {cell : SymbolCell} (stored : sourceRead memory address = some cell.sourceValue) :
    cell.binders.Rooted ∧ cell.identity.Rooted :=
  (symbol_value_discipline_iff cell).mp (ArrayBaseDiscipline.read valid stored)

theorem term_arrays_from_memory {memory : SourceMemory} (valid : ArrayBaseDiscipline.Memory memory)
    {address : Address} {cell : TermCell} (stored : sourceRead memory address = some cell.sourceValue) :
    cell.literal.Rooted ∧ cell.arguments.Rooted :=
  (term_value_discipline_iff cell).mp (ArrayBaseDiscipline.read valid stored)

theorem reference_count_write_keeps_array_discipline {memory after : SourceMemory}
    (valid : ArrayBaseDiscipline.Memory memory) (address : Address) (count : Word)
    (written : sourceWrite memory address (.word count) = some after) : ArrayBaseDiscipline.Memory after :=
  ArrayBaseDiscipline.write valid address (.word count) rfl written

theorem term_reference_write_preserves_stored_symbol_arrays
    (memory after : SourceMemory) (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [6]⟩ (.word count) = some after)
    (symbolAddress : Address) (symbol : SymbolCell)
    (read : sourceRead memory symbolAddress = some symbol.sourceValue) :
    words after symbol.binders = words memory symbol.binders ∧
    words after symbol.identity = words memory symbol.identity := by
  have roots := symbol_arrays_from_memory valid read
  exact ⟨(term_count_write_preserves_root_arrays memory after storage element cell count stored written
      symbol.binders roots.1).1,
    (term_count_write_preserves_root_arrays memory after storage element cell count stored written
      symbol.identity roots.2).1⟩

theorem symbol_reference_write_preserves_stored_term_arrays
    (memory after : SourceMemory) (valid : ArrayBaseDiscipline.Memory memory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (written : sourceWrite memory ⟨storage, element, [4]⟩ (.word count) = some after)
    (termAddress : Address) (term : TermCell)
    (read : sourceRead memory termAddress = some term.sourceValue) :
    literal after term.literal = literal memory term.literal ∧
    references after term.arguments = references memory term.arguments := by
  have roots := term_arrays_from_memory valid read
  exact ⟨(symbol_count_write_preserves_root_arrays memory after storage element cell count stored written
      term.literal roots.1).2.2,
    (symbol_count_write_preserves_root_arrays memory after storage element cell count stored written
      term.arguments roots.2).2.1⟩

end Mettapedia.Languages.VibeITP.Native.HeapCells
