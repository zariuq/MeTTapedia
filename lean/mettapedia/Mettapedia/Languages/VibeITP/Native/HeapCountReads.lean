import Mettapedia.GSLT.LanguageDef.NativeOpsShallowRecordReads
import Mettapedia.Languages.VibeITP.Native.HeapArrayDiscipline

/-! Actual count stores preserve semantic record fields at every readable address. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapCells

open Mettapedia.GSLT.LanguageDef.NativeOps
open Mettapedia.GSLT.LanguageDef.NativeWord64 (Word)

theorem term_record_read_path_empty (cell : TermCell) (path : List Nat)
    (name : String) (fields : List SourceValue)
    (read : sourceReadPath path cell.sourceValue = some (.record name fields)) : path = [] := by
  apply ShallowRecordReads.record_path_is_root "Term" _ ?_ path name fields read
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem symbol_record_read_path_empty (cell : SymbolCell) (path : List Nat)
    (name : String) (fields : List SourceValue)
    (read : sourceReadPath path cell.sourceValue = some (.record name fields)) : path = [] := by
  apply ShallowRecordReads.record_path_is_root "Symbol" _ ?_ path name fields read
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem term_count_store_term_read (memory : SourceMemory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (address : Address) (observed : TermCell)
    (read : sourceRead memory address = some observed.sourceValue) :
    ∃ actualCount, sourceRead (sourceStoreCell memory storage element
      { cell with references := count }.sourceValue) address =
        some { observed with references := actualCount }.sourceValue := by
  by_cases same : address.storage = storage ∧ address.element = element
  · have pathRead : sourceReadPath address.fields cell.sourceValue = some observed.sourceValue := by
      simpa only [sourceRead, same.1, same.2, stored, Option.bind_some] using read
    have empty := term_record_read_path_empty cell address.fields "Term" _ pathRead
    have cells : cell = observed := term_cell_injective (Option.some.inj
      (by simpa only [empty, sourceReadPath] using pathRead))
    cases cells
    exact ⟨count, by simp only [sourceRead, sourceStoreCell, same.1, same.2,
      and_self, if_true, empty, Option.bind_some, sourceReadPath]⟩
  · exact ⟨observed.references, by
      rw [ShallowRecordReads.read_store_other memory storage element _ address same]
      exact read⟩

theorem term_count_store_symbol_read (memory : SourceMemory) (storage element : Nat)
    (cell : TermCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (address : Address) (observed : SymbolCell)
    (read : sourceRead memory address = some observed.sourceValue) :
    sourceRead (sourceStoreCell memory storage element
      { cell with references := count }.sourceValue) address = some observed.sourceValue := by
  by_cases same : address.storage = storage ∧ address.element = element
  · have pathRead : sourceReadPath address.fields cell.sourceValue = some observed.sourceValue := by
      simpa only [sourceRead, same.1, same.2, stored, Option.bind_some] using read
    have empty := term_record_read_path_empty cell address.fields "Symbol" _ pathRead
    simp only [empty, sourceReadPath, Option.some.injEq, TermCell.sourceValue,
      SymbolCell.sourceValue, SourceValue.record.injEq] at pathRead
    exact False.elim ((by decide : ("Term" : String) ≠ "Symbol") pathRead.1)
  · rw [ShallowRecordReads.read_store_other memory storage element _ address same]
    exact read

theorem symbol_count_store_symbol_read (memory : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (address : Address) (observed : SymbolCell)
    (read : sourceRead memory address = some observed.sourceValue) :
    ∃ actualCount, sourceRead (sourceStoreCell memory storage element
      { cell with references := count }.sourceValue) address =
        some { observed with references := actualCount }.sourceValue := by
  by_cases same : address.storage = storage ∧ address.element = element
  · have pathRead : sourceReadPath address.fields cell.sourceValue = some observed.sourceValue := by
      simpa only [sourceRead, same.1, same.2, stored, Option.bind_some] using read
    have empty := symbol_record_read_path_empty cell address.fields "Symbol" _ pathRead
    have cells : cell = observed := symbol_cell_injective (Option.some.inj
      (by simpa only [empty, sourceReadPath] using pathRead))
    cases cells
    exact ⟨count, by simp only [sourceRead, sourceStoreCell, same.1, same.2,
      and_self, if_true, empty, Option.bind_some, sourceReadPath]⟩
  · exact ⟨observed.references, by
      rw [ShallowRecordReads.read_store_other memory storage element _ address same]
      exact read⟩

theorem symbol_count_store_term_read (memory : SourceMemory) (storage element : Nat)
    (cell : SymbolCell) (count : Word) (stored : memory.cells storage element = some cell.sourceValue)
    (address : Address) (observed : TermCell)
    (read : sourceRead memory address = some observed.sourceValue) :
    sourceRead (sourceStoreCell memory storage element
      { cell with references := count }.sourceValue) address = some observed.sourceValue := by
  by_cases same : address.storage = storage ∧ address.element = element
  · have pathRead : sourceReadPath address.fields cell.sourceValue = some observed.sourceValue := by
      simpa only [sourceRead, same.1, same.2, stored, Option.bind_some] using read
    have empty := symbol_record_read_path_empty cell address.fields "Term" _ pathRead
    simp only [empty, sourceReadPath, Option.some.injEq, TermCell.sourceValue,
      SymbolCell.sourceValue, SourceValue.record.injEq] at pathRead
    exact False.elim ((by decide : ("Symbol" : String) ≠ "Term") pathRead.1)
  · rw [ShallowRecordReads.read_store_other memory storage element _ address same]
    exact read

end Mettapedia.Languages.VibeITP.Native.HeapCells
