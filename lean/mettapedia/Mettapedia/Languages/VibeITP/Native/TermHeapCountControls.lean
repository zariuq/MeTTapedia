import Mettapedia.Languages.VibeITP.Native.TermHeapCountFrames
import Mettapedia.Languages.VibeITP.Native.HeapArrayDisciplineControls

/-! Shared nodes and bytes distinguish count updates from semantic mutation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeapCountControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells TermHeap TermHeapControls

theorem root_count_write_preserves_shared_application :
    At HeapAliasControls.ordinaryAfter signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  term_count_write_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
    101 0 rootCell 2 rfl HeapAliasControls.ordinary_reference_count_write shared_application_represented

def childCountAfter : SourceMemory :=
  sourceStoreCell memory 100 0 { childCell with references := 3 }.sourceValue

theorem child_count_write : sourceWrite memory ⟨100, 0, [6]⟩ (.word 3) = some childCountAfter := rfl

theorem shared_child_count_write_preserves_both_occurrences :
    At childCountAfter signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  term_count_write_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
    100 0 childCell 3 rfl child_count_write shared_application_represented

theorem count_write_preserves_literal_bytes :
    At childCountAfter signature markers literalAddress (.lit [65, 66]) :=
  term_count_write_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
    100 0 childCell 3 rfl child_count_write literal_represented

theorem symbol_zero_count_store_preserves_contents :
    At (sourceStoreCell memory 10 0 { symbolCell with references := 0 }.sourceValue)
      signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  symbol_count_store_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
    10 0 symbolCell 0 rfl shared_application_represented

theorem marker_count_store_preserves_bound_variables :
    At (sourceStoreCell memory 1 0 { boundMarker with references := 9 }.sourceValue)
      signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) :=
  symbol_count_store_preserves_meaning HeapArrayDisciplineControls.ordinary_memory_has_discipline
    1 0 boundMarker 9 rfl shared_application_represented

def byteChanged : SourceMemory := sourceStoreCell memory 50 0 (.byte 67)

theorem literal_byte_write : sourceWrite memory ⟨50, 0, []⟩ (.byte 67) = some byteChanged := rfl

theorem literal_byte_write_keeps_array_discipline : ArrayBaseDiscipline.Memory byteChanged :=
  ArrayBaseDiscipline.write HeapArrayDisciplineControls.ordinary_memory_has_discipline _ _ rfl literal_byte_write

theorem literal_byte_write_changes_meaning : ¬ At byteChanged signature markers literalAddress (.lit [65, 66]) := by
  intro represented
  cases represented with
  | lit stored _ _ _ contents _ _ _ _ =>
    have cells := term_cell_unique byteChanged literalAddress _ literalCell stored rfl
    cases cells
    have different : literal byteChanged literalCell.literal ≠ some ([65, 66] : List UInt8) := by decide +kernel
    exact different contents

theorem forged_heap_has_primitive_frame_but_fails_array_profile :
    CountFrame HeapAliasControls.memory HeapAliasControls.after ∧
    ¬ ArrayBaseDiscipline.Memory HeapAliasControls.memory :=
  ⟨term_count_store_frame HeapAliasControls.memory 40 0 HeapAliasControls.term 2 rfl,
    HeapArrayDisciplineControls.forged_alias_memory_fails_discipline⟩

end Mettapedia.Languages.VibeITP.Native.TermHeapCountControls
