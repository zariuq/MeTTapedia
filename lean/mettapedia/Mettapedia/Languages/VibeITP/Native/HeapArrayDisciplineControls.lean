import Mettapedia.Languages.VibeITP.Native.HeapArrayDiscipline
import Mettapedia.Languages.VibeITP.Native.HeapAliasControls

/-! Concrete array-base profiles and their content/ownership limits. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapArrayDisciplineControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

theorem ordinary_memory_has_discipline : ArrayBaseDiscipline.Memory TermHeapControls.memory := by
  intro storage element contents stored
  have valid : (TermHeapControls.memory.cells storage element).all ArrayBaseDiscipline.value = true := by
    unfold TermHeapControls.memory
    dsimp only
    repeat first | split | rfl
  simpa only [stored, Option.all_some] using valid

theorem ordinary_count_write_preserves_discipline :
    ArrayBaseDiscipline.Memory HeapAliasControls.ordinaryAfter :=
  reference_count_write_keeps_array_discipline ordinary_memory_has_discipline ⟨101, 0, [6]⟩ 2
    HeapAliasControls.ordinary_reference_count_write

theorem binder_preservation_from_memory_discipline :
    words HeapAliasControls.ordinaryAfter TermHeapControls.symbolCell.binders = some [0, 0] ∧
    words HeapAliasControls.ordinaryAfter TermHeapControls.symbolCell.identity = some [13] :=
  term_reference_write_preserves_stored_symbol_arrays
    TermHeapControls.memory HeapAliasControls.ordinaryAfter ordinary_memory_has_discipline 101 0
    TermHeapControls.rootCell 2 rfl HeapAliasControls.ordinary_reference_count_write
    TermHeapControls.symbolAddress TermHeapControls.symbolCell rfl

theorem forged_alias_memory_fails_discipline : ¬ ArrayBaseDiscipline.Memory HeapAliasControls.memory := by
  intro valid
  have rooted := symbol_arrays_from_memory valid
    (show sourceRead HeapAliasControls.memory HeapAliasControls.symbolAddress =
      some HeapAliasControls.symbol.sourceValue from rfl)
  exact HeapAliasControls.forged_binder_does_not_meet_address_discipline rooted.1

theorem discipline_does_not_supply_missing_contents :
    ArrayBaseDiscipline.value (.array .word none 1) = true ∧
    words ⟨fun _ _ => none, fun _ => none⟩ ⟨none, 1⟩ = none := ⟨rfl, rfl⟩

end Mettapedia.Languages.VibeITP.Native.HeapArrayDisciplineControls
