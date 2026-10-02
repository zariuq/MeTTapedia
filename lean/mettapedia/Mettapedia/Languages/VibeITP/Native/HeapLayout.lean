import Mettapedia.Languages.VibeITP.Native.HeapCells
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceGuestSnapshot
import Mettapedia.GSLT.LanguageDef.NativeOpsFieldLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarProfiles

/-!
# Stored Vibe cells against the admitted operational record declarations

The field names, order and types below are checked against the actual admitted
guest interface. Content-view laws alone do not establish physical C layout
or preservation by the generated function bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapLayout

open Mettapedia.GSLT.LanguageDef
open NativeOps HeapCells

def symbolFields : List Parameter :=
  [⟨"kind", .word⟩, ⟨"arity", .word⟩, ⟨"binders", .array .word⟩,
   ⟨"identity", .array .word⟩, ⟨"rc", .word⟩, ⟨"immortal", .bool⟩]

def termFields : List Parameter :=
  [⟨"symbol", .ref (.named "Symbol")⟩, ⟨"number", .word⟩, ⟨"literal", .array .byte⟩,
   ⟨"args", .array (.ref (.named "Term"))⟩, ⟨"depth", .word⟩,
   ⟨"has-fvar", .bool⟩, ⟨"rc", .word⟩]

theorem actual_symbol_declaration :
    lookupRecord NativeOpsSourceGuestSnapshot.expectedProgram.interface "Symbol" =
      some ⟨"Symbol", symbolFields⟩ := by
  decide +kernel

theorem actual_term_declaration :
    lookupRecord NativeOpsSourceGuestSnapshot.expectedProgram.interface "Term" =
      some ⟨"Term", termFields⟩ := by
  decide +kernel

theorem actual_symbol_positions :
    (symbolFields.map Parameter.name).map
      (sourceFieldIndex? NativeOpsSourceGuestSnapshot.expectedProgram.interface "Symbol") =
      [some 0, some 1, some 2, some 3, some 4, some 5] := by
  decide +kernel

theorem actual_term_positions :
    (termFields.map Parameter.name).map
      (sourceFieldIndex? NativeOpsSourceGuestSnapshot.expectedProgram.interface "Term") =
      [some 0, some 1, some 2, some 3, some 4, some 5, some 6] := by
  decide +kernel

theorem actual_symbol_reference_slot :
    NativeLowering.fieldLayout? NativeOpsSourceGuestSnapshot.expectedProgram.interface "Symbol" "rc" =
      some 4 := by
  rw [field_layout_correspondence]
  decide +kernel

theorem actual_term_reference_slot :
    NativeLowering.fieldLayout? NativeOpsSourceGuestSnapshot.expectedProgram.interface "Term" "rc" =
      some 6 := by
  rw [field_layout_correspondence]
  decide +kernel

theorem symbol_cell_fields_tagged (cell : SymbolCell) :
    ∃ fields, cell.sourceValue = .record "Symbol" fields ∧
      List.Forall₂ (fun field value => SourceOuterTag field.type value) symbolFields fields := by
  refine ⟨_, rfl, ?_⟩
  repeat' constructor

theorem term_cell_fields_tagged (cell : TermCell) :
    ∃ fields, cell.sourceValue = .record "Term" fields ∧
      List.Forall₂ (fun field value => SourceOuterTag field.type value) termFields fields := by
  refine ⟨_, rfl, ?_⟩
  repeat' constructor

theorem unknown_symbol_field_refused :
    sourceFieldIndex? NativeOpsSourceGuestSnapshot.expectedProgram.interface "Symbol" "missing" = none := by
  decide +kernel

theorem term_reference_slot_is_not_symbol_reference_slot : (6 : Nat) ≠ 4 := by decide

end Mettapedia.Languages.VibeITP.Native.HeapLayout
