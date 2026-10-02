import Mettapedia.Languages.VibeITP.Native.SymbolHeap
import Mettapedia.Languages.VibeITP.Native.HeapLayout

/-! Stored-symbol examples and limits of the content representation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells SymbolHeap

def symbolAddress : Address := ⟨10, 0, []⟩
def binderAddress : Address := ⟨20, 0, []⟩
def identityAddress : Address := ⟨30, 0, []⟩

def sampleCell : SymbolCell :=
  ⟨1, 1, ⟨some binderAddress, 1⟩, ⟨some identityAddress, 1⟩, 1, false⟩

def sampleMemory : SourceMemory :=
  ⟨fun storage element =>
      if element ≠ 0 then none else
      if storage = 10 then some sampleCell.sourceValue else
      if storage = 20 then some (.word 0) else
      if storage = 30 then some (.word 13) else none,
    fun _ => none⟩

theorem stored_fvar_meaning : Meaning sampleMemory sampleCell (.fresh 0) (Spec.SymInfo.fvarOf 1) := by
  refine ⟨rfl, rfl, rfl, [13], rfl, ?_⟩
  rfl

theorem stored_fvar_at : At sampleMemory symbolAddress (.fresh 0) (Spec.SymInfo.fvarOf 1) :=
  ⟨sampleCell, rfl, stored_fvar_meaning⟩

theorem wrong_identity_rejected : ¬ At sampleMemory symbolAddress (.fresh 1) (Spec.SymInfo.fvarOf 1) :=
  different_symbols_cannot_share_live_representation sampleMemory symbolAddress
    (.fresh 0) (.fresh 1) (Spec.SymInfo.fvarOf 1) (Spec.SymInfo.fvarOf 1)
    (by decide) stored_fvar_at

theorem wrong_signature_rejected : ¬ At sampleMemory symbolAddress (.fresh 0) (Spec.SymInfo.fvarOf 2) := by
  intro other
  have same := (at_unique sampleMemory symbolAddress (.fresh 0) (.fresh 0)
    (Spec.SymInfo.fvarOf 1) (Spec.SymInfo.fvarOf 2) stored_fvar_at other).2
  have lengths := congrArg (fun info => info.binders.length) same
  contradiction

theorem contents_do_not_grant_ownership :
    At sampleMemory symbolAddress (.fresh 0) (Spec.SymInfo.fvarOf 1) ∧
      sampleMemory.owned symbolAddress.storage = none :=
  ⟨stored_fvar_at, rfl⟩

def wideCell : SymbolCell :=
  ⟨0, 0, ⟨none, 0⟩, ⟨some identityAddress, 2⟩, 1, false⟩

def wideMemory : SourceMemory :=
  ⟨fun storage element =>
      if storage = 10 ∧ element = 0 then some wideCell.sourceValue else
      if storage = 30 ∧ element = 0 then some (.word 0) else
      if storage = 30 ∧ element = 1 then some (.word 1) else none,
    fun _ => none⟩

theorem identity_above_one_word_is_retained :
    At wideMemory symbolAddress (.fresh (2 ^ 64 - 13)) ⟨.constant, []⟩ := by
  refine ⟨wideCell, rfl, rfl, rfl, rfl, [0, 1], rfl, ?_⟩
  change 0 + 2 ^ 64 * (1 + 2 ^ 64 * 0) = 13 + (2 ^ 64 - 13)
  decide +kernel

def copiedMemory : SourceMemory :=
  ⟨fun storage element =>
      if storage = 11 ∧ element = 0 then some sampleCell.sourceValue
      else sampleMemory.cells storage element,
    fun _ => none⟩

theorem copied_identity_has_same_content_meaning :
    At copiedMemory symbolAddress (.fresh 0) (Spec.SymInfo.fvarOf 1) ∧
    At copiedMemory ⟨11, 0, []⟩ (.fresh 0) (Spec.SymInfo.fvarOf 1) ∧
    symbolAddress ≠ ⟨11, 0, []⟩ := by
  have meaning : Meaning copiedMemory sampleCell (.fresh 0) (Spec.SymInfo.fvarOf 1) :=
    ⟨rfl, rfl, rfl, [13], rfl, rfl⟩
  exact ⟨⟨sampleCell, rfl, meaning⟩, ⟨sampleCell, rfl, meaning⟩, by decide⟩

end Mettapedia.Languages.VibeITP.Native.HeapControls
