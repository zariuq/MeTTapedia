import Mettapedia.Languages.VibeITP.Native.TermHeapUnique

/-! Concrete shared term graphs, literal bytes and interpretation refusals. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermHeapControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells TermHeap

def markers : Markers := ⟨⟨1, 0, []⟩, ⟨2, 0, []⟩⟩
def symbolAddress : Address := ⟨10, 0, []⟩
def childAddress : Address := ⟨100, 0, []⟩
def rootAddress : Address := ⟨101, 0, []⟩
def literalAddress : Address := ⟨102, 0, []⟩

def boundMarker : SymbolCell := ⟨2, 0, ⟨none, 0⟩, ⟨none, 0⟩, 0, true⟩
def literalMarker : SymbolCell := ⟨3, 0, ⟨none, 0⟩, ⟨none, 0⟩, 0, true⟩
def symbolCell : SymbolCell :=
  ⟨1, 2, ⟨some ⟨20, 0, []⟩, 2⟩, ⟨some ⟨30, 0, []⟩, 1⟩, 1, false⟩
def childCell : TermCell :=
  ⟨some markers.boundVariable, 0, ⟨none, 0⟩, ⟨none, 0⟩, 1, false, 2⟩
def rootCell : TermCell :=
  ⟨some symbolAddress, 0, ⟨none, 0⟩, ⟨some ⟨40, 0, []⟩, 2⟩, 1, true, 1⟩
def literalCell : TermCell :=
  ⟨some markers.literal, 0, ⟨some ⟨50, 0, []⟩, 2⟩, ⟨none, 0⟩, 0, false, 1⟩

def memory : SourceMemory :=
  ⟨fun storage element =>
    if storage = 1 ∧ element = 0 then some boundMarker.sourceValue else
    if storage = 2 ∧ element = 0 then some literalMarker.sourceValue else
    if storage = 10 ∧ element = 0 then some symbolCell.sourceValue else
    if storage = 20 ∧ element < 2 then some (.word 0) else
    if storage = 30 ∧ element = 0 then some (.word 13) else
    if storage = 40 ∧ element < 2 then some (.reference (some childAddress)) else
    if storage = 50 ∧ element = 0 then some (.byte 65) else
    if storage = 50 ∧ element = 1 then some (.byte 66) else
    if storage = 100 ∧ element = 0 then some childCell.sourceValue else
    if storage = 101 ∧ element = 0 then some rootCell.sourceValue else
    if storage = 102 ∧ element = 0 then some literalCell.sourceValue else none,
    fun _ => none⟩

def signature : Spec.Sig := fun symbol =>
  if symbol = .fresh 0 then some (Spec.SymInfo.fvarOf 2) else none

theorem child_represented : At memory signature markers childAddress (.bvar 0) :=
  .bvar (cell := childCell) (marker := boundMarker) rfl rfl rfl rfl rfl rfl rfl rfl

theorem literal_represented : At memory signature markers literalAddress (.lit [65, 66]) :=
  .lit (cell := literalCell) (marker := literalMarker) rfl rfl rfl rfl rfl
    (by decide +kernel) rfl rfl rfl

theorem shared_application_represented :
    At memory signature markers rootAddress (.app (.fresh 0) [.bvar 0, .bvar 0]) := by
  have symbolMeaning : SymbolHeap.At memory symbolAddress (.fresh 0) (Spec.SymInfo.fvarOf 2) :=
    ⟨symbolCell, rfl, rfl, rfl, rfl, [13], rfl, rfl⟩
  exact .app (cell := rootCell) rfl rfl symbolMeaning rfl rfl
    (shared_child_retained_twice child_represented) rfl rfl rfl rfl

theorem shared_argument_occurrences_preserved :
    references memory rootCell.arguments = some [childAddress, childAddress] ∧
    ListAt memory signature markers [childAddress, childAddress] [.bvar 0, .bvar 0] :=
  ⟨rfl, shared_child_retained_twice child_represented⟩

theorem shared_application_well_formed :
    Spec.WellFormed signature (.app (.fresh 0) [.bvar 0, .bvar 0]) = true :=
  wellFormed shared_application_represented

theorem duplicate_argument_cannot_be_discarded :
    ¬ At memory signature markers rootAddress (.app (.fresh 0) [.bvar 0]) :=
  different_terms_cannot_share_representation (by decide +kernel) shared_application_represented

theorem literal_contents_cannot_be_reordered :
    ¬ At memory signature markers literalAddress (.lit [66, 65]) :=
  different_terms_cannot_share_representation (by decide +kernel) literal_represented

theorem missing_node_cannot_be_read :
    ∀ term, ¬ At memory signature markers ⟨103, 0, []⟩ term :=
  missing_cell_unrepresented rfl

theorem incorrect_cache_cannot_describe_shared_graph :
    ∀ cell : TermCell, sourceRead memory rootAddress = some cell.sourceValue →
      cell.depth.val = 1 ∧ cell.hasFreeVariable = true := by
  intro cell read
  exact cache_unique shared_application_represented cell read

end Mettapedia.Languages.VibeITP.Native.TermHeapControls
