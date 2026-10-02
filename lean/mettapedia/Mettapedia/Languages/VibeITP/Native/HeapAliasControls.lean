import Mettapedia.Languages.VibeITP.Native.TermHeapControls
import Mettapedia.Languages.VibeITP.Native.HeapRecordFrames

/-!
# Content and ownership counters do not exclude metadata aliasing

These deliberately forged heaps are not asserted reachable by the guest.
They show why preserving meaning across reference-count writes needs a reached
pointer discipline in addition to contents and allocation extents.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.HeapAliasControls

open Mettapedia.GSLT.LanguageDef.NativeOps
open HeapCells

def markers : TermHeap.Markers := ⟨⟨1, 0, []⟩, ⟨2, 0, []⟩⟩
def symbolAddress : Address := ⟨10, 0, []⟩
def termAddress : Address := ⟨40, 0, []⟩
def countAddress : Address := ⟨40, 0, [6]⟩

def marker : SymbolCell := ⟨2, 0, ⟨none, 0⟩, ⟨none, 0⟩, 0, true⟩
def term : TermCell :=
  ⟨some markers.boundVariable, 0, ⟨none, 0⟩, ⟨none, 0⟩, 1, false, 1⟩
def symbol : SymbolCell :=
  ⟨0, 1, ⟨some countAddress, 1⟩, ⟨some ⟨30, 0, []⟩, 1⟩, 1, false⟩
def info : Spec.SymInfo := ⟨.constant, [1]⟩
def signature : Spec.Sig := fun name => if name = .fresh 0 then some info else none

def memory : SourceMemory :=
  ⟨fun storage element =>
    if element ≠ 0 then none else
    if storage = 1 then some marker.sourceValue else
    if storage = 10 then some symbol.sourceValue else
    if storage = 30 then some (.word 13) else
    if storage = 40 then some term.sourceValue else none,
    fun storage => if storage = 1 ∨ storage = 10 ∨ storage = 30 ∨ storage = 40 then some 1 else none⟩

def after : SourceMemory :=
  sourceStoreCell memory 40 0 { term with references := 2 }.sourceValue

theorem symbol_meaning_before : SymbolHeap.At memory symbolAddress (.fresh 0) info :=
  ⟨symbol, rfl, rfl, rfl, rfl, [13], rfl, rfl⟩

theorem term_meaning_before : TermHeap.At memory signature markers termAddress (.bvar 0) :=
  .bvar (cell := term) (marker := marker) rfl rfl rfl rfl rfl rfl rfl rfl

theorem actual_count_write : sourceWrite memory countAddress (.word 2) = some after :=
  term_reference_write memory 40 0 term 2 rfl

theorem term_meaning_after : TermHeap.At after signature markers termAddress (.bvar 0) :=
  .bvar (cell := { term with references := 2 }) (marker := marker)
    rfl rfl rfl rfl rfl rfl rfl rfl

theorem symbol_meaning_is_not_preserved : ¬ SymbolHeap.At after symbolAddress (.fresh 0) info := by
  intro represented
  obtain ⟨cell, stored, meaning⟩ := represented
  have same := symbol_cell_unique after symbolAddress cell symbol stored rfl
  cases same
  have binders := meaning.2.2.1
  change some [2] = some [1] at binders
  cases binders

theorem alias_is_a_readable_owned_record_field :
    memory.owned termAddress.storage = some 1 ∧
    sourceRead memory countAddress = some (.word 1) ∧
    sourceRead after countAddress = some (.word 2) ∧
    countAddress.fields ≠ [] := ⟨rfl, rfl, rfl, by decide⟩

def ordinaryAfter : SourceMemory := sourceStoreCell TermHeapControls.memory 101 0
  { TermHeapControls.rootCell with references := 2 }.sourceValue

theorem ordinary_reference_count_write :
    sourceWrite TermHeapControls.memory ⟨101, 0, [6]⟩ (.word 2) = some ordinaryAfter :=
  term_reference_write TermHeapControls.memory 101 0 TermHeapControls.rootCell 2 rfl

theorem ordinary_arrays_remain_readable :
    words ordinaryAfter ⟨some ⟨20, 0, []⟩, 2⟩ = some [0, 0] ∧
    references ordinaryAfter TermHeapControls.rootCell.arguments =
      some [TermHeapControls.childAddress, TermHeapControls.childAddress] ∧
    literal ordinaryAfter TermHeapControls.literalCell.literal = some [65, 66] := by
  have binders := term_count_write_preserves_root_arrays TermHeapControls.memory ordinaryAfter 101 0
    TermHeapControls.rootCell 2 rfl ordinary_reference_count_write ⟨some ⟨20, 0, []⟩, 2⟩
    (by intro base same; cases same; rfl)
  have children := term_count_write_preserves_root_arrays TermHeapControls.memory ordinaryAfter 101 0
    TermHeapControls.rootCell 2 rfl ordinary_reference_count_write TermHeapControls.rootCell.arguments
    (by intro base same; cases same; rfl)
  have bytes := term_count_write_preserves_root_arrays TermHeapControls.memory ordinaryAfter 101 0
    TermHeapControls.rootCell 2 rfl ordinary_reference_count_write TermHeapControls.literalCell.literal
    (by intro base same; cases same; rfl)
  exact ⟨binders.1, children.2.1, bytes.2.2⟩

theorem forged_binder_does_not_meet_address_discipline : ¬ symbol.binders.Rooted := by
  intro rooted
  have empty := rooted countAddress rfl
  change [6] = [] at empty
  contradiction

end Mettapedia.Languages.VibeITP.Native.HeapAliasControls
