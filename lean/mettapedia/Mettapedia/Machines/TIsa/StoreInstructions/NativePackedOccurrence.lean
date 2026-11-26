import Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate

/-!
# Native selection of the two words of an occurrence

The ordinal selects the identity and term-code cells together.
This projection is shared by the symbolic role test and equation
append. It is independent of the pattern and does not interpret
the occurrence as ground.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativePackedOccurrence

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open NativeRoleGate (WordAt)
open MemoryBinding (Native)
open PackedOccurrences (Codes)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Bank := WordRegion.Region 2

def wordAt (bank : Bank) (field : Fin 2) : WordAt bank.pointer :=
  ⟨BitVec.ofNat 32 (WordRegion.offset field), bank.cell field⟩

abbrev identity (bank : Bank) := wordAt bank 0
abbrev termCode (bank : Bank) := wordAt bank 1

structure Prepared (packed : PackedOccurrences.Layout) (native : Native) where
  lookupCode : NativeCandidateLookup.Layout packed.occurrences.size
  banks : Fin packed.occurrences.size → Bank
  resident : lookupCode.Represents (fun index => (banks index).pointer) native
  identity : ∀ index, Reads native (wordAt (banks index) 0).cell.address (packed.occurrences[index.val]).1
  term : ∀ index, Reads native (wordAt (banks index) 1).cell.address (packed.occurrences[index.val]).2

theorem selected_pair {T : Type*} (codes : Codes T) {packed : PackedOccurrences.Layout}
    {ordinal id : ℕ} {term : T} (found : PackedOccurrences.at? codes packed ordinal = some (id, term)) :
    ∃ index : Fin packed.occurrences.size, index.val = ordinal ∧
      (packed.occurrences[index.val]).1.toNat = id ∧ codes.decode (packed.occurrences[index.val]).2 = some term := by
  unfold PackedOccurrences.at? at found
  obtain ⟨pair, atIndex, reopened⟩ := Option.bind_eq_some_iff.mp found
  have bounds := (Array.getElem?_eq_some_iff.mp atIndex).choose
  have record := (Array.getElem?_eq_some_iff.mp atIndex).choose_spec
  unfold PackedOccurrences.unpackRow at reopened
  obtain ⟨decoded, decodedValue, exactRecord⟩ := Option.map_eq_some_iff.mp reopened
  obtain ⟨identity, rfl⟩ := Prod.mk.inj exactRecord
  refine ⟨⟨ordinal, bounds⟩, rfl, ?_, ?_⟩
  · rw [record]
    exact identity
  · rw [record]
    exact decodedValue

/-- Fetched lookup establishes the actual identity and term word
readouts used by MATCH. Both readouts stay valid after lookup. -/
theorem fetched {T : Type*} (codes : Codes T) (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {codeBase : BitVec 48} {start refused : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    {packed : PackedOccurrences.Layout} (ready : Prepared packed before)
    (header : lookup before 7 = some ready.lookupCode.header)
    (base : lookup before 2 = some ready.lookupCode.directory.pointer)
    (source : Fin 16) (safe : source ≠ 14) (ordinal : Word) (indexRead : lookup before source = some ordinal)
    (placed : NativeCandidateLookup.Checked image start refused source ready.lookupCode.countOffset)
    (id : ℕ) (term : T) (found : PackedOccurrences.at? codes packed ordinal.toNat = some (id, term)) :
    letI : OtherOpcodeHandlers := NativeCandidateLookup.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ (after : Native) (index : Fin packed.occurrences.size),
      (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame NativeCandidateLookup.clobbers ∅ before after ∧
      index.val = ordinal.toNat ∧
      lookup after 7 = some (ready.banks index).pointer ∧
      (identity (ready.banks index)).ReadsId after id ∧
      Reads after (termCode (ready.banks index)).cell.address (packed.occurrences[index.val]).2 ∧
      codes.decode (packed.occurrences[index.val]).2 = some term ∧
      Nonempty (At image after codeBase (start + 30)) := by
  obtain ⟨index, ordinalExact, identityExact, termExact⟩ := selected_pair codes found
  have within : ordinal.toNat < packed.occurrences.size := ordinalExact ▸ index.isLt
  obtain ⟨after, steps, ran, frame, located⟩ :=
    NativeCandidateLookup.fetched other extra vector point controls ready.lookupCode _ ready.resident
      header base source safe ordinal indexRead placed
  rw [dif_pos within] at located
  obtain ⟨rfl, selected, finish⟩ := located
  have sameIndex : (⟨ordinal.toNat, within⟩ : Fin packed.occurrences.size) = index := Fin.ext ordinalExact.symm
  rw [sameIndex] at selected
  have actual := (ready.identity index).preserved frame (by simp)
  have fitsId : id < 2 ^ 64 := identityExact ▸ (packed.occurrences[index.val]).1.isLt
  have word : (packed.occurrences[index.val]).1 = BitVec.ofNat 64 id := by
    rw [← identityExact, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨after, index, ran, frame, ordinalExact, selected, ⟨fitsId, word ▸ actual⟩,
    (ready.term index).preserved frame (by simp), termExact, finish⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativePackedOccurrence
