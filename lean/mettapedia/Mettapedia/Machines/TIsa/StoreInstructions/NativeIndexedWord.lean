import Mettapedia.Machines.TIsa.StoreInstructions.NativeArenaGeometry
import Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup

/-!
# Placed word access in a contiguous arena

The same two fetched instructions address a qword in a canonical
arena or in any of its spans. The caller establishes the bound
on the original index. The byte code contains no selected pointer
or word. R10 is the calculated address and RAX is the data word.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedWord

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Encoding Controls Reads CodeApart footprint)
open X86PlacedScalar (Code)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open NativeArenaGeometry (Region)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def storeEncoding : Encoding := .direct 10 (by decide) (by decide)

def loadWire (destination : Fin 16) (different : destination ≠ 10) : NativeWords.Wiring :=
  ⟨10, by decide, by decide, storeEncoding, destination, different.symm, different.symm⟩

def loadToCode (base : Base) (index : Index) (destination : Fin 16) : List ℕ :=
  addressCode 10 index 3 base ++ X86DataLoad.code true destination 10 0

def loadCode (base : Base) (index : Index) : List ℕ :=
  loadToCode base index 0

def storeCode (base : Base) (index : Index) : List ℕ :=
  addressCode 10 index 3 base ++ storeEncoding.bytes 0 0

theorem load_size (base : Base) (index : Index) : (loadCode base index).length = 11 := rfl
theorem load_to_size (base : Base) (index : Index) (destination : Fin 16) :
    (loadToCode base index destination).length = 11 := rfl
theorem store_size (base : Base) (index : Index) : (storeCode base index).length = 11 := rfl

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev readClobbers : Finset Register := {.r10, .rax, .rip}
def loadClobbers (destination : Fin 16) : Finset Register := {.r10, key destination, .rip}
abbrev writeClobbers : Finset Register := {.r10, .rip}

theorem read_clobbers_data : readClobbers ⊆ dataRegisters := by decide
theorem write_clobbers_data : writeClobbers ⊆ dataRegisters := by decide

private theorem cell_pointer {length : ℕ} (region : Region length) (start : ℕ) (ordinal : Word)
    (within : start + ordinal.toNat < length) :
    (region.wordCell ⟨start + ordinal.toNat, within⟩).pointer = region.atWord start + ordinal * 8 := by
  change region.atWord (start + ordinal.toNat) = _
  rw [← region.atWord_next start ordinal.toNat, NativeArenaGeometry.word_scale8]

theorem fetched_load_to (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (extent : start + 11 ≤ image.size)
    (baseRegister : Base) (indexRegister : Index) (destination : Fin 16) (distinct : destination ≠ 10)
    {length : ℕ} (region : Region length)
    (offset : ℕ) (ordinal value : Word) (within : offset + ordinal.toNat < length)
    (pointer : lookup before baseRegister.register = some (region.atWord offset))
    (index : lookup before indexRegister.register = some ordinal)
    (read : Reads before ((region.wordCell ⟨offset + ordinal.toNat, within⟩).cell 0).address value)
    (placed : Code image start (loadToCode baseRegister indexRegister destination)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame (loadClobbers destination) ∅ before after ∧ lookup after destination = some value ∧
      Nonempty (At image after base (start + 11)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let bank := region.wordCell ⟨offset + ordinal.toNat, within⟩
  obtain ⟨lea, load⟩ := NativeWords.code_append (show Code image start
    (addressCode 10 indexRegister 3 baseRegister ++ X86DataLoad.code true destination 10 0) from placed)
  have loadFits : start + 4 + 7 ≤ image.size := extent
  obtain ⟨addressed, one, registerFrame, address, ⟨next⟩⟩ := X86IndexedAddress.forms_address other extra vector point
    (by omega) 10 indexRegister 3 baseRegister lea (region.atWord offset) ordinal pointer index
  have frame := X86StateFrame.registerOnly registerFrame
  let source : NativeWords.Source bank.pointer := .copy 0 (bank.cell 0)
  have exactAddress : lookup addressed 10 = some bank.pointer := by
    rw [cell_pointer]
    exact address
  obtain ⟨after, two, kept, result, endpoint⟩ := source.fetch (handlers other extra) vector (loadWire destination distinct) value next
    (controls.transport frame (by decide)) exactAddress (read.preserved frame (by simp)) loadFits load
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at two
  exact ⟨after, X86FuelPrefix.fetches_then 1 1 before addressed after one two,
    (frame.trans kept).mono (by
      intro register touched
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, NativeWords.touched, loadWire, loadClobbers,
        show key 10 = .r10 from rfl] at touched ⊢
      tauto) (by simp), result, endpoint⟩

theorem fetched_load (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (extent : start + 11 ≤ image.size)
    (baseRegister : Base) (indexRegister : Index) {length : ℕ} (region : Region length)
    (offset : ℕ) (ordinal value : Word) (within : offset + ordinal.toNat < length)
    (pointer : lookup before baseRegister.register = some (region.atWord offset))
    (index : lookup before indexRegister.register = some ordinal)
    (read : Reads before ((region.wordCell ⟨offset + ordinal.toNat, within⟩).cell 0).address value)
    (placed : Code image start (loadCode baseRegister indexRegister)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame readClobbers ∅ before after ∧ lookup after 0 = some value ∧
      Nonempty (At image after base (start + 11)) :=
  fetched_load_to other extra vector point controls extent baseRegister indexRegister 0 (by decide) region
    offset ordinal value within pointer index read placed

theorem fetched_store (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (extent : start + 11 ≤ image.size)
    (baseRegister : Base) (indexRegister : Index) {length : ℕ} (region : Region length)
    (offset : ℕ) (ordinal value : Word) (within : offset + ordinal.toNat < length)
    (pointer : lookup before baseRegister.register = some (region.atWord offset))
    (index : lookup before indexRegister.register = some ordinal) (source : lookup before 0 = some value)
    (placed : Code image start (storeCode baseRegister indexRegister))
    (apart : CodeApart image base (footprint ((region.wordCell ⟨offset + ordinal.toNat, within⟩).cell 0).address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame writeClobbers (footprint ((region.wordCell ⟨offset + ordinal.toNat, within⟩).cell 0).address)
        before after ∧
      Reads after ((region.wordCell ⟨offset + ordinal.toNat, within⟩).cell 0).address value ∧
      Nonempty (At image after base (start + 11)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let bank := region.wordCell ⟨offset + ordinal.toNat, within⟩
  obtain ⟨lea, store⟩ := NativeWords.code_append (show Code image start
    (addressCode 10 indexRegister 3 baseRegister ++ storeEncoding.bytes 0 0) from placed)
  have storeFits : start + 4 + 7 ≤ image.size := extent
  obtain ⟨addressed, one, registerFrame, address, ⟨next⟩⟩ := X86IndexedAddress.forms_address other extra vector point
    (by omega) 10 indexRegister 3 baseRegister lea (region.atWord offset) ordinal pointer index
  have frame := X86StateFrame.registerOnly registerFrame
  have exactAddress : lookup addressed 10 = some bank.pointer := by
    rw [cell_pointer]
    exact address
  obtain ⟨after, two, kept, result, endpoint⟩ := X86PlacedMemory.stores
    (handlers other extra) vector next (controls.transport frame (by decide)) storeEncoding 0 0 bank.pointer value (bank.cell 0)
    exactAddress ((frame.lookup 0 (by decide)).trans source) storeFits store apart
  exact ⟨after, X86FuelPrefix.fetches_then 1 1 before addressed after one two,
    (frame.trans kept).mono (by decide) (by simp [bank]), result, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedWord
