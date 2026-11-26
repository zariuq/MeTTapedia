import Mettapedia.Machines.TIsa.StoreInstructions.ProjectedCandidate
import Mettapedia.Machines.TIsa.X86IndexedAddress

/-!
# Fetched selection of a candidate bank by ordinal

The directory holds one pointer per occurrence. The code compares
the original unsigned ordinal with the count before forming any
scaled address. A rejected ordinal does not fetch an address from
the directory, even if scaling it would wrap.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads)
open X86PlacedScalar (Code CompareBranch registerCode)
open NativeWords (Wiring)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev handlers := X86IndexedAddress.handlers

theorem match_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    MemoryBinding.handlers (X86PlacedFrameAddress.nativeBase other) extra = handlers other extra := rfl

private theorem load_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    NativeWords.handlers (handlers other extra) = handlers other extra := rfl

structure Layout (count : ℕ) where
  directory : WordRegion.Region count
  header : Word
  countOffset : BitVec 32
  countCell : Cell header countOffset

variable {count : ℕ}

structure Layout.Represents (layout : Layout count) (pointers : Fin count → Word) (state : MemoryBinding.Native) : Prop where
  countRead : Reads state layout.countCell.address (BitVec.ofNat 64 count)
  pointerRead : ∀ index, Reads state (layout.directory.cell index).address (pointers index)

private theorem Layout.count_exact (layout : Layout count) : (BitVec.ofNat 64 count).toNat = count := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := layout.directory.shortOffset
  omega

def countWire : Wiring := ⟨7, by decide, by decide, MemoryBinding.storeEncoding, 14, by decide, by decide⟩
def pointerWire : Wiring := ⟨15, by decide, by decide, MemoryBinding.storeEncoding, 7, by decide, by decide⟩
def indexReg : X86PreparedLea.Index := ⟨1, by decide⟩
def pointerReg : X86IndexedAddress.Base := ⟨2, by decide⟩

structure Checked (image : NativeImage.View) (start refused : ℕ) (source : Fin 16) (field : BitVec 32) : Prop where
  extent : start + 30 ≤ image.size
  countBytes : Code image start (X86DataLoad.code true 14 7 field)
  check : CompareBranch image (start + 7) refused .lessUnsigned source 14
  copyIndex : Code image (start + 16) (registerCode 0x89 source 1)
  locate : Code image (start + 19) (X86IndexedAddress.addressCode 15 indexReg 3 pointerReg)
  readPointer : Code image (start + 23) (X86DataLoad.code true 7 15 0)

abbrev clobbers : Finset Register := {.r14, .rflags, .rcx, .r15, .rdi, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

/-- A placed directory lookup either loads the exact bank pointer
or reaches refusal with no data read beyond the count. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {before : MemoryBinding.Native} {base : BitVec 48} {start refused : ℕ}
    (point : At image before base start) (controls : Controls before)
    (layout : Layout count) (pointers : Fin count → Word) (resident : layout.Represents pointers before)
    (header : lookup before 7 = some layout.header) (directory : lookup before 2 = some layout.directory.pointer)
    (source : Fin 16) (keepsSource : source ≠ 14) (ordinal : Word) (index : lookup before source = some ordinal)
    (checked : Checked image start refused source layout.countOffset) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if inside : ordinal.toNat < count then
        steps = 6 ∧ lookup after 7 = some (pointers ⟨ordinal.toNat, inside⟩) ∧
          Nonempty (At image after base (start + 30))
      else steps = 3 ∧ X86StateFrame.Frame {.r14, .rflags, .rip} ∅ before after ∧
        Nonempty (At image after base refused) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let countSource : NativeWords.Source layout.header := .copy layout.countOffset layout.countCell
  obtain ⟨size, ranCount, sizeFrame, knownCount, ⟨atCheck⟩⟩ := countSource.fetch (handlers other extra) vector countWire
    (BitVec.ofNat 64 count) point controls header resident.countRead
    (by have := checked.extent; change start + 7 ≤ image.size; omega) checked.countBytes
  rw [load_handlers] at ranCount
  have keptIndex := (sizeFrame.lookup _ (NativeWords.outside_scratch countWire source keepsSource)).trans index
  obtain ⟨tested, ranCheck, checkFrame, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector atCheck .lessUnsigned source 14
    checked.check ordinal (BitVec.ofNat 64 count) keptIndex knownCount
  have prelude := sizeFrame.trans (X86StateFrame.registerOnly checkFrame)
  have ranPrelude := X86FuelPrefix.fetches_then 1 2 before size tested ranCount ranCheck
  change At image tested base (if decide (ordinal.toNat < (BitVec.ofNat 64 count).toNat)
    then start + 7 + 9 else refused) at endpoint
  rw [layout.count_exact] at endpoint
  by_cases inside : ordinal.toNat < count
  · simp only [inside, decide_true, if_true] at endpoint
    have atCopy : At image tested base (start + 16) := endpoint
    have sourceKnown := (checkFrame.lookup source (by
      fin_cases source <;> decide)).trans keptIndex
    obtain ⟨copied, ranCopy, copyFrame, lowIndex, ⟨atLocate⟩⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector atCopy (by have := checked.extent; omega)
      source 1 ordinal sourceKnown checked.copyIndex
    have copiedFrame := prelude.trans (X86StateFrame.registerOnly copyFrame)
    have atAddress : At image copied base (start + 19) := atLocate
    obtain ⟨addressed, ranAddress, addressFrame, effective, ⟨atLoad⟩⟩ := X86IndexedAddress.forms_address
      other extra vector atAddress (by have := checked.extent; omega) 15 indexReg 3 pointerReg
      checked.locate layout.directory.pointer ordinal ((copiedFrame.lookup 2 (by decide)).trans directory) lowIndex
    have brought : X86StateFrame.Frame _ ∅ before addressed :=
      (copiedFrame.trans (X86StateFrame.registerOnly addressFrame)).mono (Finset.Subset.refl _) (by simp)
    let raw := layout.directory.cell ⟨ordinal.toNat, inside⟩
    let cell : Cell (raw.address.signExtend 64) 0 :=
      ⟨raw.address, by simp, raw.upper, raw.aligned⟩
    let leaf : NativeWords.Source (raw.address.signExtend 64) := .copy 0 cell
    have points : lookup addressed 15 = some (raw.address.signExtend 64) :=
      effective.trans (congrArg some (layout.directory.indexed_cell ordinal inside))
    have atRead : At image addressed base (start + 23) := atLoad
    obtain ⟨loaded, ranLoad, loadFrame, selected, ⟨next⟩⟩ := leaf.fetch (handlers other extra) vector pointerWire
      (pointers ⟨ordinal.toNat, inside⟩) atRead (controls.transport brought (by decide)) points
      ((resident.pointerRead ⟨ordinal.toNat, inside⟩).preserved brought (by simp))
      checked.extent checked.readPointer
    rw [load_handlers] at ranLoad
    have copiedRun := X86FuelPrefix.fetches_then 3 1 before tested copied ranPrelude ranCopy
    have addressRun := X86FuelPrefix.fetches_then 4 1 before copied addressed copiedRun ranAddress
    refine ⟨loaded, 6, X86FuelPrefix.fetches_then 5 1 before addressed loaded addressRun ranLoad,
      (brought.trans loadFrame).mono (by decide) (by simp), ?_⟩
    rw [dif_pos inside]
    exact ⟨rfl, selected, ⟨next⟩⟩
  · simp only [inside, decide_false] at endpoint
    refine ⟨tested, 3, ranPrelude, prelude.mono (by decide) (by simp), ?_⟩
    rw [dif_neg inside]
    exact ⟨rfl, prelude.mono (by decide) (by simp), ⟨endpoint⟩⟩

namespace Examples

/-- Index scaling alone would mistake this huge ordinal for zero. -/
theorem scaled_alias : (0x2000000000000000#64) * 8 = 0 := by decide +kernel

theorem rejects_scaled_alias (layout : Layout count) : ¬ (0x2000000000000000#64).toNat < count := by
  have limit := layout.directory.shortOffset
  change ¬ 2 ^ 61 < count
  omega

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup
