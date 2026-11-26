import Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMemory

/-!
# Writing one classified occurrence

Only the slot belonging to the current ordinal is written.
The input value is already the classifier's mark, and the
output array records positions in the held occurrence order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMark

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads Cell CodeApart)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeCollectMemory (Prefix slotBytes mark)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def outputRegister : X86IndexedAddress.Base := ⟨2, by decide⟩
def ordinalRegister : X86PreparedLea.Index := ⟨1, by decide⟩
def pointerCode : List ℕ := X86DataLoad.code true 2 6 144
def storeCode : List ℕ := NativeIndexedWord.storeCode outputRegister ordinalRegister

def emit : List ℕ :=
  NativeGuardOperands.stackCode ++ (pointerCode ++ (NativeGuardOperands.indexCode ++ storeCode))

theorem emit_size : emit.length = 28 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 28 ≤ image.size
  stack : Code image start NativeGuardOperands.stackCode
  pointer : Code image (start + 3) pointerCode
  ordinal : Code image (start + 10) NativeGuardOperands.indexCode
  store : Code image (start + 17) storeCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (extent : start + 28 ≤ image.size)
    (code : Code image start emit) : Placed image start := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (NativeGuardOperands.stackCode ++ _) from code)
  obtain ⟨pointer, rest⟩ := NativeWords.code_append rest
  obtain ⟨ordinal, store⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, pointer, ordinal, store⟩

abbrev clobbers : Finset Register := {.rdx, .rcx, .rsi, .r10, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86IndexedAddress.handlers

variable {cap : ℕ} {output : Region cap} {frame : Frame} {pointer : Cell frame.pointer 144}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (code : Placed image start) (point : At image before base start) (controls : Controls before)
    (bits : Array Bool) (selected : Bool) (resident : Prefix frame output pointer bits before)
    (stack : lookup before 4 = some frame.pointer)
    (ordinal : Reads before (frame.cell 14).address (BitVec.ofNat 64 bits.size)) (which : lookup before 0 = some (mark selected))
    (room : bits.size < cap)
    (apart : CodeApart image base (slotBytes output ⟨bits.size, room⟩))
    (isolated : Disjoint (X86PlacedMemory.footprint pointer.address) (slotBytes output ⟨bits.size, room⟩)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes output ⟨bits.size, room⟩) before after ∧
      Prefix frame output pointer (bits.push selected) after ∧ Nonempty (At image after base (start + 28)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let i := BitVec.ofNat 64 bits.size
  have exactWord : i.toNat = bits.size := NativeSubstitutionReserve.word_of_region output _ room.le
  have place : 0 + i.toNat < cap := by rw [Nat.zero_add, exactWord]; exact room
  have same : (⟨0 + i.toNat, place⟩ : Fin cap) = ⟨bits.size, room⟩ := Fin.ext ((Nat.zero_add _).trans exactWord)
  have extent := code.extent
  obtain ⟨a, opened, move, stackAddress, ⟨atPointer⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have first := X86StateFrame.registerOnly move
  let address : NativeWords.Source frame.pointer := .copy 144 pointer
  obtain ⟨b, loaded, loadedFrame, outputKnown, ⟨atIndex⟩⟩ := address.fetch (handlers other extra) vector
    NativeGuardOperands.pointerWire (output.atWord 0) atPointer (controls.transport first (by decide))
    stackAddress (resident.base.preserved first (by simp)) (show start + 10 ≤ image.size by omega) code.pointer
  have second := first.trans loadedFrame
  obtain ⟨c, indexed, indexFrame, knownIndex, ⟨atStore⟩⟩ := (NativeAgendaRead.fieldSource frame 14).fetch
    (handlers other extra) vector NativeGuardOperands.indexWire i (show At image b base (start + 10) from atIndex)
    (controls.transport second (by decide)) ((loadedFrame.lookup 6 (by decide)).trans stackAddress)
    (ordinal.preserved second (by simp)) (show start + 17 ≤ image.size by omega) code.ordinal
  have almost := second.trans indexFrame
  obtain ⟨after, stored, writeFrame, readback, endpoint⟩ := NativeIndexedWord.fetched_store other extra vector
    (show At image c base (start + 17) from atStore) (controls.transport almost (by decide)) (by omega)
    outputRegister ordinalRegister output 0 i (mark selected) place ((indexFrame.lookup 2 (by decide)).trans outputKnown)
    knownIndex ((almost.lookup 0 (by decide)).trans which) code.store (by rw [same]; exact apart)
  rw [same] at writeFrame readback
  have all : X86StateFrame.Frame clobbers (slotBytes output ⟨bits.size, room⟩) before after :=
    (almost.trans writeFrame).mono (by decide) (by simp [slotBytes])
  have pointerKept := resident.base.preserved all isolated
  have marks := resident.bits.extend room selected all readback
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loaded indexed
  have ran := X86FuelPrefix.fetches_then 3 2 before c after
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b opened loaded) indexed) stored
  exact ⟨after, ran, all, ⟨pointerKept, marks⟩, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeCollectMark
