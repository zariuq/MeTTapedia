import Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailReserve

/-!
# Making one completed trail entry live

The count is advanced only after the new record exists.
The frame and the agenda cursor are unaffected, so this block
can be used at the end of the same logical solver transition.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailPublish

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint Encoding)
open X86PlacedScalar (Code registerCode)
open NativeTrailReserve (Descriptor stackCode pointerCode pointerWire)
open NativeAgendaRecords (Ready Records)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def loadCode : List ℕ := X86DataLoad.code true 14 2 0
def countWire : NativeWords.Wiring := ⟨2, by decide, by decide, MemoryBinding.storeEncoding, 14, by decide, by decide⟩
def increment : List ℕ := registerCode (X86Arithmetic.opcode .add) 13 14
def encoding : Encoding := .direct 2 (by decide) (by decide)
def storeCode : List ℕ := encoding.bytes 14 0
def emit : List ℕ := stackCode ++ (pointerCode ++ (loadCode ++ (increment ++ storeCode)))

theorem emit_size : emit.length = 27 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 27 ≤ image.size
  stack : Code image start stackCode
  pointer : Code image (start + 3) pointerCode
  count : Code image (start + 10) loadCode
  step : Code image (start + 17) increment
  store : Code image (start + 20) storeCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (extent : start + 27 ≤ image.size)
    (code : Code image start emit) : Placed image start := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨pointer, rest⟩ := NativeWords.code_append rest
  obtain ⟨count, rest⟩ := NativeWords.code_append rest
  obtain ⟨step, store⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, pointer, count, step, store⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rdx, .rsi, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start)
    {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {old new : PackedEquations.Arena}
    (frame : Descriptor) (stack : lookup before 4 = some frame.pointer)
    (trailPtr : Reads before (frame.cell 7).address layout.words.pointer)
    (live : Ready layout old before) (ready : Records layout new before) (size : new.size = old.size + 1)
    (one : lookup before 13 = some 1) (codeApart : CodeApart image base (footprint (layout.header.cell 0).address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (footprint (layout.header.cell 0).address) before after ∧
      Ready layout new after ∧ lookup after 6 = some frame.pointer ∧ Nonempty (At image after base (start + 27)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, moved, move, baseWord, ⟨atPointer⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) 4 6 frame.pointer stack placed.stack
  have stackFrame := X86StateFrame.registerOnly move
  obtain ⟨b, followed, followFrame, pointer, ⟨atCount⟩⟩ := (NativeAgendaRead.fieldSource frame 7).fetch
    (handlers other extra) vector pointerWire layout.words.pointer atPointer (controls.transport stackFrame (by decide))
    baseWord (trailPtr.preserved stackFrame (by simp)) (show start + 10 ≤ image.size by omega) placed.pointer
  have place := stackFrame.trans followFrame
  have trailBase : lookup b 2 = some layout.header.pointer := layout.header_pointer.symm ▸ pointer
  obtain ⟨c, counted, countFrame, len, ⟨atInc⟩⟩ := (NativeAgendaRead.fieldSource layout.header 0).fetch
    (handlers other extra) vector countWire (BitVec.ofNat 64 old.size)
    (show At image b base (start + 10) from atCount) (controls.transport place (by decide))
    trailBase (live.count.preserved place (by simp)) (show start + 17 ≤ image.size by omega) placed.count
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at followed counted
  have throughCount := place.trans countFrame
  obtain ⟨d, increased, incFrame, newLen, ⟨atStore⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector (show At image c base (start + 17) from atInc) (by omega)
    .add 13 14 (BitVec.ofNat 64 old.size) 1 ((throughCount.lookup 13 (by decide)).trans one) len placed.step
  have arithmetic : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [arithmetic] at increased
  have effective : lookup d 14 = some (BitVec.ofNat 64 new.size) := by
    change lookup d 14 = some (BitVec.ofNat 64 old.size + BitVec.ofNat 64 1) at newLen
    rwa [BitVec.ofNat_add_ofNat, ← size] at newLen
  have throughInc := throughCount.trans (X86StateFrame.registerOnly incFrame)
  obtain ⟨after, published, stored, liveCount, endpoint⟩ := X86PlacedMemory.stores (handlers other extra)
    vector (show At image d base (start + 20) from atStore) (controls.transport throughInc (by decide))
    encoding 14 0 layout.header.pointer (BitVec.ofNat 64 new.size) (layout.header.cell 0)
    (((countFrame.trans (X86StateFrame.registerOnly incFrame)).lookup 2 (by decide)).trans trailBase)
    effective extent placed.store codeApart
  have whole : X86StateFrame.Frame clobbers (footprint (layout.header.cell 0).address) before after :=
    (throughInc.trans stored).mono (by decide) (by simp)
  have framePointer := ((followFrame.trans countFrame).trans ((X86StateFrame.registerOnly incFrame).trans stored)).lookup 6 (by decide)
  have prelude := X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b moved followed) counted
  exact ⟨after, X86FuelPrefix.fetches_then 4 1 before d after
      (X86FuelPrefix.fetches_then 3 1 before c d prelude increased) published, whole,
    ⟨ready.fits, liveCount, fun i j => (ready.node i j).preserved whole (layout.header_apart _ _).symm⟩,
    framePointer.trans baseWord, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTrailPublish
