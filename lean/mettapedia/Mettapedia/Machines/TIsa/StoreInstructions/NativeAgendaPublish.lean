import Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaLoop

/-!
# Publishing one completed native agenda extension

All new records are ready before this block begins. There is
one write of the initialized length, followed by restoring the
application-tag register and returning to the solver entry.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaPublish

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint Encoding)
open X86PlacedScalar (Code Jump registerCode jumpDelta)
open PackedEquations (Arena)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def baseCode : List ℕ := registerCode 0x89 5 2
def encoding : Encoding := .direct 2 (by decide) (by decide)
def sizeCode : List ℕ := encoding.bytes 14 0
def restoreCode : List ℕ := X86Immediate32.code 14 2

def emit (start next : ℕ) : List ℕ :=
  baseCode ++ (sizeCode ++ (restoreCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 16) next)))

theorem emit_size (start next : ℕ) : (emit start next).length = 21 := rfl

structure Placed (image : NativeImage.View) (start next : ℕ) : Prop where
  extent : start + 21 ≤ image.size
  base : Code image start baseCode
  count : Code image (start + 3) sizeCode
  restore : Code image (start + 10) restoreCode
  jump : Jump image (start + 16) next

theorem placed_of_emitted (image : NativeImage.View) (start next : ℕ)
    (space : start + 21 ≤ image.size) (target : next ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start next)) : Placed image start next := by
  obtain ⟨base, rest⟩ := NativeWords.code_append (show Code image start (baseCode ++ _) from bytes)
  obtain ⟨count, rest⟩ := NativeWords.code_append rest
  obtain ⟨restore, jump⟩ := NativeWords.code_append rest
  refine ⟨space, base, count, restore, ⟨by omega, target, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rdx, .r14, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start next : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start next)
    {capacity : ℕ} {layout : NativeAgendaRecords.Layout capacity} {arena : Arena}
    (records : NativeAgendaRecords.Records layout arena before) (pointer : lookup before 5 = some layout.words.pointer)
    (length : lookup before 14 = some (BitVec.ofNat 64 arena.size))
    (apart : CodeApart image base (footprint (layout.header.cell 0).address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (footprint (layout.header.cell 0).address) before after ∧
      NativeAgendaRecords.Ready layout arena after ∧ lookup after 14 = some 2 ∧ Nonempty (At image after base next) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, moved, movedFrame, baseRead, ⟨atCount⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 5 2 layout.words.pointer pointer placed.base
  have registerOnly := X86StateFrame.registerOnly movedFrame
  obtain ⟨b, ranStore, storeFrame, visible, ⟨atRestore⟩⟩ := X86PlacedMemory.stores
    (handlers other extra) vector atCount (controls.transport registerOnly (by decide)) encoding 14 0
    layout.header.pointer (BitVec.ofNat 64 arena.size) (layout.header.cell 0) (layout.header_pointer.symm ▸ baseRead)
    ((movedFrame.lookup 14 (by decide)).trans length) (show start + 10 ≤ image.size by omega) placed.count apart
  obtain ⟨c, reset, resetFrame, app, ⟨atJump⟩⟩ := X86PlacedScalar.rex_immediate
    (X86PlacedFrameAddress.nativeBase other) extra vector (show At image b base (start + 10) from atRestore)
    (by omega) 14 2 placed.restore
  obtain ⟨after, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 16) from atJump) placed.jump
  have done := X86StateFrame.registerOnly (resetFrame.trans jumpFrame)
  have frame : X86StateFrame.Frame clobbers (footprint (layout.header.cell 0).address) before after :=
    ((registerOnly.trans storeFrame).trans done).mono (by decide) (by simp)
  have first := X86FuelPrefix.fetches_then 1 1 before a b moved ranStore
  have arrival := X86FuelPrefix.fetches_then 3 1 before c after (X86FuelPrefix.fetches_then 2 1 before b c first reset) jumped
  refine ⟨after, arrival, frame, ⟨records.fits, visible.preserved done (by simp), ?_⟩,
    (jumpFrame.lookup 14 (by decide)).trans app, endpoint⟩
  intro index field
  exact (records.node index field).preserved frame (layout.header_apart _ _).symm

end Mettapedia.Machines.TIsa.StoreInstructions.NativeAgendaPublish
