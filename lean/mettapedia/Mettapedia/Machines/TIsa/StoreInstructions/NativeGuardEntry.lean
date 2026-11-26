import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardState

/-!
# Starting a guard at its first occurrence

The entry writes just the cursor and the requested count.
The count is a complete word, not a sign-extended immediate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardEntry

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code)
open NativeArenaGeometry (Region)
open NativeGuardWorkspace (Frame)
open NativeGuardState (Stable Geometry counters)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def ordinalCode : List ℕ := NativeGuardPolicy.encoding.bytes 12 112
def amountCode : List ℕ := NativeGuardPolicy.encoding.bytes 0 120
def emit (target : Word) : List ℕ :=
  NativeGuardOperands.stackCode ++ (X86PlacedWideImmediate.bytes 0 target ++ (ordinalCode ++ amountCode))

theorem emit_size (target : Word) : (emit target).length = 27 := rfl

structure Placed (image : NativeImage.View) (start : ℕ) (target : Word) : Prop where
  extent : start + 27 ≤ image.size
  stack : Code image start NativeGuardOperands.stackCode
  amount : Code image (start + 3) (X86PlacedWideImmediate.bytes 0 target)
  ordinal : Code image (start + 13) ordinalCode
  counter : Code image (start + 20) amountCode

theorem placed_of_emitted (image : NativeImage.View) (start : ℕ) (target : Word)
    (extent : start + 27 ≤ image.size) (code : Code image start (emit target)) :
    Placed image start target := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (NativeGuardOperands.stackCode ++ _) from code)
  obtain ⟨amount, rest⟩ := NativeWords.code_append rest
  obtain ⟨ordinal, counter⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, amount, ordinal, counter⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rsi, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nc ec mc ac tc oc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc} {frame : Frame}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc} {table : Region oc}

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (target : ℕ)
    (code : Placed image start (BitVec.ofNat 64 target))
    (space : Geometry term map frame agenda trail table image base) (source : PackedTerms.Arena) (needle : Word) (handles : Array Word)
    (input : Stable term map frame agenda trail table source needle handles before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (counters frame) before after ∧
      NativeGuardState.State term map frame agenda trail table source needle handles 0 target after ∧
      Nonempty (At image after base (start + 27)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  obtain ⟨a, opened, openedFrame, address, ⟨atAmount⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer input.scratch.stack code.stack
  let literal : NativeWords.Source frame.pointer := .literal (BitVec.ofNat 64 target)
  have first := X86StateFrame.registerOnly openedFrame
  obtain ⟨b, materialized, materializedFrame, amount, ⟨atOrdinal⟩⟩ := literal.fetch
    (handlers other extra) vector NativeGuardPolicy.wire (BitVec.ofNat 64 target) atAmount
    (controls.transport first (by decide)) address rfl (show start + 13 ≤ image.size by omega) code.amount
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at materialized
  have two := first.trans materializedFrame
  obtain ⟨c, initialized, ordinalFrame, cursor, ⟨atCounter⟩⟩ := X86PlacedMemory.stores (handlers other extra) vector
    (show At image b base (start + 13) from atOrdinal) (controls.transport two (by decide))
    NativeGuardPolicy.encoding 12 112 frame.pointer 0 (frame.cell 14)
    ((materializedFrame.lookup 6 (by decide)).trans address) ((two.lookup 12 (by decide)).trans input.scratch.zero)
    (show start + 20 ≤ image.size by omega) code.ordinal space.ordinalCode
  have three := two.trans ordinalFrame
  obtain ⟨after, counted, countFrame, count, endpoint⟩ := X86PlacedMemory.stores (handlers other extra) vector
    (show At image c base (start + 20) from atCounter) (controls.transport three (by decide))
    NativeGuardPolicy.encoding 0 120 frame.pointer (BitVec.ofNat 64 target) (frame.cell 15)
    ((ordinalFrame.lookup 6 (by decide)).trans ((materializedFrame.lookup 6 (by decide)).trans address))
    ((ordinalFrame.lookup 0 (by decide)).trans amount) extent code.counter space.countCode
  have whole : X86StateFrame.Frame clobbers (counters frame) before after :=
    (three.trans countFrame).mono (by decide) (by simp [counters, NativeGuardCursor.ordinalBytes, NativeGuardPolicy.counterBytes])
  have run := X86FuelPrefix.fetches_then 3 1 before c after
    (X86FuelPrefix.fetches_then 2 1 before b c (X86FuelPrefix.fetches_then 1 1 before a b opened materialized) initialized) counted
  exact ⟨after, run, whole,
    ⟨input.afterCounters space whole (by decide) (by decide) (by decide),
      cursor.preserved countFrame (frame.separate_words (by decide)), count⟩, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardEntry
