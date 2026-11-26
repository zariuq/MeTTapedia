import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermAppend

/-!
# Selecting an original term during the native remap pass

The loop's word cursor addresses the original initialized prefix,
even when additional records are ready farther into the arena.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionSelect

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def zeroCode : List ℕ := registerCode 0x89 12 0
def emit : List ℕ := zeroCode ++ NativeTermSelection.scaleCode .left

theorem emit_size : emit.length = 11 := rfl

noncomputable abbrev handlers := X86IndexedAddress.handlers
abbrev clobbers : Finset Register := {.rax, .rsi, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (extent : start + 11 ≤ image.size)
    (code : Code image start emit)
    {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {source : PackedTerms.Arena}
    (ready : NativeTermArena.Ready layout source before) (index : Word) (within : index.toNat < source.nodes.size)
    (cursor : lookup before 1 = some index) (pointer : lookup before 3 = some layout.nodes.pointer) (zero : lookup before 12 = some 0) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 6 = some (ready.bank ⟨index.toNat, within⟩).pointer ∧
      Nonempty (At image after base (start + 11)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨cleared, bytes⟩ := NativeWords.code_append (show Code image start
    (zeroCode ++ NativeTermSelection.scaleCode .left) from code)
  obtain ⟨middle, atZero, clearFrame, knownZero, ⟨atScale⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 12 0 0 zero cleared
  obtain ⟨after, scaled, scaleFrame, address, endpoint⟩ := NativeTermSelection.scale_fetched
    other extra vector atScale extent .left layout.nodes.pointer index ((clearFrame.lookup 3 (by decide)).trans pointer)
    knownZero ((clearFrame.lookup 1 (by decide)).trans cursor) bytes
  exact ⟨after, X86FuelPrefix.fetches_then 1 2 before middle after atZero scaled,
    ((X86StateFrame.registerOnly clearFrame).trans scaleFrame).mono (by decide) (by simp),
    (ready.bank_word index within).symm ▸ address, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstitutionSelect
