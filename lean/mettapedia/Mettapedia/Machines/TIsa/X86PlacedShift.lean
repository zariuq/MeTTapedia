import Mettapedia.Machines.TIsa.X86PlacedScalar
import Mettapedia.Machines.TIsa.X86Shift

/-! # An immediate shift at a placed instruction boundary -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PlacedShift

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code registerCode)
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (operation : Shift) (destination : Fin 16) (count : BitVec 8) : List Nat :=
  registerCode 0xc1 (X86Shift.extension operation) destination ++ [count.toNat]

private theorem byte {image : NativeImage.View} {state : State} {base : BitVec 48}
    {start : Nat} (point : At image state base start) (inside : start ≤ image.size)
    {code : List Nat} (checked : Code image start code) (index value : Nat) (found : code[index]? = some value) :
    state.mem.get? ((address base.toInt (start + index)).signExtend 52).toNat = some (.ofNat 8 value) := by
  have read := point.bytes start inside code checked index value found
  rwa [point.relative_address start index inside] at read

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {start : Nat}
    (point : At image state base start) (inside : start + 4 ≤ image.size)
    (operation : Shift) (destination : Fin 16) (count : BitVec 8)
    (value : Word) (known : lookup state destination = some value)
    (checked : Code image start (bytes operation destination count)) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame {key destination, .rflags, .rip} state after ∧
      lookup after destination = some (X86Shift.evaluate operation value (count.setWidth 6)) ∧
      Nonempty (At image after base (start + 4)) := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let digit := X86Shift.extension operation
  let origin : X86LegacyFetch.Window state 0xc1 true digit destination :=
    { toBasis := point.basis (by omega)
      prefixByte := by
        have found := byte point (by omega) checked 0 (rex true digit destination).toNat rfl
        simpa only [At.basis, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using found
      opcodeByte := byte point (by omega) checked 1 0xc1 rfl
      modrmByte := by
        have found := byte point (by omega) checked 2 (modRM digit destination).toNat rfl
        simpa only [At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using found }
  let next := address base.toInt (start + 4)
  have advance : origin.next.toInt + 1 = next.toInt := by
    change (address base.toInt (start + 3)).toInt + 1 = (address base.toInt (start + 4)).toInt
    rw [point.location _ (by omega), point.location _ inside]
    omega
  have countRead : state.mem.get? (origin.next.signExtend 52).toNat = some count := by
    simpa only [origin, At.basis, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      byte point (by omega) checked 3 count.toNat rfl
  obtain ⟨output, mask, ran⟩ := X86Shift.fetched other vector operation state destination origin next
    value point.flags count advance known point.knownFlags point.quiet countRead
  let flags := X86MaskedFlags.merged point.flags output mask
  let word := X86Shift.evaluate operation value (count.setWidth 6)
  let after := X86Move.putPointer (put (X86Flags.putFlags state flags) destination word) next
  have frame := X86Shift.result_frame state destination word point.flags output mask next
  have insideData : ({key destination, .rflags, .rip} : Finset Register) ⊆ dataRegisters := by
    intro register member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · exact data_key destination
    · decide
    · decide
  have outside : ∀ reg : Fin 16, Register.rflags ∉ ({key reg} : Finset Register) := by decide
  have flagRead : after.regs.get? .rflags = some flags := by
    unfold after
    rw [(pointer_frame _ _).registers .rflags (by decide), (put_frame _ _ _).registers .rflags (outside destination)]
    simp [X86Flags.putFlags]
  exact ⟨after, X86FuelPrefix.fetches_one _ _ ran, frame, by
    simp only [after, X86Move.lookup_putPointer, lookup_put_same, word],
    ⟨point.advance frame insideData (X86FuelPrefix.pointer_rip _ _) flags flagRead⟩⟩

end Mettapedia.Machines.TIsa.X86PlacedShift
