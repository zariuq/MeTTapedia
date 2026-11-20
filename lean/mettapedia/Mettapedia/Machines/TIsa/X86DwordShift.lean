import Mettapedia.Machines.TIsa.X86Shift32Instruction
import Mettapedia.Machines.TIsa.X86FetchEntry

/-!
# Exact dword shift code at a framed instruction entry

The optional REX prefix, ModRM byte and immediate are read from the supplied
code list. The instruction count is one for either byte length. Source count
admission and carrier normalization remain part of the enclosing template.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86DwordShift
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86FetchEntry X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (operation : Shift) (destination : Fin 16) (count : BitVec 8) : List Nat :=
  if destination.val < 8 then [0xc1,(modRM (X86Shift.extension operation) destination).toNat,count.toNat]
  else [(rex false (X86Shift.extension operation) destination).toNat,0xc1,
    (modRM (X86Shift.extension operation) destination).toNat,count.toNat]

theorem length_bounds (operation : Shift) (destination : Fin 16) (count : BitVec 8) :
    3 ≤ (bytes operation destination count).length ∧ (bytes operation destination count).length ≤ 4 := by
  unfold bytes
  split <;> simp

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (state : State) (destination : Fin 16) (value : Word) (count : BitVec 8)
    (flags : BitVec 32) (origin : Entry state)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes operation destination count).length < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt (bytes operation destination count)) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output mask, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (X86Shift32Instruction.evaluate operation value count))
        (address origin.address.toInt (bytes operation destination count).length)) := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  by_cases low : destination.val < 8
  · have size : (bytes operation destination count).length = 3 := by simp [bytes,low]
    have bound : origin.address.toInt + 3 < (2 ^ 47 : Int) := by simpa [size] using upper
    have present : codeLoaded state origin.address.toInt
        [0xc1,(modRM (X86Shift.extension operation) destination).toNat,count.toNat] := by
      simpa only [bytes,if_pos low] using loaded
    have initial := codeLoaded_left state origin.address.toInt
      [0xc1,(modRM (X86Shift.extension operation) destination).toNat] [count.toNat] present
    let window := origin.bareWindow (0xc1#8) (modRM (X86Shift.extension operation) destination) (by omega) initial
    have immediate : state.mem.get? ((address origin.address.toInt 2).signExtend 52).toNat = some count := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using present 2 count.toNat (by rfl)
    have advance : (address origin.address.toInt 2).toInt + 1 = (address origin.address.toInt 3).toInt := by
      rw [address_toInt origin.address.toInt lower bound 2 (by decide : 2 ≤ 3),
        address_toInt origin.address.toInt lower bound 3 (by decide : 3 ≤ 3)]
      omega
    have run := X86Shift32Instruction.fetched_bare other vector operation state destination low window
      (address origin.address.toInt 3) value flags count advance known flagsKnown quiet immediate
    rw [size]
    exact run
  · have size : (bytes operation destination count).length = 4 := by simp [bytes,low]
    have bound : origin.address.toInt + 4 < (2 ^ 47 : Int) := by simpa [size] using upper
    have present : codeLoaded state origin.address.toInt
        [(rex false (X86Shift.extension operation) destination).toNat,0xc1,
          (modRM (X86Shift.extension operation) destination).toNat,count.toNat] := by
      simpa only [bytes,if_neg low] using loaded
    have initial := codeLoaded_left state origin.address.toInt
      [(rex false (X86Shift.extension operation) destination).toNat,0xc1,
        (modRM (X86Shift.extension operation) destination).toNat] [count.toNat] present
    let window := origin.rexWindow (0xc1#8) false (X86Shift.extension operation) destination (by omega) initial
    have immediate : state.mem.get? ((address origin.address.toInt 3).signExtend 52).toNat = some count := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using present 3 count.toNat (by rfl)
    have advance : (address origin.address.toInt 3).toInt + 1 = (address origin.address.toInt 4).toInt := by
      rw [address_toInt origin.address.toInt lower bound 3 (by decide : 3 ≤ 4),
        address_toInt origin.address.toInt lower bound 4 (by decide : 4 ≤ 4)]
      omega
    have run := X86Shift32Instruction.fetched_rex other vector operation state destination (by omega) window
      (address origin.address.toInt 4) value flags count advance known flagsKnown quiet immediate
    rw [size]
    exact run

#print axioms executes
end Mettapedia.Machines.TIsa.X86DwordShift
