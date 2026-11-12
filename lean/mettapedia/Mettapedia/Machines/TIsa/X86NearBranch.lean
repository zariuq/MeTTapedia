import Mettapedia.Machines.TIsa.X86BranchCondition
import Mettapedia.Machines.TIsa.X86FrameLoad

/-!
# Original conditional near-branch handler

The retained two-byte Jcc handler checks immediate size and instruction
length, evaluates the original flag predicate, reads a signed disp32 when
taken and writes the canonical destination RIP. Both taken and fallthrough
paths preserve all memory and every register outside RIP. Full escape-byte
decode and native branch-template linkage are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/NearBranchFunctions.lean.inc"
  sha256 "399b357d255faa7d184045d7bb43076bd5fe8fa00b61257567a9551c1101a744"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86NearBranch

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

local instance : MemoryPrimitives := X86Memory.ordinary

theorem operand_size32 (prefixes : BitVec 52) (rex : BitVec 8) :
    Functions.select_operand_size .Mode_64bit false rex false prefixes false true true =
      (pure 4 : SailM Int) := by
  simp [Functions.select_operand_size, Functions.in_64bit_mode]

theorem length_six (start base finish : BitVec 48)
    (first : base.toInt = start.toInt + 2) (advance : base.toInt + 4 = finish.toInt) :
    Functions.check_instruction_length start base (4#3) = none := by
  have startBits := X86Move.bits_of_int48 start
  have baseBits := X86Move.bits_of_int48 base
  have endBits : (Functions.bits_of_int (base.toInt + 4) 49).toInt = finish.toInt := by
    rw [advance, X86Move.bits_of_int49, BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 49)]
  have difference : finish.toInt - start.toInt = 6 := by omega
  simpa [Functions.check_instruction_length, Sail.BitVec.toNatInt, startBits, baseBits,
    show Functions.bits_of_int 4 3 = (4#3) from rfl, endBits, difference] using
    (by decide : (Functions.bits_of_int 6 50).toInt ≤ 15)

theorem delta_exact (displacement : BitVec 32) :
    (Functions.bits_of_int (4 + (displacement.signExtend 64).toInt) 48).toInt = 4 + displacement.toInt := by
  rw [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), X86Alu.bits_of_int_eq]
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · have := BitVec.le_toInt displacement; omega
  · have := BitVec.toInt_lt (x := displacement); omega

theorem handler (condition : X86BranchCondition.Condition) (state : State)
    (start base finish target : BitVec 48) (prefixes : BitVec 52) (rex : BitVec 8)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (first : base.toInt = start.toInt + 2)
    (advance : base.toInt + 4 = finish.toInt)
    (jump : target.toInt = finish.toInt + displacement.toInt)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_two_byte_jcc .Mode_64bit start base prefixes rex (X86BranchCondition.opcode condition)
      (0#8) (0#8)).run state =
        .ok () (X86Move.putPointer state (if X86BranchCondition.value condition flags then target else finish)) := by
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  have codeUpper : base.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := finish)
    omega
  unfold Functions.x86_two_byte_jcc
  rw [operand_size32]
  simp only [pure_bind]
  rw [X86PrefixRead.check_range_ok 0 4 4 (by decide) (by decide)]
  simp only [pure_bind]
  rw [show Functions.bits_of_int 4 3 = (4#3) from rfl, length_six start base finish first advance]
  rw [if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, X86BranchCondition.executes condition state flags flagsKnown]
  dsimp only
  cases chosen : X86BranchCondition.value condition flags with
  | false =>
    rw [if_neg (by decide : ¬false = true)]
    rw [run_bind, X86PrefixRead.add_pointer_checked state base (Functions.bits_of_int 4 48) finish
      (by change base.toInt + 4 = finish.toInt; exact advance)]
    dsimp only
    exact X86Move.write_pointer64 state finish quiet
  | true =>
    rw [if_pos rfl, addressSize]
    simp only [pure_bind]
    rw [show Int.toNat (4 : Int) = 4 from rfl, show Int.toNat (8 : Int) = 8 from rfl,
      show Sail.BitVec.signExtend base 64 = base.signExtend 64 from rfl, run_bind,
      X86ReadWords.signed_displacement_exact state base attributes pointer displacement codeUpper
        segments application rip present]
    dsimp only
    rw [run_bind, X86PrefixRead.add_pointer_checked state base
      (Functions.bits_of_int (4 + (displacement.signExtend 64).toInt) 48) target
      (by rw [delta_exact]; omega)]
    dsimp only
    exact X86Move.write_pointer64 state target quiet

namespace Controls

private def attributes : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)

private def mapped (flags : BitVec 32) (displacement : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true
  let registers := registers.insert .rip (0x4000#64)
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .rflags flags
  let registers := registers.insert .log_register_writes false
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 16384 (0x0f#8)
  let memory := memory.insert 16385 (0x83#8)
  let memory := memory.insert 16386 (displacement.extractLsb' 0 8)
  let memory := memory.insert 16387 (displacement.extractLsb' 8 8)
  let memory := memory.insert 16388 (displacement.extractLsb' 16 8)
  let memory := memory.insert 16389 (displacement.extractLsb' 24 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private theorem run_branch (flags : BitVec 32) (displacement : BitVec 32) (target : BitVec 48)
    (jump : target.toInt = (16390 : Int) + displacement.toInt) :
    (Functions.x86_two_byte_jcc .Mode_64bit (0x4000#48) (0x4002#48) (0#52) (0#8) (0x83#8)
      (0#8) (0#8)).run (mapped flags displacement) =
        .ok () (X86Move.putPointer (mapped flags displacement)
          (if X86BranchCondition.value .aboveEqual flags then target else (0x4006#48))) := by
  apply handler .aboveEqual (mapped flags displacement) (0x4000#48) (0x4002#48) (0x4006#48) target
    (0#52) (0#8) attributes (0x4000#64) flags displacement (by decide) (by decide)
    jump (by decide)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped])
  intro index within
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem forward_taken :
    (Functions.x86_two_byte_jcc .Mode_64bit (0x4000#48) (0x4002#48) (0#52) (0#8) (0x83#8)
      (0#8) (0#8)).run (mapped (0#32) (16#32)) =
        .ok () (X86Move.putPointer (mapped (0#32) (16#32)) (0x4016#48)) :=
  run_branch (0#32) (16#32) (0x4016#48) (by decide)

theorem backward_taken :
    (Functions.x86_two_byte_jcc .Mode_64bit (0x4000#48) (0x4002#48) (0#52) (0#8) (0x83#8)
      (0#8) (0#8)).run (mapped (0#32) (0xfffffff0#32)) =
        .ok () (X86Move.putPointer (mapped (0#32) (0xfffffff0#32)) (0x3ff6#48)) :=
  run_branch (0#32) (0xfffffff0#32) (0x3ff6#48) (by decide)

theorem falls_through :
    (Functions.x86_two_byte_jcc .Mode_64bit (0x4000#48) (0x4002#48) (0#52) (0#8) (0x83#8)
      (0#8) (0#8)).run (mapped (1#32) (16#32)) =
        .ok () (X86Move.putPointer (mapped (1#32) (16#32)) (0x4006#48)) :=
  run_branch (1#32) (16#32) (0x4016#48) (by decide)

theorem changed_displacement_refuses_forward_target :
    (Functions.x86_two_byte_jcc .Mode_64bit (0x4000#48) (0x4002#48) (0#52) (0#8) (0x83#8)
      (0#8) (0#8)).run (mapped (0#32) (0xfffffff0#32)) ≠
        .ok () (X86Move.putPointer (mapped (0#32) (0xfffffff0#32)) (0x4016#48)) := by
  rw [backward_taken]
  intro wrong
  have same := congrArg (fun state : State => state.regs.get? .rip) (EStateM.Result.ok.inj wrong).2
  simp [X86Move.putPointer] at same

end Controls
end Mettapedia.Machines.TIsa.X86NearBranch

#print axioms Mettapedia.Machines.TIsa.X86NearBranch.handler
#print axioms Mettapedia.Machines.TIsa.X86NearBranch.Controls.forward_taken
#print axioms Mettapedia.Machines.TIsa.X86NearBranch.Controls.changed_displacement_refuses_forward_target
