import Mettapedia.Machines.TIsa.X86SubImmediate
import Mettapedia.Machines.TIsa.X86DwordLoad

/-!
# Original fetched SETE and byte zero-extension

Both complete generated handler bodies are retained from the pinned model.
SETE writes the low byte of R11; MOVZX then removes all dependence on its
previous upper bits. Register reads, writes, instruction lengths, prefix
selection and the complete four-byte fetch paths use the original semantics.
The frames preserve memory, flags and all other general registers.

Shared REX escape and ModRM decoding contracts live in the existing fetch
and two-byte dispatch modules. Complete template/source/ABI joins remain
separate obligations.
-/

set_option autoImplicit false

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/ConditionalByteFunctions.lean.inc"
  sha256 "38a5321151c753b6c42ebcd0811d26fc5de141b53721ad14e7a291151653b940"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86ConditionByte

open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

def replaceByte (old : Word) (byte : BitVec 8) : Word := Functions.changeSlice_bits old 0 8 byte
def bitByte (value : Bool) : BitVec 8 := if value then 1 else 0

theorem replaceByte_low (old : Word) (byte : BitVec 8) :
    Sail.BitVec.truncate (replaceByte old byte) 8 = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [replaceByte, Functions.changeSlice_bits, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', Sail.BitVec.truncate, within]

theorem read_byte (state : State) (old : Word) (rex : BitVec 8)
    (present : lookup state 11 = some old) (extended : rex ≠ (0#8)) :
    (Functions.rr08 (11#4) rex).run state = .ok (Sail.BitVec.truncate old 8) state := by
  unfold Functions.rr08
  rw [show Sail.BitVec.toNatInt (11#4) = 11 from rfl,
    show (rex == (0#8)) = false from beq_eq_false_iff_ne.mpr extended]
  simp only [Bool.not_false, Bool.true_or, ite_true]
  simp only [show Int.toNat (11 : Int) = 11 from rfl]
  have read := rgfi_exact state 11 old present
  change (Functions.rgfi ((11 : Nat) : Int)).run state = .ok old state at read
  rw [run_bind, read]
  rfl

theorem write_byte (state : State) (old : Word) (byte : BitVec 8) (rex : BitVec 8)
    (present : lookup state 11 = some old) (extended : rex ≠ (0#8))
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.wr08 (11#4) rex byte).run state = .ok () (put state 11 (replaceByte old byte)) := by
  unfold Functions.wr08
  rw [show Sail.BitVec.toNatInt (11#4) = 11 from rfl,
    show (rex == (0#8)) = false from beq_eq_false_iff_ne.mpr extended]
  simp only [Bool.not_false, Bool.true_or, ite_true]
  simp only [show Int.toNat (11 : Int) = 11 from rfl]
  have read := rgfi_exact state 11 old present
  change (Functions.rgfi ((11 : Nat) : Int)).run state = .ok old state at read
  rw [run_bind, read]
  dsimp only
  rw [X86Alu.full_extract]
  exact write_rgfi_exact state 11 (replaceByte old byte) quiet

theorem write_operand_byte (state : State) (old : Word) (byte : BitVec 8) (prefixes : BitVec 52)
    (present : lookup state 11 = some old)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 1 true false (byte.zeroExtend 128)
      3 (0#64) prefixes (0x41#8) (3#3) (3#2) (0#8)).run state =
        .ok () (put state 11 (replaceByte old byte)) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show Functions.reg_index (3#3) (0x41#8) (0#2) = (11#4) from rfl, ite_true]
  unfold Functions.write_rgfi_size
  simp only [Functions.eq_bits_nat, Sail.BitVec.toNatInt]
  change (Functions.wr08 (11#4) (0x41#8)
    (Sail.BitVec.truncate (Sail.BitVec.truncate (byte.zeroExtend 128) 64) 8)).run state = _
  have low : Sail.BitVec.truncate (Sail.BitVec.truncate (byte.zeroExtend 128) 64) 8 = byte := by
    change ((byte.setWidth 128).setWidth 64).setWidth 8 = byte
    rw [BitVec.setWidth_setWidth_of_le byte (by decide : 64 ≤ 128),
      BitVec.setWidth_setWidth_of_le byte (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  rw [low]
  exact write_byte state old byte (0x41#8) present (by decide) quiet

theorem sete_predicate :
    Functions.jcc_cmovcc_setcc_spec (0x94#8) =
      Functions.jcc_cmovcc_setcc_spec (X86BranchCondition.opcode .zero) := by rfl

theorem sete_handler (state : State) (start finish : BitVec 48) (prefixes : BitVec 52)
    (old : Word) (flags : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (length : Functions.check_instruction_length start finish (0#3) = none)
    (known : lookup state 11 = some old)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_setcc .Mode_64bit start finish prefixes (0x41#8) (0x94#8) (0xc3#8) (0#8)).run state =
      .ok () (X86Move.putPointer
        (put state 11 (replaceByte old (bitByte (X86BranchCondition.value .zero flags)))) finish) := by
  unfold Functions.x86_setcc
  dsimp only
  simp only [show Functions._get_modr_m_mod (0xc3#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xc3#8) = (3#3) from rfl,
    show ((3#2) == (3#2)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int 0 3 = (0#3) from rfl,
    show Sail.BitVec.zeroExtend (0#3) 48 = (0#48) from rfl,
    run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [run_bind, sete_predicate, X86BranchCondition.executes .zero state flags flagsKnown]
  dsimp only
  rw [X86MovePrefix.segment64 prefixes (3#3) (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Functions.bits_of_int (if X86BranchCondition.value .zero flags then 1 else 0) 128 =
      (bitByte (X86BranchCondition.value .zero flags)).zeroExtend 128 from by
    cases X86BranchCondition.value .zero flags <;> rfl]
  rw [run_bind, write_operand_byte state old _ prefixes known quiet]
  change (Functions.write_iptr .Mode_64bit finish).run _ = _
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

theorem read_sized_byte (state : State) (old : Word) (rex : BitVec 8)
    (known : lookup state 11 = some old) (extended : rex ≠ (0#8)) :
    (Functions.rgfi_size (1#4) (11#4) rex).run state =
      .ok ((Sail.BitVec.truncate old 8).zeroExtend 64) state := by
  unfold Functions.rgfi_size
  simp only [show Functions.eq_bits_nat (1#4) 1 = true from rfl, ite_true]
  rw [run_bind, read_byte state old rex known extended]
  rfl

theorem byte_operand (state : State) (old : Word) (byte : BitVec 8)
    (prefixes : BitVec 52) (pointer : BitVec 48)
    (known : lookup state 11 = some old) (low : Sail.BitVec.truncate old 8 = byte) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 1 true false 3
      prefixes pointer (0x45#8) (3#3) (3#2) (0#8) (0#3)).run state =
      .ok (byte.zeroExtend 128, (0 : Int), (0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int ((1 : Nat) : Int) 4 = (1#4) from rfl,
    show Functions.reg_index (3#3) (0x45#8) (0#2) = (11#4) from rfl,
    run_bind, run_bind, read_sized_byte state old (0x45#8) known (by decide), low]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (byte.zeroExtend 64) 128 = byte.zeroExtend 128 from by
    change (byte.setWidth 64).setWidth 128 = byte.setWidth 128
    exact BitVec.setWidth_setWidth (by decide)]
  rfl

theorem write_zero_byte (state : State) (byte : BitVec 8)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (4#4) (11#4) (byte.zeroExtend 64) (0x45#8)).run state =
      .ok () (put state 11 (byte.zeroExtend 64)) := by
  unfold Functions.write_rgfi_size
  simp only [Functions.eq_bits_nat, Sail.BitVec.toNatInt]
  change (Functions.wr32 (11#4) (Sail.BitVec.truncate (byte.zeroExtend 64) 32)).run state = _
  have cut : Sail.BitVec.truncate (byte.zeroExtend 64) 32 = byte.zeroExtend 32 := by
    change (byte.setWidth 64).setWidth 32 = byte.setWidth 32
    exact BitVec.setWidth_setWidth_of_le byte (by decide)
  rw [cut]
  have result := wr32_exact state 11 (byte.zeroExtend 32) quiet
  change (Functions.wr32 (11#4) (byte.zeroExtend 32)).run state =
    .ok () (put state 11 ((byte.zeroExtend 32).zeroExtend 64)) at result
  have widen : (byte.zeroExtend 32).zeroExtend 64 = byte.zeroExtend 64 := by
    change (byte.setWidth 32).setWidth 64 = byte.setWidth 64
    exact BitVec.setWidth_setWidth (by decide)
  simpa only [widen] using result

theorem movzx_handler (state : State) (start finish : BitVec 48) (prefixes : BitVec 52)
    (old : Word) (byte : BitVec 8)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (length : Functions.check_instruction_length start finish (0#3) = none)
    (known : lookup state 11 = some old) (low : Sail.BitVec.truncate old 8 = byte)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_movzx .Mode_64bit start finish prefixes (0x45#8) (0xb6#8) (0xdb#8) (0#8)).run state =
      .ok () (X86Move.putPointer (put state 11 (byte.zeroExtend 64)) finish) := by
  unfold Functions.x86_movzx
  dsimp only
  rw [show Functions._get_modr_m_mod (0xdb#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xdb#8) = (3#3) from rfl,
    X86MovePrefix.segment64 prefixes (3#3) (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  simp only [show ((0xb6#8) == (0xb6#8)) = true from rfl, ite_true,
    show Int.toNat (1 : Int) = 1 from rfl]
  rw [run_bind, byte_operand state old byte prefixes finish known low]
  dsimp only
  rw [show Functions.bits_of_int 0 3 = (0#3) from rfl,
    show Sail.BitVec.zeroExtend (0#3) 48 = (0#48) from rfl,
    run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,
    Bool.false_eq_true, ite_false]
  have size := X86DwordLoad.operand_size32 (11 : Fin 16) 11 prefixes operandOverride
  change Functions.select_operand_size .Mode_64bit false (0x45#8) false prefixes
    false false false = (pure 4 : SailM Int) at size
  rw [size, run_bind, run_pure]
  dsimp only
  rw [show Functions.bits_of_int 4 4 = (4#4) from rfl,
    show Functions._get_modr_m_reg (0xdb#8) = (3#3) from rfl,
    show Functions.reg_index (3#3) (0x45#8) (2#2) = (11#4) from rfl]
  have cut : Sail.BitVec.truncate (byte.zeroExtend 128) 64 = byte.zeroExtend 64 := by
    change (byte.setWidth 128).setWidth 64 = byte.setWidth 64
    exact BitVec.setWidth_setWidth_of_le byte (by decide)
  rw [cut, run_bind, write_zero_byte state byte quiet]
  change (Functions.write_iptr .Mode_64bit finish).run _ = _
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

noncomputable abbrev byteHandlers (other : OtherTwoByteHandlers) : OtherTwoByteHandlers :=
  { other with x86_setcc := Functions.x86_setcc, x86_movzx := Functions.x86_movzx }

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (X86FrameIncrement.linkedHandlers other) (byteHandlers extra)

theorem fetched_sete (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48) (old : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 1 = finish.toInt)
    (known : lookup state 11 = some old) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x41#8))
    (escapeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x0f#8))
    (opcodeByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x94#8))
    (modrmByte : state.mem.get? (origin.next.signExtend 52).toNat = some (0xc3#8)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put state 11 (replaceByte old (bitByte (X86BranchCondition.value .zero flags)))) finish) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rw [X86EscapeFetch.fetch_to_rex_escape state origin.address origin.opcodeAddress origin.modrmAddress origin.control origin.attributes
    false 0 11 origin.step1 origin.step2 origin.status origin.fault origin.msrs origin.segments origin.longMode
    origin.codeMode origin.application origin.rip rexByte escapeByte]
  change (@Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary (X86FrameIncrement.linkedHandlers other)
    (byteHandlers extra) .Mode_64bit origin.address origin.modrmAddress (X86LegacyFetch.packet (0x0f#8))
      (0x41#8) (0x0f#8)).run state = _
  rw [@X86TwoByteDispatch.decode_register (X86FrameIncrement.linkedHandlers other) (byteHandlers extra) state origin.address
    origin.modrmAddress origin.next finish origin.attributes (origin.address.signExtend 64) (0x41#8) (0x94#8) (0xc3#8)
    origin.step3 advance (by rfl) (by rfl) (by decide) origin.segments origin.application origin.rip opcodeByte modrmByte,
    @X86TwoByteDispatch.select_sete (X86FrameIncrement.linkedHandlers other) (byteHandlers extra)]
  apply sete_handler state origin.address finish (X86LegacyFetch.packet (0x0f#8)) old flags
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
  · apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · exact known
  · exact flagsKnown
  · exact quiet

theorem fetched_movzx (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48) (old : Word) (byte : BitVec 8)
    (advance : origin.next.toInt + 1 = finish.toInt)
    (known : lookup state 11 = some old) (low : Sail.BitVec.truncate old 8 = byte)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x45#8))
    (escapeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x0f#8))
    (opcodeByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0xb6#8))
    (modrmByte : state.mem.get? (origin.next.signExtend 52).toNat = some (0xdb#8)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 11 (byte.zeroExtend 64)) finish) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rw [X86EscapeFetch.fetch_to_rex_escape state origin.address origin.opcodeAddress origin.modrmAddress origin.control origin.attributes
    false 11 11 origin.step1 origin.step2 origin.status origin.fault origin.msrs origin.segments origin.longMode
    origin.codeMode origin.application origin.rip rexByte escapeByte]
  change (@Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary (X86FrameIncrement.linkedHandlers other)
    (byteHandlers extra) .Mode_64bit origin.address origin.modrmAddress (X86LegacyFetch.packet (0x0f#8))
      (0x45#8) (0x0f#8)).run state = _
  rw [@X86TwoByteDispatch.decode_register (X86FrameIncrement.linkedHandlers other) (byteHandlers extra) state origin.address
    origin.modrmAddress origin.next finish origin.attributes (origin.address.signExtend 64) (0x45#8) (0xb6#8) (0xdb#8)
    origin.step3 advance (by rfl) (by rfl) (by decide) origin.segments origin.application origin.rip opcodeByte modrmByte,
    @X86TwoByteDispatch.select_movzx (X86FrameIncrement.linkedHandlers other) (byteHandlers extra)]
  apply movzx_handler state origin.address finish (X86LegacyFetch.packet (0x0f#8)) old byte
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _)
  · apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · exact known
  · exact low
  · exact quiet

theorem byte_frame (state : State) (value : Word) (finish : BitVec 48) :
    X86Execution.RegisterFrame {.r11,.rip} state (X86Move.putPointer (put state 11 value) finish) := by
  simpa [key] using (X86Execution.put_frame state 11 value).trans (X86Execution.pointer_frame _ finish)

end Mettapedia.Machines.TIsa.X86ConditionByte
