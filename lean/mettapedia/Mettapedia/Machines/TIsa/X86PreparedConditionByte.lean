import Mettapedia.Machines.TIsa.X86ConditionByte
import Mettapedia.Machines.TIsa.X86NativeJcc

/-!
# Materializing a p1 comparison with SETcc and MOVZX

Both emitter instructions force a REX prefix, so every destination
uses its own low byte. The generated Sail handlers first write that
byte and then zero-extend it back into the same register.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86PreparedConditionByte

open _root_.X86Registers X86RegisterRefinement
open X86RegisterEncoding (rex modRM)
open X86ConditionByte (bitByte replaceByte)
local instance : MemoryPrimitives := X86Memory.ordinary

private theorem register_number (register : Fin 16) :
    Sail.BitVec.toNatInt (BitVec.ofNat 4 register.val) = (register.val : Int) := by
  simp [Sail.BitVec.toNatInt]

theorem byte_read (state : State) (register : Fin 16) (old : Word) (rexByte : BitVec 8)
    (present : lookup state register = some old) (extended : rexByte ≠ 0#8) :
    (Functions.rr08 (.ofNat 4 register.val) rexByte).run state =
      .ok (Sail.BitVec.truncate old 8) state := by
  unfold Functions.rr08
  rw [register_number, show (rexByte == (0#8)) = false from beq_eq_false_iff_ne.mpr extended]
  simp only [Bool.not_false, Bool.true_or, ite_true]
  simp only [show (register.val : Int).toNat = register.val by omega]
  rw [run_bind, rgfi_exact state register old present]
  rfl

theorem byte_write (state : State) (register : Fin 16) (old : Word) (byte : BitVec 8) (rexByte : BitVec 8)
    (present : lookup state register = some old) (extended : rexByte ≠ 0#8)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.wr08 (.ofNat 4 register.val) rexByte byte).run state =
      .ok () (put state register (replaceByte old byte)) := by
  unfold Functions.wr08
  rw [register_number, show (rexByte == (0#8)) = false from beq_eq_false_iff_ne.mpr extended]
  simp only [Bool.not_false, Bool.true_or, ite_true]
  simp only [show (register.val : Int).toNat = register.val by omega]
  rw [run_bind, rgfi_exact state register old present]
  dsimp only
  rw [X86Alu.full_extract]
  exact write_rgfi_exact state register (replaceByte old byte) quiet

private theorem forced_rex (a b : Fin 16) : rex false a b ≠ 0#8 := by
  revert a b
  decide

def setOpcode (condition : X86NativeJcc.Condition) : BitVec 8 :=
  X86NativeJcc.opcode condition + 0x10#8

theorem set_predicate (condition : X86NativeJcc.Condition) :
    Functions.jcc_cmovcc_setcc_spec (setOpcode condition) =
      Functions.jcc_cmovcc_setcc_spec (X86NativeJcc.opcode condition) := by
  cases condition with
  | ordinary code => exact X86ConditionByte.setcc_predicate code
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

private theorem to_low_byte (state : State) (register : Fin 16) (old : Word) (byte : BitVec 8)
    (prefixes : BitVec 52) (present : lookup state register = some old)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 1 true false (byte.zeroExtend 128)
      3 (0#64) prefixes (rex false 0 register) (Functions._get_modr_m_r_m (modRM 0 register))
      (3#2) (0#8)).run state = .ok () (put state register (replaceByte old byte)) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((3#2) == (3#2)) = true from rfl, ite_true,
    X86RegisterEncoding.destination_register]
  unfold Functions.write_rgfi_size
  simp only [Functions.eq_bits_nat, Sail.BitVec.toNatInt]
  change (Functions.wr08 (.ofNat 4 register.val) (rex false 0 register)
    (Sail.BitVec.truncate (Sail.BitVec.truncate (byte.zeroExtend 128) 64) 8)).run state = _
  have low : Sail.BitVec.truncate (Sail.BitVec.truncate (byte.zeroExtend 128) 64) 8 = byte := by
    change ((byte.setWidth 128).setWidth 64).setWidth 8 = byte
    rw [BitVec.setWidth_setWidth_of_le byte (by decide : 64 ≤ 128),
      BitVec.setWidth_setWidth_of_le byte (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  rw [low]
  exact byte_write state register old byte _ present (forced_rex _ _) quiet

theorem setcc_handler (condition : X86NativeJcc.Condition) (state : State) (register : Fin 16)
    (start finish : BitVec 48) (prefixes : BitVec 52) (old : Word) (flags : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = 0#8)
    (addressOverride : Functions._get_prefixes_adr prefixes = 0#8)
    (length : Functions.check_instruction_length start finish 0#3 = none)
    (known : lookup state register = some old) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_setcc .Mode_64bit start finish prefixes (rex false 0 register)
      (setOpcode condition) (modRM 0 register) (0#8)).run state =
      .ok () (X86Move.putPointer
        (put state register (replaceByte old (bitByte (X86NativeJcc.selects condition flags)))) finish) := by
  unfold Functions.x86_setcc
  dsimp only
  simp only [X86RegisterEncoding.register_mode, show ((3#2) == (3#2)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int 0 3 = (0#3) from rfl,
    show Sail.BitVec.zeroExtend (0#3) 48 = (0#48) from rfl,
    run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [run_bind, set_predicate, X86NativeJcc.condition_reads state condition flags flagsKnown]
  dsimp only
  rw [X86MovePrefix.segment64 prefixes _ (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Functions.bits_of_int (if X86NativeJcc.selects condition flags then 1 else 0) 128 =
      (bitByte (X86NativeJcc.selects condition flags)).zeroExtend 128 from by
    cases X86NativeJcc.selects condition flags <;> rfl]
  rw [run_bind, to_low_byte state register old _ prefixes known quiet]
  change (Functions.write_iptr .Mode_64bit finish).run _ = _
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

private theorem sized_read (state : State) (register : Fin 16) (old : Word) (rexByte : BitVec 8)
    (known : lookup state register = some old) (extended : rexByte ≠ 0#8) :
    (Functions.rgfi_size (1#4) (.ofNat 4 register.val) rexByte).run state =
      .ok ((Sail.BitVec.truncate old 8).zeroExtend 64) state := by
  unfold Functions.rgfi_size
  simp only [show Functions.eq_bits_nat (1#4) 1 = true from rfl, ite_true]
  rw [run_bind, byte_read state register old rexByte known extended]
  rfl

private theorem from_low_byte (state : State) (register : Fin 16) (old : Word) (byte : BitVec 8)
    (prefixes : BitVec 52) (pointer : BitVec 48)
    (known : lookup state register = some old) (low : Sail.BitVec.truncate old 8 = byte) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 1 true false 3
      prefixes pointer (rex false register register) (Functions._get_modr_m_r_m (modRM register register))
      (3#2) (0#8) (0#3)).run state = .ok (byte.zeroExtend 128, (0 : Int), (0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int ((1 : Nat) : Int) 4 = (1#4) from rfl,
    X86RegisterEncoding.destination_register, run_bind, run_bind,
    sized_read state register old _ known (forced_rex _ _), low]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (byte.zeroExtend 64) 128 = byte.zeroExtend 128 from by
    change (byte.setWidth 64).setWidth 128 = byte.setWidth 128
    exact BitVec.setWidth_setWidth (by decide)]
  rfl

private theorem write_zero_extended (state : State) (register : Fin 16) (byte : BitVec 8)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (4#4) (.ofNat 4 register.val) (byte.zeroExtend 64)
      (rex false register register)).run state = .ok () (put state register (byte.zeroExtend 64)) := by
  unfold Functions.write_rgfi_size
  simp only [Functions.eq_bits_nat, Sail.BitVec.toNatInt]
  change (Functions.wr32 (.ofNat 4 register.val) (Sail.BitVec.truncate (byte.zeroExtend 64) 32)).run state = _
  have cut : Sail.BitVec.truncate (byte.zeroExtend 64) 32 = byte.zeroExtend 32 := by
    change (byte.setWidth 64).setWidth 32 = byte.setWidth 32
    exact BitVec.setWidth_setWidth_of_le byte (by decide)
  rw [cut]
  have widen : (byte.zeroExtend 32).zeroExtend 64 = byte.zeroExtend 64 := by
    change (byte.setWidth 32).setWidth 64 = byte.setWidth 64
    exact BitVec.setWidth_setWidth (by decide)
  simpa only [widen] using wr32_exact state register (byte.zeroExtend 32) quiet

theorem movzx8_handler (state : State) (register : Fin 16) (start finish : BitVec 48) (prefixes : BitVec 52)
    (old : Word) (byte : BitVec 8)
    (segmentOverride : Functions._get_prefixes_seg prefixes = 0#8)
    (addressOverride : Functions._get_prefixes_adr prefixes = 0#8)
    (operandOverride : Functions._get_prefixes_opr prefixes = 0#8)
    (length : Functions.check_instruction_length start finish 0#3 = none)
    (known : lookup state register = some old) (low : Sail.BitVec.truncate old 8 = byte)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_movzx .Mode_64bit start finish prefixes (rex false register register)
      (0xb6#8) (modRM register register) (0#8)).run state =
      .ok () (X86Move.putPointer (put state register (byte.zeroExtend 64)) finish) := by
  unfold Functions.x86_movzx
  dsimp only
  rw [X86RegisterEncoding.register_mode,
    X86MovePrefix.segment64 prefixes _ (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  simp only [show ((0xb6#8) == (0xb6#8)) = true from rfl, ite_true,
    show Int.toNat (1 : Int) = 1 from rfl]
  rw [run_bind, from_low_byte state register old byte prefixes finish known low]
  dsimp only
  rw [show Functions.bits_of_int 0 3 = (0#3) from rfl,
    show Sail.BitVec.zeroExtend (0#3) 48 = (0#48) from rfl,
    run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [X86DwordLoad.operand_size32 register register prefixes operandOverride, run_bind, run_pure]
  dsimp only
  rw [show Functions.bits_of_int 4 4 = (4#4) from rfl, X86RegisterEncoding.source_register]
  have cut : Sail.BitVec.truncate (byte.zeroExtend 128) 64 = byte.zeroExtend 64 := by
    change (byte.setWidth 128).setWidth 64 = byte.setWidth 64
    exact BitVec.setWidth_setWidth_of_le byte (by decide)
  rw [cut, run_bind, write_zero_extended state register byte quiet]
  change (Functions.write_iptr .Mode_64bit finish).run _ = _
  apply X86Move.write_pointer64
  simpa only [diagnostic_put] using quiet

structure RegisterOpcode (state : State) (reg rm : Fin 16) (opcode : BitVec 8)
    extends X86LegacyFetch.Basis state where
  finish : BitVec 48
  advance : next.toInt + 1 = finish.toInt
  prefixByte : state.mem.get? (address.signExtend 52).toNat = some (rex false reg rm)
  escapeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (0x0f#8)
  opcodeByte : state.mem.get? (modrmAddress.signExtend 52).toNat = some opcode
  modrmByte : state.mem.get? (next.signExtend 52).toNat = some (modRM reg rm)

def RegisterOpcode.reframe {before after : State} {reg rm : Fin 16} {opcode : BitVec 8}
    (site : RegisterOpcode before reg rm opcode) (frame : X86Execution.DataFrame before after)
    (rip : after.regs.get? .rip = some (site.address.signExtend 64)) :
    RegisterOpcode after reg rm opcode where
  address := site.address
  opcodeAddress := site.opcodeAddress
  modrmAddress := site.modrmAddress
  next := site.next
  control := site.control
  attributes := site.attributes
  step1 := site.step1
  step2 := site.step2
  step3 := site.step3
  status := (frame.registers .ms_reg (by decide)).trans site.status
  fault := (frame.registers .fault_reg (by decide)).trans site.fault
  msrs := (frame.registers .msrs (by decide)).trans site.msrs
  segments := (frame.registers .seg_hidden_attrs (by decide)).trans site.segments
  longMode := site.longMode
  codeMode := site.codeMode
  application := (frame.registers .app_view (by decide)).trans site.application
  rip := rip
  finish := site.finish
  advance := site.advance
  prefixByte := frame.memory.symm ▸ site.prefixByte
  escapeByte := frame.memory.symm ▸ site.escapeByte
  opcodeByte := frame.memory.symm ▸ site.opcodeByte
  modrmByte := frame.memory.symm ▸ site.modrmByte

private theorem RegisterOpcode.instruction_length {state : State} {reg rm : Fin 16} {opcode : BitVec 8}
    (site : RegisterOpcode state reg rm opcode) :
    Functions.check_instruction_length site.address site.finish (0#3) = none := by
  apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
  have := site.step2
  have := site.step3
  have := site.advance
  omega

private theorem fetch_register (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (reg rm : Fin 16) (opcode : BitVec 8)
    (site : RegisterOpcode state reg rm opcode)
    (mandatory : Functions.compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit opcode
      (X86LegacyFetch.packet (0x0f#8)) = (0#8))
    (modr : Functions.two_byte_opcode_modr_m_p .Mode_64bit (0#8) opcode = true) :
    letI : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
    letI : OtherTwoByteHandlers := X86ConditionByte.byteHandlers extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.two_byte_opcode_execute .Mode_64bit site.address site.finish
        (X86LegacyFetch.packet (0x0f#8)) (0#8) (rex false reg rm) opcode (modRM reg rm) (0#8)).run state := by
  let : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
  let : OtherTwoByteHandlers := X86ConditionByte.byteHandlers extra
  let : VectorOpcodeHandlers := vector
  rw [X86EscapeFetch.fetch_to_rex_escape state site.address site.opcodeAddress site.modrmAddress
    site.control site.attributes false reg rm site.step1 site.step2 site.status site.fault site.msrs
    site.segments site.longMode site.codeMode site.application site.rip site.prefixByte site.escapeByte]
  change (@Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary
    (X86FrameIncrement.linkedHandlers other) (X86ConditionByte.byteHandlers extra)
    .Mode_64bit site.address site.modrmAddress (X86LegacyFetch.packet (0x0f#8))
    (rex false reg rm) (0x0f#8)).run state = _
  exact @X86TwoByteDispatch.decode_register (X86FrameIncrement.linkedHandlers other)
    (X86ConditionByte.byteHandlers extra) state site.address site.modrmAddress site.next site.finish
    site.attributes (site.address.signExtend 64) (rex false reg rm) opcode (modRM reg rm)
    site.step3 site.advance mandatory modr (X86InstructionFetch.no_sib reg rm)
    site.segments site.application site.rip site.opcodeByte site.modrmByte

private theorem set_mandatory (condition : X86NativeJcc.Condition) :
    Functions.compute_mandatory_prefix_for_two_byte_opcode .Mode_64bit (setOpcode condition)
      (X86LegacyFetch.packet (0x0f#8)) = (0#8) := by
  cases condition with
  | ordinary code => cases code <;> rfl
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

private theorem set_has_modrm (condition : X86NativeJcc.Condition) :
    Functions.two_byte_opcode_modr_m_p .Mode_64bit (0#8) (setOpcode condition) = true := by
  cases condition with
  | ordinary code => cases code <;> rfl
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

private theorem dispatch_setcc [OtherOpcodeHandlers] [OtherTwoByteHandlers] (condition : X86NativeJcc.Condition)
    (register : Fin 16) (start finish : BitVec 48) :
    Functions.two_byte_opcode_execute .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
      (0#8) (rex false 0 register) (setOpcode condition) (modRM 0 register) (0#8) =
      OtherTwoByteHandlers.x86_setcc .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
        (rex false 0 register) (setOpcode condition) (modRM 0 register) (0#8) := by
  cases condition with
  | ordinary code => cases code <;> rfl
  | belowEqual | signedLT | signedGE | signedLE | signedGT => rfl

theorem fetched_setcc (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (register : Fin 16)
    (condition : X86NativeJcc.Condition) (site : RegisterOpcode state 0 register (setOpcode condition))
    (old : Word) (flags : BitVec 32)
    (known : lookup state register = some old) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put state register (replaceByte old (bitByte (X86NativeJcc.selects condition flags)))) site.finish) := by
  let : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
  let : OtherTwoByteHandlers := X86ConditionByte.byteHandlers extra
  let : VectorOpcodeHandlers := vector
  rw [fetch_register other extra vector state 0 register _ site (set_mandatory condition) (set_has_modrm condition)]
  rw [dispatch_setcc]
  exact setcc_handler condition state register site.address site.finish _ old flags
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    site.instruction_length known flagsKnown quiet

private theorem dispatch_movzx [OtherOpcodeHandlers] [OtherTwoByteHandlers]
    (register : Fin 16) (start finish : BitVec 48) :
    Functions.two_byte_opcode_execute .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
      (0#8) (rex false register register) (0xb6#8) (modRM register register) (0#8) =
      OtherTwoByteHandlers.x86_movzx .Mode_64bit start finish (X86LegacyFetch.packet (0x0f#8))
        (rex false register register) (0xb6#8) (modRM register register) (0#8) := by rfl

theorem fetched_movzx8 (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (register : Fin 16)
    (site : RegisterOpcode state register register (0xb6#8)) (old : Word) (byte : BitVec 8)
    (known : lookup state register = some old) (low : Sail.BitVec.truncate old 8 = byte)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state register (byte.zeroExtend 64)) site.finish) := by
  let : OtherOpcodeHandlers := X86ConditionByte.handlers other extra
  let : OtherTwoByteHandlers := X86ConditionByte.byteHandlers extra
  let : VectorOpcodeHandlers := vector
  rw [fetch_register other extra vector state register register _ site rfl rfl, dispatch_movzx]
  exact movzx8_handler state register site.address site.finish _ old byte
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _)
    site.instruction_length known low quiet

end Mettapedia.Machines.TIsa.X86PreparedConditionByte
