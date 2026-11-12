import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def x86_mov_op_en_rm (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-MOV-OP/EN-RM"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := (opcode == 0x8A#8)
  let operand_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let inst_ac? : Bool := true
  let (reg_mem, increment_rip_by, addr) ← (( do
    (x86_operand_from_modr_m_and_sib_bytes proc_mode 0#1 operand_size inst_ac? false seg_reg
      prefixes temp_rip rex_byte r_m mod_var sib 0b000#3) ) : SailM
    ((BitVec 128) × Int × (sbits 64)) )
  let increment_rip_by : (BitVec 3) := (bits_of_int increment_rip_by 3)
  let temp_rip ← (( do
    (add_to_iptr proc_mode temp_rip (Sail.BitVec.zeroExtend increment_rip_by 48)) ) : SailM
    (sbits 48) )
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2)
    (Sail.BitVec.truncate reg_mem 64) rex_byte)
  (write_iptr proc_mode temp_rip)


end X86Registers.Functions
