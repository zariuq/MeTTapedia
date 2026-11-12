import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def x86_mov_op_en_oi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-MOV-OP/EN-OI"
  let byte_operand? : Bool :=
    ((176 ≤b (BitVec.toNatInt opcode)) && (((BitVec.toNatInt opcode) ≤b 183) : Bool))
  let operand_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let imm ← (( do
    (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) operand_size
      (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM (BitVec 128) )
  let temp_rip ← (( do (add_to_iptr proc_mode temp_rip (bits_of_int operand_size 48)) ) : SailM
    (sbits 48) )
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let reg : (BitVec 3) := (Sail.BitVec.truncate (0x07#8 &&& opcode) 3)
  (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b00#2)
    (Sail.BitVec.truncate imm 64) rex_byte)
  (write_iptr proc_mode temp_rip)

def x86_mov_op_en_mi (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-MOV-OP/EN-MI"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := (opcode == 0xC6#8)
  let imm_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte true prefixes false false false) ) : SailM
    Int )
  let reg_mem_size : Int :=
    if (((opcode == 0xC7#8) && (logbitp_bits 3 rex_byte)) : Bool)
    then 8
    else imm_size
  let (addr, increment_rip_by) ← (( do
    if ((mod_var == 0b11#2) : Bool)
    then (pure (0x0000000000000000#64, 0))
    else
      (x86_effective_addr proc_mode prefixes temp_rip rex_byte r_m mod_var sib
        (bits_of_int imm_size 3)) ) : SailM ((sbits 64) × Int) )
  let increment_rip_by : (BitVec 3) := (bits_of_int increment_rip_by 3)
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let temp_rip ← (( do
    (add_to_iptr proc_mode temp_rip (Sail.BitVec.zeroExtend increment_rip_by 48)) ) : SailM
    (sbits 48) )
  let imm ← (( do
    (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) imm_size
      (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM (BitVec 128) )
  let temp_rip ← (( do (add_to_iptr proc_mode temp_rip (bits_of_int imm_size 48)) ) : SailM
    (sbits 48) )
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let imm : (BitVec 128) :=
    if ((reg_mem_size == 8) : Bool)
    then (Sail.BitVec.zeroExtend (Sail.BitVec.signExtend (Sail.BitVec.truncate imm 32) 64) 128)
    else imm
  let inst_ac? : Bool := true
  (x86_operand_to_reg_mem proc_mode reg_mem_size inst_ac? false imm seg_reg addr prefixes rex_byte
    r_m mod_var sib)
  (write_iptr proc_mode temp_rip)

end X86Registers.Functions
