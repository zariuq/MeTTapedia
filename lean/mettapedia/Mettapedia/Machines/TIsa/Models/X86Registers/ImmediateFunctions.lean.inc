import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let e_byte_operand? : Bool := ((opcode == 0x80#8) || ((opcode == 0x82#8) || (opcode == 0xF6#8)))
  let e_size ← (( do
    (select_operand_size proc_mode e_byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let imm_byte_operand? : Bool :=
    ((opcode == 0x80#8) || ((opcode == 0x82#8) || ((opcode == 0x83#8) || (opcode == 0xF6#8))))
  let imm_size ← (( do
    (check_range 1 4
      (← (select_operand_size proc_mode imm_byte_operand? rex_byte true prefixes false false false)))
    ) : SailM Int )
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let inst_ac? : Bool := true
  let (e, increment_rip_by, e_addr) ← (( do
    (x86_operand_from_modr_m_and_sib_bytes proc_mode 0#1 e_size inst_ac? false seg_reg prefixes
      temp_rip rex_byte r_m mod_var sib (bits_of_int imm_size 3)) ) : SailM
    ((BitVec 128) × Int × (sbits 64)) )
  let temp_rip ← (( do (add_to_iptr proc_mode temp_rip (bits_of_int increment_rip_by 48)) ) :
    SailM (sbits 48) )
  let imm ← (( do
    (pure (Sail.BitVec.truncate
        (← (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) imm_size
            (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false)) 32)) ) : SailM
    (BitVec 32) )
  let imm ← (( do
    (pure (loghead_int (ash_left_int e_size 3)
        (← (binary_logext (ash_left_int imm_size 3) (BitVec.toNatInt imm))))) ) : SailM Int )
  let temp_rip ← (( do
    (pure (Sail.BitVec.signExtend (← (add_to_iptr proc_mode temp_rip (bits_of_int imm_size 48)))
        49)) ) : SailM (sbits 49) )
  let badlength? : (Option Int) :=
    (check_instruction_length start_rip (Sail.BitVec.truncate temp_rip 48) 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let input_rflags ← (( do readReg rflags ) : SailM rflagsbits )
  let (result, output_rflags, undefined_flags) ← (( do
    (gpr_arith_logic_spec e_size operation (Sail.BitVec.truncate e 64) (bits_of_int imm 64)
      input_rflags) ) : SailM ((BitVec 64) × rflagsbits × rflagsbits) )
  if (((operation == 8) || (operation == 7)) : Bool)
  then (pure ())
  else
    (x86_operand_to_reg_mem proc_mode e_size inst_ac? false (Sail.BitVec.zeroExtend result 128)
      seg_reg e_addr prefixes rex_byte r_m mod_var sib)
  (write_user_rflags output_rflags undefined_flags)
  (write_iptr proc_mode (Sail.BitVec.truncate temp_rip 48))

/- Type quantifiers: operation : Nat, 0 ≤ operation ∧ operation ≤ 8 -/
end X86Registers.Functions
