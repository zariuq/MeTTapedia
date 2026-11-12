import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def rme16 (proc_mode : proc_mode) (addr_size : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (r_x : String) (check_alignment? : Bool) : SailM (BitVec 16) := do
  (load_bytes_from_ea proc_mode addr_size 2 eff_addr base_reg seg_reg r_x check_alignment? false)

def read_sptr (proc_mode : proc_mode) : SailM (BitVec 64) := do
  let sptr ← (( do (rgfi 4) ) : SailM (sbits 64) )
  if ((in_64bit_mode proc_mode) : Bool)
  then (pure sptr)
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let ss_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 2)) ) :
            SailM (BitVec 16) )
          let ss_b : (BitVec 1) :=
            (_get_data_segment_descriptor_attributesbits_d_b
              (Mk_data_segment_descriptor_attributesbits ss_attr))
          if ((ss_b == 1#1) : Bool)
          then (pure (Sail.BitVec.zeroExtend (Sail.BitVec.truncate sptr 32) 64))
          else
            (pure (Sail.BitVec.zeroExtend (Sail.BitVec.zeroExtend (Sail.BitVec.truncate sptr 16) 32)
                64)))
      else (pure 0x0000000000000000#64))

def add_to_sptr (proc_mode : proc_mode) (sptr : (BitVec 64)) (delta : (BitVec 64)) : SailM (BitVec 64) := do
  let sptr_plus_delta : (sbits 65) := (bits_of_int ((BitVec.toInt sptr) +i (BitVec.toInt delta)) 65)
  if ((in_64bit_mode proc_mode) : Bool)
  then
    (do
      let sptr_plus_delta : (sbits 64) := (Sail.BitVec.truncate sptr_plus_delta 64)
      if ((← (canonical_address_p (BitVec.toInt sptr_plus_delta))) : Bool)
      then (pure sptr_plus_delta)
      else (x86_model_error ":NON-CANONICAL-STACK-ADDRESS"))
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let ss_limit ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_limits) 2)) ) :
            SailM (BitVec 32) )
          let ss_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 2)) ) :
            SailM (BitVec 16) )
          let ss_b : (BitVec 1) :=
            (_get_data_segment_descriptor_attributesbits_d_b
              (Mk_data_segment_descriptor_attributesbits ss_attr))
          let ss_e : (BitVec 1) :=
            (_get_data_segment_descriptor_attributesbits_e
              (Mk_data_segment_descriptor_attributesbits ss_attr))
          let ss_lower : Int :=
            if ((ss_e == 1#1) : Bool)
            then (1 +i (BitVec.toNatInt ss_limit))
            else 0
          let ss_upper : (BitVec 32) :=
            if ((ss_e == 1#1) : Bool)
            then
              (if ((ss_b == 1#1) : Bool)
              then 0xFFFFFFFF#32
              else 0x0000FFFF#32)
            else ss_limit
          let sptr_plus_delta : (BitVec 32) :=
            if ((ss_b == 1#1) : Bool)
            then (Sail.BitVec.truncate sptr_plus_delta 32)
            else (Sail.BitVec.zeroExtend (Sail.BitVec.truncate sptr_plus_delta 16) 32)
          if ((! ((ss_lower ≤b (BitVec.toNatInt sptr_plus_delta)) && (((BitVec.toNatInt
                     sptr_plus_delta) ≤b (BitVec.toNatInt ss_upper)) : Bool))) : Bool)
          then (x86_model_error ":OUT-OF-SEGMENT-STACK-ADDRESS")
          else (pure ())
          (pure (Sail.BitVec.zeroExtend sptr_plus_delta 64)))
      else (x86_model_error ":UNIMPLEMENTED-PROC-MODE"))

def write_sptr (proc_mode : proc_mode) (sptr : (BitVec 64)) : SailM Unit := do
  if ((in_64bit_mode proc_mode) : Bool)
  then (write_rgfi 4 sptr)
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let ss_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 2)) ) :
            SailM (BitVec 16) )
          let ss_b : (BitVec 1) :=
            (_get_data_segment_descriptor_attributesbits_d_b
              (Mk_data_segment_descriptor_attributesbits ss_attr))
          if ((ss_b == 1#1) : Bool)
          then (write_rgfi 4 (Sail.BitVec.zeroExtend (Sail.BitVec.truncate sptr 32) 64))
          else
            (do
              let rsp_var ← (( do (rgfi 4) ) : SailM (sbits 64) )
              let rsp_new : (sbits 64) :=
                (changeSlice_bits rsp_var 0 16 (Sail.BitVec.truncate sptr 16))
              (write_rgfi 4 rsp_new)))
      else (pure ()))

def x86_push_general_register (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-PUSH-GENERAL-REGISTER"
  let operand_size ← (( do
    (select_operand_size proc_mode false rex_byte false prefixes true false false) ) : SailM Int )
  let rsp_var ← (( do (read_sptr proc_mode) ) : SailM (sbits 64) )
  let new_rsp ← (( do (add_to_sptr proc_mode rsp_var (bits_of_int (Neg.neg operand_size) 64)) ) :
    SailM (sbits 64) )
  let reg : (BitVec 3) := (loghead_bits 3 opcode)
  let sailval ← (( do
    (rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b00#2) rex_byte) ) : SailM
    (BitVec 64) )
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  (wme_size proc_mode (← (select_address_size proc_mode (some prefixes))) operand_size
    (Sail.BitVec.signExtend (Sail.BitVec.truncate new_rsp 48) 64) none 2
    (Sail.BitVec.zeroExtend sailval 128) (← (alignment_checking_enabled_p ())) false)
  (write_sptr proc_mode new_rsp)
  (write_iptr proc_mode temp_rip)

def x86_pop_general_register (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-POP-GENERAL-REGISTER"
  let operand_size ← (( do
    (select_operand_size proc_mode false rex_byte false prefixes true false false) ) : SailM Int )
  let rsp_var ← (( do (read_sptr proc_mode) ) : SailM (sbits 64) )
  let new_rsp ← (( do (add_to_sptr proc_mode rsp_var (bits_of_int operand_size 64)) ) : SailM
    (sbits 64) )
  let sailval ← (( do
    (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) operand_size rsp_var
      none 2 ":R" (← (alignment_checking_enabled_p ())) false) ) : SailM (BitVec 128) )
  let reg : (BitVec 8) := (opcode &&& 0x07#8)
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  (write_sptr proc_mode new_rsp)
  (write_rgfi_size (bits_of_int operand_size 4)
    (reg_index (Sail.BitVec.truncate reg 3) rex_byte 0b00#2) (Sail.BitVec.truncate sailval 64)
    rex_byte)
  (write_iptr proc_mode temp_rip)

def x86_ret (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-RET"
  let rsp_var ← (( do (read_sptr proc_mode) ) : SailM (sbits 64) )
  let operand_size ← (( do
    (check_range 2 8
      (← (select_operand_size proc_mode false rex_byte false (Mk_prefixes 0x0000000000000#52) true
          true true))) ) : SailM Int )
  let new_rsp ← (( do
    if ((opcode == 0xC3#8) : Bool)
    then
      (do
        let new_rsp ← (( do (add_to_sptr proc_mode rsp_var (bits_of_int operand_size 64)) ) :
          SailM (sbits 64) )
        (pure (Sail.BitVec.truncate new_rsp 48)))
    else
      (do
        let imm16 ← (( do
          (rme16 proc_mode (← (select_address_size proc_mode (some prefixes)))
            (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false) ) : SailM (BitVec 16) )
        let new_rsp ← (( do
          (add_to_sptr proc_mode rsp_var (bits_of_int (operand_size +i (BitVec.toNatInt imm16)) 64))
          ) : SailM (sbits 64) )
        (pure (Sail.BitVec.truncate new_rsp 48))) ) : SailM (sbits 48) )
  let badlength? : Bool :=
    ((opcode == 0xC2#8) && (is_some (check_instruction_length start_rip temp_rip 0b010#3)))
  if (badlength? : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let check_alignment? ← (( do (alignment_checking_enabled_p ()) ) : SailM Bool )
  let tos ← (( do
    if ((operand_size == 8) : Bool)
    then
      (rime_size proc_mode (← (select_address_size proc_mode (some prefixes))) operand_size
        rsp_var none 2 ":R" check_alignment? false)
    else
      (pure (Sail.BitVec.truncate
          (← (rme_size proc_mode (← (select_address_size proc_mode (some prefixes)))
              operand_size rsp_var none 2 ":R" check_alignment? false)) 64)) ) : SailM (sbits 64) )
  if ((! (← do
         if ((in_64bit_mode proc_mode) : Bool)
         then (canonical_address_p (BitVec.toInt tos))
         else
           (do
             let cs_limit ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_limits) 1)) ) :
               SailM (BitVec 32) )
             (pure ((0 ≤b (BitVec.toInt tos)) && (((BitVec.toInt tos) ≤b (BitVec.toNatInt
                     cs_limit)) : Bool)))))) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :BAD-RETURN-ADDRESS TOS)")
  else (pure ())
  (write_sptr proc_mode (Sail.BitVec.signExtend new_rsp 64))
  (write_rip (Sail.BitVec.truncate tos 48))

end X86Registers.Functions
