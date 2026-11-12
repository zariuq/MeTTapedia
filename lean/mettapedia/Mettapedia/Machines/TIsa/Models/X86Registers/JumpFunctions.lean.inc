import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def x86_near_jmp_op_en_d (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-NEAR-JMP-OP/EN-D"
  let byte_operand? : Bool := (opcode == 0xEB#8)
  let offset_size ← (( do
    (check_range 0 4
      (← (select_operand_size proc_mode byte_operand? rex_byte false prefixes false true true))) )
    : SailM Int )
  let offset ← (( do
    (pure (Sail.BitVec.truncate
        (← (rime_size proc_mode (← (select_address_size proc_mode (some prefixes))) offset_size
            (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false)) 32)) ) : SailM (sbits 32)
    )
  let next_rip ← (( do (add_to_iptr proc_mode temp_rip (bits_of_int offset_size 48)) ) : SailM
    (sbits 48) )
  let badlength? : (Option Int) := (check_instruction_length start_rip next_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let temp_rip ← (( do (add_to_iptr proc_mode next_rip (Sail.BitVec.signExtend offset 48)) ) :
    SailM (sbits 48) )
  let temp_rip : (sbits 48) :=
    if ((offset_size == 2) : Bool)
    then (0x00000000FFFF#48 &&& temp_rip)
    else temp_rip
  (write_iptr proc_mode temp_rip)


end X86Registers.Functions
