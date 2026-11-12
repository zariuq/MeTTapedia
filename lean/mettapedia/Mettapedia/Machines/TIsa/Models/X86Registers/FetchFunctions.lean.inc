import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception VectorOpcodeHandlers

def ms (_ : Unit) : SailM Bool := do
  readReg ms_reg


def Mk_vex_prefixes (v : (BitVec 24)) : (BitVec 24) :=
  v


def _update_vex_prefixes_byte0 (v : (BitVec 24)) (x : (BitVec 8)) : (BitVec 24) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_evex_prefixes_byte0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_vex_prefixes_byte1 (v : (BitVec 24)) (x : (BitVec 8)) : (BitVec 24) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_evex_prefixes_byte1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _get_code_segment_descriptor_attributesbits_l (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def Mk_evex_prefixes (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_modr_m (v : (BitVec 8)) : (BitVec 8) :=
  v


def Mk_sib (v : (BitVec 8)) : (BitVec 8) :=
  v


def _get_ia32_eferbits_lma (v : (BitVec 12)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def n64_bit_modep (_ : Unit) : SailM Bool := do
  let ia32_efer ← (( do (pure (Sail.BitVec.truncate (← (read_msr 0)) 12)) ) : SailM (BitVec 12)
    )
  let ia32_efer_lma : (BitVec 1) := (_get_ia32_eferbits_lma (Mk_ia32_eferbits ia32_efer))
  let cs_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 1)) ) : SailM
    (BitVec 16) )
  let cs_l : (BitVec 1) :=
    (_get_code_segment_descriptor_attributesbits_l
      (Mk_code_segment_descriptor_attributesbits cs_attr))
  (pure ((ia32_efer_lma == 1#1) && (cs_l == 1#1)))


def x86_operation_mode (_ : Unit) : SailM proc_mode := do
  if ((← (n64_bit_modep ())) : Bool)
  then (pure Mode_64bit)
  else (pure Mode_Compatibility)


def Mk_prefixes (v : (BitVec 52)) : (BitVec 52) :=
  v


def _get_prefixes_num (v : (BitVec 52)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_prefixes_nxt (v : (BitVec 52)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 51 44)


def read_iptr (proc_mode : proc_mode) : SailM (BitVec 48) := do
  let iptr ← (( do (read_rip ()) ) : SailM (sbits 48) )
  if ((in_64bit_mode proc_mode) : Bool)
  then (pure iptr)
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let cs_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 1)) ) :
            SailM (BitVec 16) )
          let cs_d : (BitVec 1) :=
            (_get_code_segment_descriptor_attributesbits_d
              (Mk_code_segment_descriptor_attributesbits cs_attr))
          if ((cs_d == 1#1) : Bool)
          then (pure (Sail.BitVec.zeroExtend (Sail.BitVec.truncate iptr 32) 48))
          else
            (pure (Sail.BitVec.zeroExtend (Sail.BitVec.zeroExtend (Sail.BitVec.truncate iptr 16) 32)
                48)))
      else (pure 0x000000000000#48))


def n64_bit_mode_one_byte_opcode_modr_m_p (opcode : (BitVec 8)) : Bool :=
  (GetElem?.getElem!
    (#v[true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, true, true, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true] : (Vector Bool 256))
    (BitVec.toNatInt opcode))


def n32_bit_mode_one_byte_opcode_modr_m_p (opcode : (BitVec 8)) : Bool :=
  (GetElem?.getElem!
    (#v[true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, false, false, false, true, true] : (Vector Bool 256))
    (BitVec.toNatInt opcode))


def one_byte_opcode_modr_m_p (proc_mode : proc_mode) (opcode : (BitVec 8)) : Bool :=
  if ((in_64bit_mode proc_mode) : Bool)
  then (n64_bit_mode_one_byte_opcode_modr_m_p opcode)
  else (n32_bit_mode_one_byte_opcode_modr_m_p opcode)


def x86_decode_sib_p (modr_m : (BitVec 8)) (n16_bit_addressp : Bool) : Bool :=
  ((! n16_bit_addressp) && (let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
    let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
    ((r_m == 0b100#3) && (! (mod_var == 0b11#2)))))


noncomputable def x86_fetch_decode_execute (_ : Unit) : SailM Unit := do
  let ctx : String := "x86-fetch-decode-execute"
  if (((← (ms ())) || (← (fault ()))) : Bool)
  then (pure ())
  else
    (do
      let proc_mode ← (( do (x86_operation_mode ()) ) : SailM proc_mode )
      let n64_bit_modep_var : Bool := (in_64bit_mode proc_mode)
      let start_rip ← (( do (read_iptr proc_mode) ) : SailM (sbits 48) )
      let (prefixes, rex_byte) ← (( do
        (get_prefixes proc_mode start_rip (Mk_prefixes 0x0000000000000#52) 0x00#8 15) ) : SailM
        (prefixes × (BitVec 8)) )
      let prefixes : X86Registers.prefixes := (Mk_prefixes prefixes)
      let opcode_vex_evex_byte : (BitVec 8) := (_get_prefixes_nxt prefixes)
      let prefix_length : (BitVec 4) := (_get_prefixes_num prefixes)
      let temp_rip ← (( do
        (add_to_iptr proc_mode start_rip (bits_of_int (1 +i (BitVec.toNatInt prefix_length)) 48)) )
        : SailM (sbits 48) )
      let vex_byte0? : Bool :=
        ((opcode_vex_evex_byte == 0xC5#8) || (opcode_vex_evex_byte == 0xC4#8))
      let les_lds_distinguishing_byte ← (( do
        if (vex_byte0? : Bool)
        then
          (rme08 proc_mode (← (select_address_size proc_mode (some prefixes)))
            (Sail.BitVec.signExtend temp_rip 64) none 1 ":X")
        else (pure 0x00#8) ) : SailM (BitVec 8) )
      if ((vex_byte0? && (n64_bit_modep_var || ((! n64_bit_modep_var) && ((Sail.BitVec.extractLsb
                   (les_lds_distinguishing_byte : (BitVec 8)) 7 6) == 0b11#2)))) : Bool)
      then
        (do
          let temp_rip ← (( do (add_to_iptr proc_mode temp_rip 0x000000000001#48) ) : SailM
            (sbits 48) )
          let vex_prefixes : X86Registers.vex_prefixes :=
            (_update_vex_prefixes_byte0 (Mk_vex_prefixes 0x000000#24) opcode_vex_evex_byte)
          let vex_prefixes : X86Registers.vex_prefixes :=
            (_update_vex_prefixes_byte1 vex_prefixes (les_lds_distinguishing_byte : (BitVec 8)))
          (vex_decode_and_execute proc_mode start_rip temp_rip prefixes rex_byte vex_prefixes))
      else
        (do
          let opcode_evex_byte : (BitVec 8) := opcode_vex_evex_byte
          let evex_byte0? : Bool := (opcode_evex_byte == 0x62#8)
          let bound_distinguishing_byte ← (( do
            if (evex_byte0? : Bool)
            then
              (rme08 proc_mode (← (select_address_size proc_mode (some prefixes)))
                (Sail.BitVec.signExtend temp_rip 64) none 1 ":X")
            else (pure 0x00#8) ) : SailM (BitVec 8) )
          if ((evex_byte0? && (n64_bit_modep_var || ((! n64_bit_modep_var) && ((Sail.BitVec.extractLsb
                       bound_distinguishing_byte 7 6) == 0b11#2)))) : Bool)
          then
            (do
              let temp_rip ← (( do (add_to_iptr proc_mode temp_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              let evex_prefixes : X86Registers.evex_prefixes :=
                (_update_evex_prefixes_byte0 (Mk_evex_prefixes 0x00000000#32) opcode_evex_byte)
              let evex_prefixes : X86Registers.evex_prefixes :=
                (_update_evex_prefixes_byte1 evex_prefixes bound_distinguishing_byte)
              (evex_decode_and_execute proc_mode start_rip temp_rip prefixes rex_byte evex_prefixes))
          else
            (do
              let opcode_byte : (BitVec 8) := opcode_evex_byte
              let modr_m? : Bool := (one_byte_opcode_modr_m_p proc_mode opcode_byte)
              let modr_m ← (( do
                if (modr_m? : Bool)
                then
                  (do
                    if ((vex_byte0? || evex_byte0?) : Bool)
                    then (pure (Mk_modr_m (les_lds_distinguishing_byte : (BitVec 8))))
                    else
                      (pure (Mk_modr_m
                          (← (rme08 proc_mode
                              (← (select_address_size proc_mode (some prefixes)))
                              (Sail.BitVec.signExtend temp_rip 64) none 1 ":X")))))
                else (pure (Mk_modr_m 0x00#8)) ) : SailM modr_m )
              let temp_rip ← (( do
                if (modr_m? : Bool)
                then (add_to_iptr proc_mode temp_rip 0x000000000001#48)
                else (pure temp_rip) ) : SailM (sbits 48) )
              let sib? ← (( do
                (pure (modr_m? && (← do
                      let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
                      let n16_bit_addressp ← (( do
                        (pure (2 == (← (select_address_size proc_mode (some prefixes))))) ) :
                        SailM Bool )
                      (pure (x86_decode_sib_p modr_m n16_bit_addressp))))) ) : SailM Bool )
              let sib ← (( do
                if (sib? : Bool)
                then
                  (pure (Mk_sib
                      (← (rme08 proc_mode (← (select_address_size proc_mode (some prefixes)))
                          (Sail.BitVec.signExtend temp_rip 64) none 1 ":X"))))
                else (pure (Mk_sib 0x00#8)) ) : SailM sib )
              let temp_rip ← (( do
                if (sib? : Bool)
                then (add_to_iptr proc_mode temp_rip 0x000000000001#48)
                else (pure temp_rip) ) : SailM (sbits 48) )
              (one_byte_opcode_execute proc_mode start_rip temp_rip prefixes rex_byte opcode_byte
                modr_m sib))))


end X86Registers.Functions
