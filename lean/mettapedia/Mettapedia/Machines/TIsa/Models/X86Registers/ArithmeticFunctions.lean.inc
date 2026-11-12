import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def rz32 (reg : (BitVec 5)) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg zmms) (BitVec.toNatInt reg)) 32))


def rz64 (reg : (BitVec 5)) : SailM (BitVec 64) := do
  (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg zmms) (BitVec.toNatInt reg)) 64))


def rz128 (reg : (BitVec 5)) : SailM (BitVec 128) := do
  (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg zmms) (BitVec.toNatInt reg)) 128))


def rx32 (reg : (BitVec 4)) : SailM (BitVec 32) := do
  (rz32 (Sail.BitVec.zeroExtend reg 5))


def rx64 (reg : (BitVec 4)) : SailM (BitVec 64) := do
  (rz64 (Sail.BitVec.zeroExtend reg 5))


def rx128 (reg : (BitVec 4)) : SailM (BitVec 128) := do
  (rz128 (Sail.BitVec.zeroExtend reg 5))


def xmmi_size (nbytes : (BitVec 5)) (index : (BitVec 4)) : SailM (BitVec 128) := do
  let v_22 := nbytes
  if ((eq_bits_nat v_22 4) : Bool)
  then (pure (Sail.BitVec.zeroExtend (← (rx32 index)) 128))
  else
    (do
      if ((eq_bits_nat v_22 8) : Bool)
      then (pure (Sail.BitVec.zeroExtend (← (rx64 index)) 128))
      else
        (do
          if ((eq_bits_nat v_22 16) : Bool)
          then (rx128 index)
          else (pure 0x00000000000000000000000000000000#128)))

/- Type quantifiers: sailval : Int -/

def cf_spec8 (raw_result : (BitVec 9)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (unsigned_byte_p_int 8 (BitVec.toNatInt raw_result))))))


def cf_spec16 (raw_result : (BitVec 17)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (unsigned_byte_p_int 16 (BitVec.toNatInt raw_result))))))


def cf_spec32 (raw_result : (BitVec 33)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (unsigned_byte_p_int 32 (BitVec.toNatInt raw_result))))))


def of_spec8 (signed_raw_result : (BitVec 9)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (signed_byte_p_int 8 (BitVec.toInt signed_raw_result))))))


def of_spec16 (signed_raw_result : (BitVec 17)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (signed_byte_p_int 16 (BitVec.toInt signed_raw_result))))))


def of_spec32 (signed_raw_result : (BitVec 33)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (signed_byte_p_int 32 (BitVec.toInt signed_raw_result))))))


def pf_spec8 (result : (BitVec 8)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (logbitp_int 0 (logcount_int (BitVec.toNatInt result)))))))


def pf_spec16 (result : (BitVec 16)) : SailM (BitVec 1) := do
  (pure (bool_to_bits
      (! (← (logbitp_int 0 (logcount_int (BitVec.toNatInt (loghead_bits 8 result))))))))


def pf_spec32 (result : (BitVec 32)) : SailM (BitVec 1) := do
  (pure (bool_to_bits
      (! (← (logbitp_int 0 (logcount_int (BitVec.toNatInt (loghead_bits 8 result))))))))


def sf_spec8 (result : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb result 7 7)


def sf_spec16 (result : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb result 15 15)


def sf_spec32 (result : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb result 31 31)


def add_af_spec8 (dst : (BitVec 8)) (src : (BitVec 8)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let add : (BitVec 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) +i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits (15 <b (BitVec.toNatInt add)))


def add_af_spec16 (dst : (BitVec 16)) (src : (BitVec 16)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let add : (BitVec 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) +i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits (15 <b (BitVec.toNatInt add)))


def add_af_spec32 (dst : (BitVec 32)) (src : (BitVec 32)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let add : (BitVec 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) +i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits (15 <b (BitVec.toNatInt add)))


def sub_af_spec8 (dst : (BitVec 8)) (src : (BitVec 8)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sub : (sbits 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) -i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits ((BitVec.toInt sub) <b 0))


def sub_af_spec16 (dst : (BitVec 16)) (src : (BitVec 16)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sub : (sbits 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) -i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits ((BitVec.toInt sub) <b 0))


def sub_af_spec32 (dst : (BitVec 32)) (src : (BitVec 32)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sub : (sbits 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) -i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits ((BitVec.toInt sub) <b 0))


def adc_af_spec8 (dst : (BitVec 8)) (src : (BitVec 8)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let adc : (BitVec 6) :=
    (bits_of_int ((BitVec.toNatInt dst_3_0) +i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt cf)))
      6)
  (bool_to_bits (15 <b (BitVec.toNatInt adc)))


def adc_af_spec16 (dst : (BitVec 16)) (src : (BitVec 16)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let adc : (BitVec 6) :=
    (bits_of_int ((BitVec.toNatInt dst_3_0) +i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt cf)))
      6)
  (bool_to_bits (15 <b (BitVec.toNatInt adc)))


def adc_af_spec32 (dst : (BitVec 32)) (src : (BitVec 32)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let adc : (BitVec 6) :=
    (bits_of_int ((BitVec.toNatInt dst_3_0) +i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt cf)))
      6)
  (bool_to_bits (15 <b (BitVec.toNatInt adc)))


def adc_af_spec64 (dst : (BitVec 64)) (src : (BitVec 64)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let adc : (BitVec 6) :=
    (bits_of_int ((BitVec.toNatInt dst_3_0) +i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt cf)))
      6)
  (bool_to_bits (15 <b (BitVec.toNatInt adc)))


def sbb_af_spec8 (dst : (BitVec 8)) (src : (BitVec 8)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sbb : Int :=
    ((BitVec.toNatInt dst_3_0) -i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt
          (Sail.BitVec.zeroExtend cf 4))))
  (bool_to_bits (sbb <b 0))


def sbb_af_spec16 (dst : (BitVec 16)) (src : (BitVec 16)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sbb : Int :=
    ((BitVec.toNatInt dst_3_0) -i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt
          (Sail.BitVec.zeroExtend cf 4))))
  (bool_to_bits (sbb <b 0))


def sbb_af_spec32 (dst : (BitVec 32)) (src : (BitVec 32)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sbb : Int :=
    ((BitVec.toNatInt dst_3_0) -i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt
          (Sail.BitVec.zeroExtend cf 4))))
  (bool_to_bits (sbb <b 0))


def sbb_af_spec64 (dst : (BitVec 64)) (src : (BitVec 64)) (cf : (BitVec 1)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sbb : Int :=
    ((BitVec.toNatInt dst_3_0) -i ((BitVec.toNatInt src_3_0) +i (BitVec.toNatInt
          (Sail.BitVec.zeroExtend cf 4))))
  (bool_to_bits (sbb <b 0))


def gpr_add_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : (BitVec 9) := (bits_of_int ((BitVec.toNatInt dst) +i (BitVec.toNatInt src)) 9)
  let signed_raw_result : (sbits 9) := (bits_of_int ((BitVec.toInt dst) +i (BitVec.toInt src)) 9)
  let result : (BitVec 8) := (Sail.BitVec.truncate raw_result 8)
  let cf ← (( do (cf_spec8 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (add_af_spec8 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of ← (( do (of_spec8 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_add_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : (BitVec 17) := (bits_of_int ((BitVec.toNatInt dst) +i (BitVec.toNatInt src)) 17)
  let signed_raw_result : (sbits 17) := (bits_of_int ((BitVec.toInt dst) +i (BitVec.toInt src)) 17)
  let result : (BitVec 16) := (Sail.BitVec.truncate raw_result 16)
  let cf ← (( do (cf_spec16 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (add_af_spec16 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of ← (( do (of_spec16 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_add_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : (BitVec 33) := (bits_of_int ((BitVec.toNatInt dst) +i (BitVec.toNatInt src)) 33)
  let signed_raw_result : (sbits 33) := (bits_of_int ((BitVec.toInt dst) +i (BitVec.toInt src)) 33)
  let result : (BitVec 32) := (Sail.BitVec.truncate raw_result 32)
  let cf ← (( do (cf_spec32 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (add_af_spec32 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of ← (( do (of_spec32 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_adc_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let raw_result : (BitVec 9) :=
    (bits_of_int ((BitVec.toNatInt dst) +i ((BitVec.toNatInt src) +i (BitVec.toNatInt input_cf))) 9)
  let signed_raw_result : (sbits 9) :=
    (bits_of_int ((BitVec.toInt dst) +i ((BitVec.toInt src) +i (BitVec.toNatInt input_cf))) 9)
  let result : (BitVec 8) := (Sail.BitVec.truncate raw_result 8)
  let cf ← (( do (cf_spec8 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (adc_af_spec8 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of ← (( do (of_spec8 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_adc_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let raw_result : (BitVec 17) :=
    (bits_of_int ((BitVec.toNatInt dst) +i ((BitVec.toNatInt src) +i (BitVec.toNatInt input_cf))) 17)
  let signed_raw_result : (sbits 17) :=
    (bits_of_int ((BitVec.toInt dst) +i ((BitVec.toInt src) +i (BitVec.toNatInt input_cf))) 17)
  let result : (BitVec 16) := (Sail.BitVec.truncate raw_result 16)
  let cf ← (( do (cf_spec16 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (adc_af_spec16 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of ← (( do (of_spec16 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_adc_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let raw_result : (BitVec 33) :=
    (bits_of_int ((BitVec.toNatInt dst) +i ((BitVec.toNatInt src) +i (BitVec.toNatInt input_cf))) 33)
  let signed_raw_result : (sbits 33) :=
    (bits_of_int ((BitVec.toInt dst) +i ((BitVec.toInt src) +i (BitVec.toNatInt input_cf))) 33)
  let result : (BitVec 32) := (Sail.BitVec.truncate raw_result 32)
  let cf ← (( do (cf_spec32 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (adc_af_spec32 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of ← (( do (of_spec32 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_adc_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let raw_result : (BitVec 65) :=
    (bits_of_int ((BitVec.toNatInt dst) +i ((BitVec.toNatInt src) +i (BitVec.toNatInt input_cf))) 65)
  let signed_raw_result : (sbits 65) :=
    (bits_of_int ((BitVec.toInt dst) +i ((BitVec.toInt src) +i (BitVec.toNatInt input_cf))) 65)
  let result : (BitVec 64) := (Sail.BitVec.truncate raw_result 64)
  let cf ← (( do (cf_spec64 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (adc_af_spec64 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec64 result)
  let of ← (( do (of_spec64 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sub_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let signed_raw_result : (sbits 9) := (bits_of_int ((BitVec.toInt dst) -i (BitVec.toInt src)) 9)
  let result : (BitVec 8) := (Sail.BitVec.truncate signed_raw_result 8)
  let cf : (BitVec 1) := (bool_to_bits ((BitVec.toNatInt dst) <b (BitVec.toNatInt src)))
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sub_af_spec8 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of ← (( do (of_spec8 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sub_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let signed_raw_result : (sbits 17) := (bits_of_int ((BitVec.toInt dst) -i (BitVec.toInt src)) 17)
  let result : (BitVec 16) := (Sail.BitVec.truncate signed_raw_result 16)
  let cf : (BitVec 1) := (bool_to_bits ((BitVec.toNatInt dst) <b (BitVec.toNatInt src)))
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sub_af_spec16 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of ← (( do (of_spec16 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sub_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let signed_raw_result : (sbits 33) := (bits_of_int ((BitVec.toInt dst) -i (BitVec.toInt src)) 33)
  let result : (BitVec 32) := (Sail.BitVec.truncate signed_raw_result 32)
  let cf : (BitVec 1) := (bool_to_bits ((BitVec.toNatInt dst) <b (BitVec.toNatInt src)))
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sub_af_spec32 dst src)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of ← (( do (of_spec32 signed_raw_result) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sbb_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let signed_raw_result : (sbits 10) :=
    (bits_of_int
      ((BitVec.toInt dst) -i (BitVec.toInt
          (bits_of_int ((BitVec.toInt src) +i (BitVec.toNatInt input_cf)) 9))) 10)
  let result : (BitVec 8) := (Sail.BitVec.truncate signed_raw_result 8)
  let cf : (BitVec 1) :=
    (bool_to_bits
      ((BitVec.toNatInt dst) <b (BitVec.toNatInt
          (bits_of_int ((BitVec.toNatInt input_cf) +i (BitVec.toNatInt src)) 9))))
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sbb_af_spec8 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of ← (( do (of_spec8 (Sail.BitVec.truncate signed_raw_result 9)) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sbb_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let signed_raw_result : (sbits 18) :=
    (bits_of_int
      ((BitVec.toInt dst) -i (BitVec.toInt
          (bits_of_int ((BitVec.toInt src) +i (BitVec.toNatInt input_cf)) 17))) 18)
  let result : (BitVec 16) := (Sail.BitVec.truncate signed_raw_result 16)
  let cf : (BitVec 1) :=
    (bool_to_bits
      ((BitVec.toNatInt dst) <b (BitVec.toNatInt
          (bits_of_int ((BitVec.toNatInt input_cf) +i (BitVec.toNatInt src)) 17))))
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sbb_af_spec16 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of ← (( do (of_spec16 (Sail.BitVec.truncate signed_raw_result 17)) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sbb_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let signed_raw_result : (sbits 34) :=
    (bits_of_int
      ((BitVec.toInt dst) -i (BitVec.toInt
          (bits_of_int ((BitVec.toInt src) +i (BitVec.toNatInt input_cf)) 33))) 34)
  let result : (BitVec 32) := (Sail.BitVec.truncate signed_raw_result 32)
  let cf : (BitVec 1) :=
    (bool_to_bits
      ((BitVec.toNatInt dst) <b (BitVec.toNatInt
          (bits_of_int ((BitVec.toNatInt input_cf) +i (BitVec.toNatInt src)) 33))))
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sbb_af_spec32 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of ← (( do (of_spec32 (Sail.BitVec.truncate signed_raw_result 33)) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_sbb_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let signed_raw_result : (sbits 66) :=
    (bits_of_int
      ((BitVec.toInt dst) -i (BitVec.toInt
          (bits_of_int ((BitVec.toInt src) +i (BitVec.toNatInt input_cf)) 65))) 66)
  let result : (BitVec 64) := (Sail.BitVec.truncate signed_raw_result 64)
  let cf : (BitVec 1) :=
    (bool_to_bits
      ((BitVec.toNatInt dst) <b (BitVec.toNatInt
          (bits_of_int ((BitVec.toNatInt input_cf) +i (BitVec.toNatInt src)) 65))))
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sbb_af_spec64 dst src input_cf)
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec64 result)
  let of ← (( do (of_spec64 (Sail.BitVec.truncate signed_raw_result 65)) ) : SailM (BitVec 1) )
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_af (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf)
            af) zf) sf) of)
  let undefined_flags : rflagsbits := (Mk_rflagsbits 0x00000000#32)
  (pure (result, output_rflags, undefined_flags))


def gpr_or_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 8) := (Sail.BitVec.extractLsb (dst ||| src) 7 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_or_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 16) := (Sail.BitVec.extractLsb (dst ||| src) 15 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_or_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 32) := (Sail.BitVec.extractLsb (dst ||| src) 31 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_and_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 8) := (Sail.BitVec.extractLsb (dst &&& src) 7 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_and_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 16) := (Sail.BitVec.extractLsb (dst &&& src) 15 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_and_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 32) := (Sail.BitVec.extractLsb (dst &&& src) 31 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_xor_spec_1 (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 8) := (Sail.BitVec.extractLsb (logxor dst src) 7 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec8 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_xor_spec_2 (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 16) := (Sail.BitVec.extractLsb (logxor dst src) 15 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec16 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_xor_spec_4 (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 32) := (Sail.BitVec.extractLsb (logxor dst src) 31 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec32 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_arith_logic_spec_1 (operation : Nat) (dst : (BitVec 8)) (src : (BitVec 8)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  match operation with
  | 0 => (gpr_add_spec_1 dst src input_rflags)
  | 1 => (gpr_or_spec_1 dst src input_rflags)
  | 2 => (gpr_adc_spec_1 dst src input_rflags)
  | 3 => (gpr_and_spec_1 dst src input_rflags)
  | 4 => (gpr_sub_spec_1 dst src input_rflags)
  | 5 => (gpr_xor_spec_1 dst src input_rflags)
  | 6 => (gpr_sbb_spec_1 dst src input_rflags)
  | 7 => (gpr_and_spec_1 dst src input_rflags)
  | 8 => (gpr_sub_spec_1 dst src input_rflags)
  | _ => (pure (0x00#8, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

/- Type quantifiers: operation : Nat, operation ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8} -/

def gpr_arith_logic_spec_2 (operation : Nat) (dst : (BitVec 16)) (src : (BitVec 16)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  match operation with
  | 0 => (gpr_add_spec_2 dst src input_rflags)
  | 1 => (gpr_or_spec_2 dst src input_rflags)
  | 2 => (gpr_adc_spec_2 dst src input_rflags)
  | 3 => (gpr_and_spec_2 dst src input_rflags)
  | 4 => (gpr_sub_spec_2 dst src input_rflags)
  | 5 => (gpr_xor_spec_2 dst src input_rflags)
  | 6 => (gpr_sbb_spec_2 dst src input_rflags)
  | 7 => (gpr_and_spec_2 dst src input_rflags)
  | 8 => (gpr_sub_spec_2 dst src input_rflags)
  | _ => (pure (0x0000#16, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

/- Type quantifiers: operation : Nat, operation ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8} -/

def gpr_arith_logic_spec_4 (operation : Nat) (dst : (BitVec 32)) (src : (BitVec 32)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  match operation with
  | 0 => (gpr_add_spec_4 dst src input_rflags)
  | 1 => (gpr_or_spec_4 dst src input_rflags)
  | 2 => (gpr_adc_spec_4 dst src input_rflags)
  | 3 => (gpr_and_spec_4 dst src input_rflags)
  | 4 => (gpr_sub_spec_4 dst src input_rflags)
  | 5 => (gpr_xor_spec_4 dst src input_rflags)
  | 6 => (gpr_sbb_spec_4 dst src input_rflags)
  | 7 => (gpr_and_spec_4 dst src input_rflags)
  | 8 => (gpr_sub_spec_4 dst src input_rflags)
  | _ => (pure (0x00000000#32, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

/- Type quantifiers: operation : Nat, operation ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8} -/

def gpr_arith_logic_spec_8 (operation : Nat) (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match operation with
  | 0 => (gpr_add_spec_8 dst src input_rflags)
  | 1 => (gpr_or_spec_8 dst src input_rflags)
  | 2 => (gpr_adc_spec_8 dst src input_rflags)
  | 3 => (gpr_and_spec_8 dst src input_rflags)
  | 4 => (gpr_sub_spec_8 dst src input_rflags)
  | 5 => (gpr_xor_spec_8 dst src input_rflags)
  | 6 => (gpr_sbb_spec_8 dst src input_rflags)
  | 7 => (gpr_and_spec_8 dst src input_rflags)
  | 8 => (gpr_sub_spec_8 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

/- Type quantifiers: operation : Nat, operand_size : Nat, operand_size ∈ {1, 2, 4, 8}, operation
  ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8} -/

def gpr_arith_logic_spec (operand_size : Nat) (operation : Nat) (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match operand_size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (gpr_arith_logic_spec_1 operation (Sail.BitVec.truncate dst 8) (Sail.BitVec.truncate src 8)
          input_rflags) ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (gpr_arith_logic_spec_2 operation (Sail.BitVec.truncate dst 16)
          (Sail.BitVec.truncate src 16) input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (gpr_arith_logic_spec_4 operation (Sail.BitVec.truncate dst 32)
          (Sail.BitVec.truncate src 32) input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | _ => (gpr_arith_logic_spec_8 operation dst src input_rflags)

/- Type quantifiers: seg_reg : Nat, addr_size : Nat, addr_size ∈ {2, 4, 8}, 0 ≤ seg_reg ∧
  seg_reg ≤ 5 -/

def rme_size (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (r_x : String) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM (BitVec 128) := do
  (pure (Sail.BitVec.zeroExtend
      (← (load_bytes_from_ea proc_mode addr_size nbytes eff_addr base_reg seg_reg r_x
          check_alignment? mem_ptr?)) 128))

/- Type quantifiers: k_ex568041_ : Bool, k_ex568040_ : Bool, seg_reg : Nat, nbytes : Nat, addr_size
  : Nat, addr_size ∈ {2, 4, 8}, nbytes ∈ {1, 2, 4, 6, 8}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/

def x86_operand_from_modr_m_and_sib_bytes (proc_mode : proc_mode) (reg_type : (BitVec 1)) (operand_size : Nat) (inst_ac? : Bool) (memory_ptr? : Bool) (seg_reg : Nat) (prefixes : (BitVec 52)) (temp_rip : (BitVec 48)) (rex_byte : (BitVec 8)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) (num_imm_bytes : (BitVec 3)) : SailM ((BitVec 128) × Int × (BitVec 64)) := do
  let (addr, increment_rip_by) ← (( do
    if ((mod_var == 0b11#2) : Bool)
    then (pure (0x0000000000000000#64, 0))
    else (x86_effective_addr proc_mode prefixes temp_rip rex_byte r_m mod_var sib num_imm_bytes) ) :
    SailM ((sbits 64) × Int) )
  let operand ← (( do
    if ((mod_var == 0b11#2) : Bool)
    then
      (do
        if ((reg_type == 0#1) : Bool)
        then
          (pure (Sail.BitVec.zeroExtend
              (← (rgfi_size (bits_of_int operand_size 4) (reg_index r_m rex_byte 0b00#2) rex_byte))
              128))
        else (xmmi_size (bits_of_int operand_size 5) (reg_index r_m rex_byte 0b00#2)))
    else
      (do
        let check_alignment? ← (( do (pure (inst_ac? && (← (alignment_checking_enabled_p ()))))
          ) : SailM Bool )
        let addr_size ← do (select_address_size proc_mode (some prefixes))
        let base_reg := (select_base_register proc_mode rex_byte r_m mod_var sib)
        (rme_size proc_mode addr_size operand_size addr base_reg seg_reg ":R" check_alignment?
          memory_ptr?)) ) : SailM (BitVec 128) )
  (pure (operand, increment_rip_by, addr))

/- Type quantifiers: seg_reg : Nat, k_ex568074_ : Bool, k_ex568073_ : Bool, operand_size : Nat, operand_size
  ∈ {1, 2, 4, 6, 8, 10, 16}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/

def x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := (0#1 == (Sail.BitVec.truncate (0x01#8 &&& opcode) 1))
  let operand_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let g ← (( do (rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2) rex_byte)
    ) : SailM (BitVec 64) )
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let inst_ac? : Bool := true
  let (e, increment_rip_by, e_addr) ← (( do
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
  let input_rflags ← (( do readReg rflags ) : SailM rflagsbits )
  let (result, output_rflags, undefined_flags) ← (( do
    (gpr_arith_logic_spec operand_size operation (Sail.BitVec.truncate e 64) g input_rflags) ) :
    SailM ((BitVec 64) × rflagsbits × rflagsbits) )
  if (((operation == 8) || (operation == 7)) : Bool)
  then (pure ())
  else
    (x86_operand_to_reg_mem proc_mode operand_size inst_ac? false
      (Sail.BitVec.zeroExtend result 128) seg_reg e_addr prefixes rex_byte r_m mod_var sib)
  (write_user_rflags output_rflags undefined_flags)
  (write_iptr proc_mode temp_rip)

/- Type quantifiers: operation : Nat, 0 ≤ operation ∧ operation ≤ 8 -/


def x86_add_adc_sub_sbb_or_and_xor_cmp_g_e (operation : Nat) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-G-E"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := (0#1 == (Sail.BitVec.truncate (0x01#8 &&& opcode) 1))
  let operand_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let g ← (( do (rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2) rex_byte)
    ) : SailM (BitVec 64) )
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let inst_ac? : Bool := true
  let (e, increment_rip_by, e_addr) ← (( do
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
  let input_rflags ← (( do readReg rflags ) : SailM rflagsbits )
  let (result, output_rflags, undefined_flags) ← (( do
    (gpr_arith_logic_spec operand_size operation g (Sail.BitVec.truncate e 64) input_rflags) ) :
    SailM ((BitVec 64) × rflagsbits × rflagsbits) )
  if ((operation == 8) : Bool)
  then (pure ())
  else
    (write_rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2) result rex_byte)
  (write_user_rflags output_rflags undefined_flags)
  (write_iptr proc_mode temp_rip)

end X86Registers.Functions
