import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def bool_to_bits (b : Bool) : (BitVec 1) :=
  match b with
  | true => 1#1
  | false => 0#1


def logcount_int (x : Int) : Int :=
  if ((x == 0) : Bool)
  then 0
  else
    (if ((x <b 0) : Bool)
    then (logcount_int (lognot_int x))
    else
      (if ((isEven x) : Bool)
      then (logcount_int (Int.shiftr x 1))
      else ((logcount_int (Int.shiftr x 1)) +i 1)))
termination_by x.natAbs
decreasing_by
  all_goals
    first
    | apply Mettapedia.Machines.TIsa.X86Alu.complement_rank
      simp_all
    | apply Mettapedia.Machines.TIsa.X86Alu.positive_half_rank
      simp_all <;> omega

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/

def logxor (x : (BitVec k_n)) (y : (BitVec k_n)) : (BitVec k_n) :=
  (x ^^^ y)

/-- Type quantifiers: j : Int, i : Int, size : Int -/

def Mk_rflagsbits (v : (BitVec 32)) : (BitVec 32) :=
  v


def _update_rflagsbits_af (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_rflagsbits_cf (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_rflagsbits_of (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_rflagsbits_pf (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_rflagsbits_sf (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_rflagsbits_zf (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def cf_spec64 (raw_result : (BitVec 65)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (unsigned_byte_p_int 64 (BitVec.toNatInt raw_result))))))

/-- Type quantifiers: signed_raw_result : Int, result_nbits : Nat, 0 ≤ result_nbits -/

def of_spec64 (signed_raw_result : (BitVec 65)) : SailM (BitVec 1) := do
  (pure (bool_to_bits (! (← (signed_byte_p_int 64 (BitVec.toInt signed_raw_result))))))

/-- Type quantifiers: result : Nat, 0 ≤ result -/

def zf_spec (result : Nat) : (BitVec 1) :=
  if ((result == 0) : Bool)
  then 1#1
  else 0#1


def pf_spec64 (result : (BitVec 64)) : SailM (BitVec 1) := do
  (pure (bool_to_bits
      (! (← (logbitp_int 0 (logcount_int (BitVec.toNatInt (loghead_bits 8 result))))))))

/-- Type quantifiers: result : Nat, result_nbits : Nat, result_nbits ∈ {8, 16, 32, 64}, 0 ≤
  result -/

def sf_spec64 (result : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb result 63 63)

/-- Type quantifiers: result : Nat, result_nbits : Nat, result_nbits ∈ {8, 16, 32, 64}, 0 ≤
  result -/

def add_af_spec64 (dst : (BitVec 64)) (src : (BitVec 64)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let add : (BitVec 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) +i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits (15 <b (BitVec.toNatInt add)))


def sub_af_spec64 (dst : (BitVec 64)) (src : (BitVec 64)) : (BitVec 1) :=
  let dst_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb dst 3 0)
  let src_3_0 : (BitVec 4) := (Sail.BitVec.extractLsb src 3 0)
  let sub : (sbits 5) := (bits_of_int ((BitVec.toNatInt dst_3_0) -i (BitVec.toNatInt src_3_0)) 5)
  (bool_to_bits ((BitVec.toInt sub) <b 0))


def gpr_add_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : (BitVec 65) := (bits_of_int ((BitVec.toNatInt dst) +i (BitVec.toNatInt src)) 65)
  let signed_raw_result : (sbits 65) := (bits_of_int ((BitVec.toInt dst) +i (BitVec.toInt src)) 65)
  let result : (BitVec 64) := (Sail.BitVec.truncate raw_result 64)
  let cf ← (( do (cf_spec64 raw_result) ) : SailM (BitVec 1) )
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (add_af_spec64 dst src)
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


def gpr_sub_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let signed_raw_result : (sbits 65) := (bits_of_int ((BitVec.toInt dst) -i (BitVec.toInt src)) 65)
  let result : (BitVec 64) := (Sail.BitVec.truncate signed_raw_result 64)
  let cf : (BitVec 1) := (bool_to_bits ((BitVec.toNatInt dst) <b (BitVec.toNatInt src)))
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let af : (BitVec 1) := (sub_af_spec64 dst src)
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


def gpr_or_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 64) := (Sail.BitVec.extractLsb (dst ||| src) 63 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec64 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_and_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 64) := (Sail.BitVec.extractLsb (dst &&& src) 63 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec64 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))


def gpr_xor_spec_8 (dst : (BitVec 64)) (src : (BitVec 64)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 64) := (Sail.BitVec.extractLsb (logxor dst src) 63 0)
  let cf : Int := 0
  let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
  let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
  let sf : (BitVec 1) := (sf_spec64 result)
  let of : Int := 0
  let output_rflags : rflagsbits :=
    (_update_rflagsbits_of
      (_update_rflagsbits_sf
        (_update_rflagsbits_zf
          (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags (bits_of_int cf 1)) pf) zf) sf)
      (bits_of_int of 1))
  let undefined_flags : rflagsbits := (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
  (pure (result, output_rflags, undefined_flags))

/- Type quantifiers: operation : Nat, operation ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8} -/

end X86Registers.Functions
