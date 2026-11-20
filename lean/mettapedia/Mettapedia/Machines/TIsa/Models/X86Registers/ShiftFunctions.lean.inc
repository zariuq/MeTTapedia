import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def trunc (n : Nat) (x : (BitVec k_m)) : (BitVec (8 * n)) :=
  (sail_mask (8 *i n) x)

def bitslice (x : (BitVec k_n)) (low : Int) (width : Int) : SailM (BitVec width) := do
  assert (((Sail.BitVec.length x) ≥b 0) && ((low ≥b 0) && (width >b 0))) "prelude.sail:135.38-135.39"
  if (((low +i width) ≤b (Sail.BitVec.length x)) : Bool)
  then (pure (Sail.BitVec.extractLsb x ((low +i width) -i 1) low))
  else
    (if ((low <b ((Sail.BitVec.length x) -i 1)) : Bool)
    then
      (pure ((BitVec.zero ((low +i width) -i (Sail.BitVec.length x))) +++ (Sail.BitVec.extractLsb x
            ((Sail.BitVec.length x) -i 1) low)))
    else (pure (BitVec.zero width)))

def b_xor (i : Int) (j : Int) : SailM Int := do
  assert ((0 ≤b i) && ((i ≤b 1) && ((0 ≤b j) && (j ≤b 1)))) "prelude.sail:191.41-191.42"
  if ((i == 0) : Bool)
  then
    (if ((j == 0) : Bool)
    then (pure 0)
    else (pure 1))
  else
    (if ((j == 0) : Bool)
    then (pure 1)
    else (pure 0))

def logbit_bits (pos : Int) (x : (BitVec k_n)) : (BitVec 1) :=
  if (((0 ≤b pos) && (pos <b (Sail.BitVec.length x))) : Bool)
  then (BitVec.join1 [(BitVec.access x pos)])
  else (0#1 : (BitVec 1))

def rotate_left_bits (x : (BitVec k_n)) (width : Int) (places : Int) : (BitVec k_n) :=
  let high := (x <<< places)
  let low := (x >>> (width -i places))
  (high ||| low)

def rotate_right_bits (x : (BitVec k_n)) (width : Int) (places : Int) : (BitVec k_n) :=
  let low := (x >>> places)
  let high := (x <<< (width -i places))
  (high ||| low)

def sal_shl_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : Int := (ash_left_int (BitVec.toNatInt dst) (BitVec.toNatInt src))
  let result : (BitVec 8) := (bits_of_int raw_result 8)
  let (output_rflags, undefined_flags) ← (( do
    let v_79 := src
    if ((eq_bits_nat v_79 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_79 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 7 7)
            let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec8 result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 7 result))) )
              : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((8 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst (8 -i (BitVec.toNatInt src)) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sal_shl_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : Int := (ash_left_int (BitVec.toNatInt dst) (BitVec.toNatInt src))
  let result : (BitVec 16) := (bits_of_int raw_result 16)
  let (output_rflags, undefined_flags) ← (( do
    let v_81 := src
    if ((eq_bits_nat v_81 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_81 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 15 15)
            let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec16 result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 15 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((16 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst (16 -i (BitVec.toNatInt src)) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sal_shl_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : Int := (ash_left_int (BitVec.toNatInt dst) (BitVec.toNatInt src))
  let result : (BitVec 32) := (bits_of_int raw_result 32)
  let (output_rflags, undefined_flags) ← (( do
    let v_83 := src
    if ((eq_bits_nat v_83 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_83 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 31 31)
            let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec32 result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 31 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((32 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst (32 -i (BitVec.toNatInt src)) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sal_shl_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let raw_result : Int := (ash_left_int (BitVec.toNatInt dst) (BitVec.toNatInt src))
  let result : (BitVec 64) := (bits_of_int raw_result 64)
  let (output_rflags, undefined_flags) ← (( do
    let v_85 := src
    if ((eq_bits_nat v_85 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_85 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 63 63)
            let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec64 result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 63 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((64 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst (64 -i (BitVec.toNatInt src)) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sal_shl_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (sal_shl_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags) ) : SailM
        ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (sal_shl_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (sal_shl_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (sal_shl_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def shr_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 9) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 9)
  let raw_result : (BitVec 8) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 8)
  let result : (BitVec 8) := raw_result
  let (output_rflags, undefined_flags) ← (( do
    let v_87 := src
    if ((eq_bits_nat v_87 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_87 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec8 result)
            let of : (BitVec 1) := (Sail.BitVec.extractLsb dst 7 7)
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf) of)
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((8 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def shr_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 17) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 17)
  let raw_result : (BitVec 16) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 16)
  let result : (BitVec 16) := raw_result
  let (output_rflags, undefined_flags) ← (( do
    let v_89 := src
    if ((eq_bits_nat v_89 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_89 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec16 result)
            let of : (BitVec 1) := (Sail.BitVec.extractLsb dst 15 15)
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf) of)
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((16 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def shr_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 33) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 33)
  let raw_result : (BitVec 32) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 32)
  let result : (BitVec 32) := raw_result
  let (output_rflags, undefined_flags) ← (( do
    let v_91 := src
    if ((eq_bits_nat v_91 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_91 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec32 result)
            let of : (BitVec 1) := (Sail.BitVec.extractLsb dst 31 31)
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf) of)
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((32 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def shr_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 65) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 65)
  let raw_result : (BitVec 64) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 64)
  let result : (BitVec 64) := raw_result
  let (output_rflags, undefined_flags) ← (( do
    let v_93 := src
    if ((eq_bits_nat v_93 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_93 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec64 result)
            let of : (BitVec 1) := (Sail.BitVec.extractLsb dst 63 63)
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf) of)
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((64 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def shr_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (shr_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (shr_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (shr_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (shr_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def sar_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 9) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 9)
  let raw_result_not_sign_extended : (BitVec 8) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 8)
  let raw_result ← (( do
    if (((logbit_bits 7 dst) == 1#1) : Bool)
    then
      (pure (loghead_int 8
          (ash_int (← (binary_logext 8 (BitVec.toNatInt dst))) (BitVec.toInt neg_src))))
    else (pure (BitVec.toNatInt raw_result_not_sign_extended)) ) : SailM Int )
  let result : (BitVec 8) := (bits_of_int raw_result 8)
  let (output_rflags, undefined_flags) ← (( do
    let v_95 := src
    if ((eq_bits_nat v_95 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_95 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec8 result)
            let of : Int := 0
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((8 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec8 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec8 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sar_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 17) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 17)
  let raw_result_not_sign_extended : (BitVec 16) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 16)
  let raw_result ← (( do
    if (((logbit_bits 15 dst) == 1#1) : Bool)
    then
      (pure (loghead_int 16
          (ash_int (← (binary_logext 16 (BitVec.toNatInt dst))) (BitVec.toInt neg_src))))
    else (pure (BitVec.toNatInt raw_result_not_sign_extended)) ) : SailM Int )
  let result : (BitVec 16) := (bits_of_int raw_result 16)
  let (output_rflags, undefined_flags) ← (( do
    let v_97 := src
    if ((eq_bits_nat v_97 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_97 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec16 result)
            let of : Int := 0
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((16 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec16 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec16 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sar_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 33) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 33)
  let raw_result_not_sign_extended : (BitVec 32) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 32)
  let raw_result ← (( do
    if (((logbit_bits 31 dst) == 1#1) : Bool)
    then
      (pure (loghead_int 32
          (ash_int (← (binary_logext 32 (BitVec.toNatInt dst))) (BitVec.toInt neg_src))))
    else (pure (BitVec.toNatInt raw_result_not_sign_extended)) ) : SailM Int )
  let result : (BitVec 32) := (bits_of_int raw_result 32)
  let (output_rflags, undefined_flags) ← (( do
    let v_99 := src
    if ((eq_bits_nat v_99 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_99 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec32 result)
            let of : Int := 0
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((32 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec32 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec32 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sar_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let neg_src : (sbits 65) := (bits_of_int (Neg.neg (BitVec.toNatInt src)) 65)
  let raw_result_not_sign_extended : (BitVec 64) :=
    (bits_of_int (ash_int (BitVec.toNatInt dst) (BitVec.toInt neg_src)) 64)
  let raw_result ← (( do
    if (((logbit_bits 63 dst) == 1#1) : Bool)
    then
      (pure (loghead_int 64
          (ash_int (← (binary_logext 64 (BitVec.toNatInt dst))) (BitVec.toInt neg_src))))
    else (pure (BitVec.toNatInt raw_result_not_sign_extended)) ) : SailM Int )
  let result : (BitVec 64) := (bits_of_int raw_result 64)
  let (output_rflags, undefined_flags) ← (( do
    let v_101 := src
    if ((eq_bits_nat v_101 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_101 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb dst 0 0)
            let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
            let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
            let sf : (BitVec 1) := (sf_spec64 result)
            let of : Int := 0
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of
                (_update_rflagsbits_sf
                  (_update_rflagsbits_zf
                    (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                (bits_of_int of 1))
            let undefined_flags : rflagsbits :=
              (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
            (pure (output_rflags, undefined_flags)))
        else
          (do
            if ((64 ≤b (BitVec.toNatInt src)) : Bool)
            then
              (do
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf (_update_rflagsbits_pf input_rflags pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of
                    (_update_rflagsbits_af (_update_rflagsbits_cf (Mk_rflagsbits 0x00000000#32) 1#1)
                      1#1) 1#1)
                (pure (output_rflags, undefined_flags)))
            else
              (do
                let cf ← (( do (bitslice dst ((BitVec.toNatInt src) -i 1) 1) ) : SailM (BitVec 1)
                  )
                let pf ← (( do (pf_spec64 result) ) : SailM (BitVec 1) )
                let zf : (BitVec 1) := (zf_spec (BitVec.toNatInt result))
                let sf : (BitVec 1) := (sf_spec64 result)
                let output_rflags : rflagsbits :=
                  (_update_rflagsbits_sf
                    (_update_rflagsbits_zf
                      (_update_rflagsbits_pf (_update_rflagsbits_cf input_rflags cf) pf) zf) sf)
                let undefined_flags : rflagsbits :=
                  (_update_rflagsbits_of (_update_rflagsbits_af (Mk_rflagsbits 0x00000000#32) 1#1)
                    1#1)
                (pure (output_rflags, undefined_flags))))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def sar_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (sar_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (sar_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (sar_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (sar_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def rcl_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let old_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 9) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 9) 8 1 old_cf)
  let raw_result : (BitVec 9) := (rotate_left_bits new_dst 9 (BitVec.toNatInt src))
  let result : (BitVec 8) := (Sail.BitVec.truncate raw_result 8)
  let (output_rflags, undefined_flags) ← (( do
    let v_115 := src
    if ((eq_bits_nat v_115 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_115 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 8 raw_result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 7 result))) )
              : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 8 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcl_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let old_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 17) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 17) 16 1 old_cf)
  let raw_result : (BitVec 17) := (rotate_left_bits new_dst 17 (BitVec.toNatInt src))
  let result : (BitVec 16) := (Sail.BitVec.truncate raw_result 16)
  let (output_rflags, undefined_flags) ← (( do
    let v_117 := src
    if ((eq_bits_nat v_117 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_117 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 16 raw_result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 15 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 16 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcl_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let old_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 33) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 33) 32 1 old_cf)
  let raw_result : (BitVec 33) := (rotate_left_bits new_dst 33 (BitVec.toNatInt src))
  let result : (BitVec 32) := (Sail.BitVec.truncate raw_result 32)
  let (output_rflags, undefined_flags) ← (( do
    let v_119 := src
    if ((eq_bits_nat v_119 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_119 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 32 raw_result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 31 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 32 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcl_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let old_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 65) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 65) 64 1 old_cf)
  let raw_result : (BitVec 65) := (rotate_left_bits new_dst 65 (BitVec.toNatInt src))
  let result : (BitVec 64) := (Sail.BitVec.truncate raw_result 64)
  let (output_rflags, undefined_flags) ← (( do
    let v_121 := src
    if ((eq_bits_nat v_121 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_121 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 64 raw_result)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 63 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 64 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcl_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (rcl_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rcl_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rcl_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (rcl_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def rol_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 8) := (rotate_left_bits dst 8 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_123 := src
    if ((eq_bits_nat v_123 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_123 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 7 result))) )
              : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rol_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 16) := (rotate_left_bits dst 16 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_125 := src
    if ((eq_bits_nat v_125 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_125 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 15 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rol_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 32) := (rotate_left_bits dst 32 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_127 := src
    if ((eq_bits_nat v_127 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_127 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 31 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rol_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 64) := (rotate_left_bits dst 64 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_129 := src
    if ((eq_bits_nat v_129 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_129 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
            let of ← (( do (b_xor (BitVec.toNatInt cf) (BitVec.toNatInt (logbit_bits 63 result)))
              ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rol_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (rol_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rol_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rol_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (rol_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def rcr_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 9) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 9) 8 1 input_cf)
  let raw_result : (BitVec 9) := (rotate_right_bits new_dst 9 (BitVec.toNatInt src))
  let result : (BitVec 8) := (Sail.BitVec.truncate raw_result 8)
  let (output_rflags, undefined_flags) ← (( do
    let v_131 := src
    if ((eq_bits_nat v_131 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_131 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 8 raw_result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 7 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 6 6))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 8 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcr_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 17) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 17) 16 1 input_cf)
  let raw_result : (BitVec 17) := (rotate_right_bits new_dst 17 (BitVec.toNatInt src))
  let result : (BitVec 16) := (Sail.BitVec.truncate raw_result 16)
  let (output_rflags, undefined_flags) ← (( do
    let v_133 := src
    if ((eq_bits_nat v_133 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_133 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 16 raw_result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 15 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 14 14))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 16 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcr_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 33) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 33) 32 1 input_cf)
  let raw_result : (BitVec 33) := (rotate_right_bits new_dst 33 (BitVec.toNatInt src))
  let result : (BitVec 32) := (Sail.BitVec.truncate raw_result 32)
  let (output_rflags, undefined_flags) ← (( do
    let v_135 := src
    if ((eq_bits_nat v_135 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_135 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 32 raw_result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 31 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 30 30))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 32 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcr_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let input_cf : (BitVec 1) := (_get_rflagsbits_cf input_rflags)
  let new_dst : (BitVec 65) := (changeSlice_bits (Sail.BitVec.zeroExtend dst 65) 64 1 input_cf)
  let raw_result : (BitVec 65) := (rotate_right_bits new_dst 65 (BitVec.toNatInt src))
  let result : (BitVec 64) := (Sail.BitVec.truncate raw_result 64)
  let (output_rflags, undefined_flags) ← (( do
    let v_137 := src
    if ((eq_bits_nat v_137 0) : Bool)
    then (pure (input_rflags, (Mk_rflagsbits 0x00000000#32)))
    else
      (do
        if ((eq_bits_nat v_137 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 64 raw_result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 63 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 62 62))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (logbit_bits 64 raw_result)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def rcr_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (rcr_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rcr_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (rcr_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (rcr_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def ror_spec_8 (dst : (BitVec 8)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 8) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 8) := (rotate_right_bits dst 8 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_139 := src
    if ((eq_bits_nat v_139 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_139 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 7 result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 7 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 6 6))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def ror_spec_16 (dst : (BitVec 16)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 16) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 16) := (rotate_right_bits dst 16 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_141 := src
    if ((eq_bits_nat v_141 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_141 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 15 result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 15 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 14 14))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def ror_spec_32 (dst : (BitVec 32)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 32) := (rotate_right_bits dst 32 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_143 := src
    if ((eq_bits_nat v_143 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_143 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 31 result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 31 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 30 30))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def ror_spec_64 (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  let result : (BitVec 64) := (rotate_right_bits dst 64 (BitVec.toNatInt src))
  let (output_rflags, undefined_flags) ← (( do
    let v_145 := src
    if ((eq_bits_nat v_145 0) : Bool)
    then
      (let undefined_flags : rflagsbits := (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
      (pure (input_rflags, undefined_flags)))
    else
      (do
        if ((eq_bits_nat v_145 1) : Bool)
        then
          (do
            let cf : (BitVec 1) := (logbit_bits 63 result)
            let of ← (( do
              (b_xor (BitVec.toNatInt (logbit_bits 63 result))
                (BitVec.toNatInt (Sail.BitVec.extractLsb result 62 62))) ) : SailM Int )
            let output_rflags : rflagsbits :=
              (_update_rflagsbits_of (_update_rflagsbits_cf input_rflags cf) (bits_of_int of 1))
            (pure (output_rflags, (Mk_rflagsbits 0x00000000#32))))
        else
          (let cf : (BitVec 1) := (Sail.BitVec.extractLsb result 0 0)
          let output_rflags : rflagsbits := (_update_rflagsbits_cf input_rflags cf)
          let undefined_flags : rflagsbits :=
            (_update_rflagsbits_of (Mk_rflagsbits 0x00000000#32) 1#1)
          (pure (output_rflags, undefined_flags)))) ) : SailM (rflagsbits × rflagsbits) )
  (pure (result, output_rflags, undefined_flags))

def ror_spec (size : Nat) (dst : (BitVec 64)) (src : (BitVec 6)) (input_rflags : (BitVec 32)) : SailM ((BitVec 64) × (BitVec 32) × (BitVec 32)) := do
  match size with
  | 1 =>
    (do
      let (elem0, elem1, elem2) ← (( do (ror_spec_8 (Sail.BitVec.truncate dst 8) src input_rflags)
        ) : SailM ((BitVec 8) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 2 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (ror_spec_16 (Sail.BitVec.truncate dst 16) src input_rflags) ) : SailM
        ((BitVec 16) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 4 =>
    (do
      let (elem0, elem1, elem2) ← (( do
        (ror_spec_32 (Sail.BitVec.truncate dst 32) src input_rflags) ) : SailM
        ((BitVec 32) × rflagsbits × rflagsbits) )
      (pure ((Sail.BitVec.zeroExtend elem0 64), elem1, elem2)))
  | 8 => (ror_spec_64 dst src input_rflags)
  | _ =>
    (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits 0x00000000#32)))

def x86_sal_sar_shl_shr_rcl_rcr_rol_ror (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := ((opcode == 0xC0#8) || ((opcode == 0xD0#8) || (opcode == 0xD2#8)))
  let reg_mem_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let inst_ac? : Bool := true
  let (reg_mem, increment_rip_by, addr) ← (( do
    (x86_operand_from_modr_m_and_sib_bytes proc_mode 0#1 reg_mem_size inst_ac? false seg_reg
      prefixes temp_rip rex_byte r_m mod_var sib
      (if (((opcode == 0xC0#8) || (opcode == 0xC1#8)) : Bool)
      then 0b001#3
      else 0b000#3)) ) : SailM ((BitVec 128) × Int × (sbits 64)) )
  let increment_rip_by : (BitVec 3) := (bits_of_int increment_rip_by 3)
  let temp_rip ← (( do
    (add_to_iptr proc_mode temp_rip (Sail.BitVec.zeroExtend increment_rip_by 48)) ) : SailM
    (sbits 48) )
  let shift_rotate_by ← (( do
    let v_147 := opcode
    if ((eq_bits_nat v_147 208) : Bool)
    then (pure 0x00000000000000000000000000000001#128)
    else
      (do
        if ((eq_bits_nat v_147 209) : Bool)
        then (pure 0x00000000000000000000000000000001#128)
        else
          (do
            if ((eq_bits_nat v_147 210) : Bool)
            then (pure (Sail.BitVec.zeroExtend (← (rr08 0x1#4 rex_byte)) 128))
            else
              (do
                if ((eq_bits_nat v_147 211) : Bool)
                then (pure (Sail.BitVec.zeroExtend (← (rr08 0x1#4 rex_byte)) 128))
                else
                  (do
                    if ((eq_bits_nat v_147 192) : Bool)
                    then
                      (rme_size proc_mode (← (select_address_size proc_mode (some prefixes))) 1
                        (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false)
                    else
                      (do
                        if ((eq_bits_nat v_147 193) : Bool)
                        then
                          (rme_size proc_mode (← (select_address_size proc_mode (some prefixes)))
                            1 (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false)
                        else (pure 0x00000000000000000000000000000000#128)))))) ) : SailM
    (BitVec 128) )
  let countmask : Int :=
    if (((logbitp_bits 3 rex_byte) && (! byte_operand?)) : Bool)
    then 63
    else 31
  let shift_rotate_by : (BitVec 128) := ((bits_of_int countmask 128) &&& shift_rotate_by)
  let temp_rip ← (( do
    if (((opcode == 0xC0#8) || (opcode == 0xC1#8)) : Bool)
    then (pure (Sail.BitVec.signExtend (← (add_to_iptr proc_mode temp_rip 0x000000000001#48)) 49))
    else (pure (Sail.BitVec.signExtend temp_rip 49)) ) : SailM (sbits 49) )
  let badlength? : (Option Int) :=
    (check_instruction_length start_rip (Sail.BitVec.truncate temp_rip 48) 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let input_rflags ← (( do readReg rflags ) : SailM rflagsbits )
  let (result, output_rflags, undefined_flags) ← (( do
    let v_153 := reg
    if ((eq_bits_nat v_153 0) : Bool)
    then
      (rol_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
        (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
    else
      (do
        if ((eq_bits_nat v_153 1) : Bool)
        then
          (ror_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
            (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
        else
          (do
            if ((eq_bits_nat v_153 2) : Bool)
            then
              (rcl_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
            else
              (do
                if ((eq_bits_nat v_153 3) : Bool)
                then
                  (rcr_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                    (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
                else
                  (do
                    if ((eq_bits_nat v_153 4) : Bool)
                    then
                      (sal_shl_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                        (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
                    else
                      (do
                        if ((eq_bits_nat v_153 5) : Bool)
                        then
                          (shr_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                            (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
                        else
                          (do
                            if ((eq_bits_nat v_153 7) : Bool)
                            then
                              (sar_spec reg_mem_size (Sail.BitVec.truncate reg_mem 64)
                                (Sail.BitVec.truncate shift_rotate_by 6) input_rflags)
                            else
                              (pure (0x0000000000000000#64, (Mk_rflagsbits 0x00000000#32), (Mk_rflagsbits
                                  0x00000000#32))))))))) ) : SailM
    ((BitVec 64) × rflagsbits × rflagsbits) )
  (write_user_rflags output_rflags undefined_flags)
  (x86_operand_to_reg_mem proc_mode reg_mem_size inst_ac? false
    (Sail.BitVec.zeroExtend (sail_mask 64 (trunc reg_mem_size result)) 128) seg_reg addr prefixes
    rex_byte r_m mod_var sib)
  (write_iptr proc_mode (Sail.BitVec.truncate temp_rip 48))

end X86Registers.Functions
