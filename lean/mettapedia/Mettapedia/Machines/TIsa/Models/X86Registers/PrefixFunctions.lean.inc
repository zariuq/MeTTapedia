import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option autoImplicit true
set_option linter.unusedVariables false
open Sail Sail.ConcurrencyInterfaceV1
namespace X86Registers.Functions
open Register proc_mode exception

def ash_int (i : Int) (c : Int) : Int :=
  if ((c == 0) : Bool)
  then i
  else
    (if ((c >b 0) : Bool)
    then (Int.shiftl i c)
    else (Int.shiftr i (Neg.neg c)))

/-- Type quantifiers: x : Int -/

def _update_prefixes_adr (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 43 36 x)


def _update_prefixes_lck (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 11 4 x)


def _update_prefixes_num (v : (BitVec 52)) (x : (BitVec 4)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_prefixes_nxt (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 51 44 x)


def _update_prefixes_opr (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 35 28 x)


def _update_prefixes_rep (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 19 12 x)


def _update_prefixes_seg (v : (BitVec 52)) (x : (BitVec 8)) : (BitVec 52) :=
  (Sail.BitVec.updateSubrange v 27 20 x)


def is_ext_prefix_byte (proc_mode : proc_mode) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (cnt : Nat) (byte : (BitVec 8)) : Bool :=
  false

/-- Type quantifiers: cnt : Nat, 0 ≤ cnt ∧ cnt ≤ 15 -/

def process_ext_prefix_byte (proc_mode : proc_mode) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (cnt : Nat) (byte : (BitVec 8)) : ((BitVec 52) × (BitVec 8) × Bool) :=
  (prefixes, rex_byte, false)


def rme08 (proc_mode : proc_mode) (addr_size : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (r_x : String) : SailM (BitVec 8) := do
  (load_bytes_from_ea proc_mode addr_size 1 eff_addr base_reg seg_reg r_x false false)

/-- Type quantifiers: k_ex568015_ : Bool, seg_reg : Nat, addr_size : Nat, addr_size ∈ {2, 4, 8}, 0
  ≤ seg_reg ∧ seg_reg ≤ 5 -/

def get_one_byte_prefix_array_code (byte : (BitVec 8)) : Int :=
  (GetElem?.getElem!
    (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : (Vector Int 256))
    (BitVec.toNatInt (loghead_bits 8 byte)))


noncomputable def get_prefixes_body (get_prefixes : PrefixScanner) (proc_mode : proc_mode) (start_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (cnt : Nat) : SailM ((BitVec 52) × (BitVec 8)) := do
  if ((cnt == 0) : Bool)
  then (pure (prefixes, rex_byte))
  else
    (do
      let byte ← (( do
        (rme08 proc_mode (← (select_address_size proc_mode (some prefixes)))
          (Sail.BitVec.signExtend start_rip 64) none 1 ":X") ) : SailM (BitVec 8) )
      if ((is_ext_prefix_byte proc_mode prefixes rex_byte cnt byte) : Bool)
      then
        (do
          let (prefixes, rex_byte, continue?) :=
            (process_ext_prefix_byte proc_mode prefixes rex_byte cnt byte)
          if ((! continue?) : Bool)
          then (pure (prefixes, rex_byte))
          else
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip prefixes rex_byte (← (check_range 0 15 (cnt -i 1))))))
      else
        (do
          let prefix_byte_group_code : Int := (get_one_byte_prefix_array_code byte)
          match prefix_byte_group_code with
          | 0 =>
            (do
              let rex? : Bool :=
                ((in_64bit_mode proc_mode) && ((bits_of_int
                      (ash_int (BitVec.toNatInt byte) (Neg.neg 4)) 4) == 0x4#4))
              if (rex? : Bool)
              then
                (do
                  let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) :
                    SailM (sbits 48) )
                  (get_prefixes proc_mode next_rip prefixes byte (← (check_range 0 15 (cnt -i 1)))))
              else
                (let prefixes : X86Registers.prefixes := (_update_prefixes_nxt prefixes byte)
                (pure ((_update_prefixes_num prefixes (bits_of_int (15 -i cnt) 4)), rex_byte))))
          | 1 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              let prefixes : X86Registers.prefixes :=
                if ((byte == 0xF0#8) : Bool)
                then (_update_prefixes_lck prefixes byte)
                else (_update_prefixes_rep prefixes byte)
              (get_prefixes proc_mode next_rip prefixes 0x00#8 (← (check_range 0 15 (cnt -i 1)))))
          | 2 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              if ((((in_64bit_mode proc_mode) && ((byte == 0x64#8) || (byte == 0x65#8))) || (! (in_64bit_mode
                       proc_mode))) : Bool)
              then
                (get_prefixes proc_mode next_rip (_update_prefixes_seg prefixes byte) 0x00#8
                  (← (check_range 0 15 (cnt -i 1))))
              else
                (get_prefixes proc_mode next_rip prefixes 0x00#8 (← (check_range 0 15 (cnt -i 1)))))
          | 3 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip (_update_prefixes_opr prefixes byte) 0x00#8
                (← (check_range 0 15 (cnt -i 1)))))
          | 4 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip (_update_prefixes_adr prefixes byte) 0x00#8
                (← (check_range 0 15 (cnt -i 1)))))
          | _ => (pure (prefixes, rex_byte))))


noncomputable def get_prefixes (proc_mode : proc_mode) (start_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (cnt : Nat) : SailM ((BitVec 52) × (BitVec 8)) := do
  if ((cnt == 0) : Bool)
  then (pure (prefixes, rex_byte))
  else
    (do
      let byte ← (( do
        (rme08 proc_mode (← (select_address_size proc_mode (some prefixes)))
          (Sail.BitVec.signExtend start_rip 64) none 1 ":X") ) : SailM (BitVec 8) )
      if ((is_ext_prefix_byte proc_mode prefixes rex_byte cnt byte) : Bool)
      then
        (do
          let (prefixes, rex_byte, continue?) :=
            (process_ext_prefix_byte proc_mode prefixes rex_byte cnt byte)
          if ((! continue?) : Bool)
          then (pure (prefixes, rex_byte))
          else
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip prefixes rex_byte ((← checkedPredecessor cnt).val))))
      else
        (do
          let prefix_byte_group_code : Int := (get_one_byte_prefix_array_code byte)
          match prefix_byte_group_code with
          | 0 =>
            (do
              let rex? : Bool :=
                ((in_64bit_mode proc_mode) && ((bits_of_int
                      (ash_int (BitVec.toNatInt byte) (Neg.neg 4)) 4) == 0x4#4))
              if (rex? : Bool)
              then
                (do
                  let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) :
                    SailM (sbits 48) )
                  (get_prefixes proc_mode next_rip prefixes byte ((← checkedPredecessor cnt).val)))
              else
                (let prefixes : X86Registers.prefixes := (_update_prefixes_nxt prefixes byte)
                (pure ((_update_prefixes_num prefixes (bits_of_int (15 -i cnt) 4)), rex_byte))))
          | 1 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              let prefixes : X86Registers.prefixes :=
                if ((byte == 0xF0#8) : Bool)
                then (_update_prefixes_lck prefixes byte)
                else (_update_prefixes_rep prefixes byte)
              (get_prefixes proc_mode next_rip prefixes 0x00#8 ((← checkedPredecessor cnt).val)))
          | 2 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              if ((((in_64bit_mode proc_mode) && ((byte == 0x64#8) || (byte == 0x65#8))) || (! (in_64bit_mode
                       proc_mode))) : Bool)
              then
                (get_prefixes proc_mode next_rip (_update_prefixes_seg prefixes byte) 0x00#8
                  ((← checkedPredecessor cnt).val))
              else
                (get_prefixes proc_mode next_rip prefixes 0x00#8 ((← checkedPredecessor cnt).val)))
          | 3 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip (_update_prefixes_opr prefixes byte) 0x00#8
                ((← checkedPredecessor cnt).val)))
          | 4 =>
            (do
              let next_rip ← (( do (add_to_iptr proc_mode start_rip 0x000000000001#48) ) : SailM
                (sbits 48) )
              (get_prefixes proc_mode next_rip (_update_prefixes_adr prefixes byte) 0x00#8
                ((← checkedPredecessor cnt).val)))
          | _ => (pure (prefixes, rex_byte))))

termination_by cnt
decreasing_by all_goals omega

end X86Registers.Functions
