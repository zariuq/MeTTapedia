import Sail
import X86Registers.Defs
import X86Registers.SpecializationV1

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace X86Registers

open ConcurrencyInterfaceV1

namespace Functions

open write_kind
open read_kind
open proc_mode
open option
open exception
open Register

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: y : Nat, k_n : Nat, k_n > 0, 0 ≤ y -/
def eq_bits_nat (x : (BitVec k_n)) (y : Nat) : Bool :=
  ((BitVec.toNatInt x) == y)

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_a : Type -/
def x86_model_error (msg : String) : SailM k_a := do
  sailThrow ((Emsg (HAppend.hAppend "Model error: " msg)))

/-- Type quantifiers: k_a : Type -/
def x86_fault (msg : String) : SailM k_a := do
  sailThrow ((Emsg (HAppend.hAppend "Fault: " msg)))

def bits_to_bool (b : (BitVec 1)) : Bool :=
  match b with
  | 1 => true
  | _ => false

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask_signed (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.signExtend v len)

/-- Type quantifiers: n : Int, m : Int, i : Int, n ≤ m -/
def check_range (n : Int) (m : Int) (i : Int) : SailM Int := do
  assert ((n ≤b i) && (i ≤b m)) "prelude.sail:171.23-171.24"
  (pure i)

/-- Type quantifiers: x : Int, n : Nat, n ≥ 0 -/
def bits_of_int (x : Int) (n : Nat) : (BitVec n) :=
  (get_slice_int n x 0)

/-- Type quantifiers: x : Int -/
def isEven (x : Int) : Bool :=
  if (((get_slice_int 1 x 0) == 0#1) : Bool)
  then true
  else false

/-- Type quantifiers: x : Int, bits : Int -/
def unsigned_byte_p_int (bits : Int) (x : Int) : SailM Bool := do
  assert (bits ≥b 0) "prelude.sail:212.17-212.18"
  (pure ((0 ≤b x) && (x <b (2 ^i bits))))

/-- Type quantifiers: x : Int, bits : Int -/
def signed_byte_p_int (bits : Int) (x : Int) : SailM Bool := do
  assert (bits ≥b 0) "prelude.sail:226.17-226.18"
  (pure (((Neg.neg (2 ^i (bits -i 1))) ≤b x) && (x <b (2 ^i (bits -i 1)))))

/-- Type quantifiers: i : Int, size : Int -/
def loghead_int (size : Int) (i : Int) : Int :=
  if ((size == 0) : Bool)
  then 0
  else (BitVec.toNatInt (get_slice_int size i 0))

/-- Type quantifiers: size : Nat, k_m : Nat, size ≥ 0 ∧ k_m ≥ 0 -/
def loghead_bits (size : Nat) (x : (BitVec k_m)) : (BitVec size) :=
  (sail_mask size x)

/-- Type quantifiers: j : Int, i : Int -/
def logbitp_int (i : Int) (j : Int) : SailM Bool := do
  assert (i ≥b 0) "prelude.sail:289.14-289.15"
  (pure (bits_to_bool (get_slice_int 1 j i)))

/-- Type quantifiers: k_n : Nat, pos : Int, k_n ≥ 0 -/
def logbitp_bits (pos : Int) (x : (BitVec k_n)) : Bool :=
  if (((0 ≤b pos) && (pos <b (Sail.BitVec.length x))) : Bool)
  then ((BitVec.access x pos) == 1#1)
  else false

/-- Type quantifiers: x : Int -/
def lognot_int (x : Int) : Int :=
  ((Neg.neg x) -i 1)

/-- Type quantifiers: j : Int, i : Int -/
def floor2 (i : Int) (j : Int) : Int :=
  let tdiv := (Int.tdiv i j)
  let tmod := (Int.tmod i j)
  if ((((j >b 0) && (tmod ≥b 0)) || ((j <b 0) && (tmod ≤b 0))) : Bool)
  then tdiv
  else (tdiv -i 1)

/-- Type quantifiers: j : Int, i : Int -/
def logand_int (i : Int) (j : Int) : Int :=
  if ((i == 0) : Bool)
  then 0
  else
    (if ((j == 0) : Bool)
    then 0
    else
      (if ((i == (Neg.neg 1)) : Bool)
      then j
      else
        (if ((j == (Neg.neg 1)) : Bool)
        then i
        else
          (let x := (2 *i (logand_int (floor2 i 2) (floor2 j 2)))
          (x +i (if ((isEven i) : Bool)
            then 0
            else
              (if ((isEven j) : Bool)
              then 0
              else 1)))))))
termination_by i.natAbs
decreasing_by
  change (Mettapedia.Machines.TIsa.SailInteger.floorFromTrunc i 2).natAbs < i.natAbs
  apply Mettapedia.Machines.TIsa.SailInteger.half_abs_decreases
  · intro zero
    subst i
    simp_all
  · intro minusOne
    subst i
    simp_all

/-- Type quantifiers: j : Int, i : Int -/
def logior_int (i : Int) (j : Int) : Int :=
  (lognot_int (logand_int (lognot_int i) (lognot_int j)))

/-- Type quantifiers: j : Int, i : Int, size : Int -/
def binary_logapp (size : Int) (i : Int) (j : Int) : Int :=
  ((loghead_int size i) +i (j *i (2 ^i size)))

/-- Type quantifiers: i : Int, size : Int -/
def binary_logext (size : Int) (i : Int) : SailM Int := do
  assert (0 <b size) "prelude.sail:440.16-440.17"
  (pure (binary_logapp (size -i 1) i
      (← do
        if ((← (logbitp_int (size -i 1) i)) : Bool)
        then (pure (Neg.neg 1))
        else (pure 0))))

/-- Type quantifiers: x : Int, n : Nat, n ≥ 0 -/
def ash_left_int (x : Int) (n : Nat) : Int :=
  (x *i (2 ^i n))

/-- Type quantifiers: v : Int, width : Int, low : Int, x : Int -/
def changeSlice_int (x : Int) (low : Int) (width : Int) (v : Int) : Int :=
  (set_slice_int width x low (get_slice_int width v 0))

/-- Type quantifiers: k_n : Nat, low : Nat, width : Nat, low ≥ 0 ∧
  width > 0 ∧ (low + width) ≤ k_n -/
def changeSlice_bits (x : (BitVec k_n)) (low : Nat) (width : Nat) (v : (BitVec width)) : (BitVec k_n) :=
  (Sail.BitVec.updateSubrange x ((low +i width) -i 1) low v)

def regval_from_reg (r : (BitVec 64)) : (BitVec 64) :=
  r

def read_rip (_ : Unit) : SailM (BitVec 48) := do
  (pure (Sail.BitVec.truncate (regval_from_reg (← readReg rip)) 48))

/-- Type quantifiers: k_addr_width : Nat, len : Nat, k_addr_width > 0 ∧ len > 0 -/
def log_memory_read (addr : (BitVec k_addr_width)) (len : Nat) (value : (BitVec (8 * len))) : SailM Unit := do
  (pure (print_endline
      (HAppend.hAppend
        (HAppend.hAppend
          (HAppend.hAppend
            (HAppend.hAppend
              (HAppend.hAppend (HAppend.hAppend (BitVec.toFormatted (← (read_rip ()))) ": R ")
                (BitVec.toFormatted addr)) " ") (Int.repr len)) " ") (BitVec.toFormatted value))))

/-- Type quantifiers: k_addr_width : Nat, k_addr_width > 0 -/
def memi (addr : (BitVec k_addr_width)) : SailM (BitVec 8) := do
  let result ← do (read_mem Read_plain 64 (sail_mask 64 addr) 1)
  (log_memory_read addr 1 result)
  (pure result)

/-- Type quantifiers: k_addr_width : Nat, len : Nat, k_addr_width > 0 ∧ len > 0 -/
def log_memory_write (addr : (BitVec k_addr_width)) (len : Nat) (value : (BitVec (8 * len))) : SailM Unit := do
  (pure (print_endline
      (HAppend.hAppend
        (HAppend.hAppend
          (HAppend.hAppend
            (HAppend.hAppend
              (HAppend.hAppend (HAppend.hAppend (BitVec.toFormatted (← (read_rip ()))) ": W ")
                (BitVec.toFormatted addr)) " ") (Int.repr len)) " ") (BitVec.toFormatted value))))

/-- Type quantifiers: k_addr_width : Nat, k_addr_width > 0 -/
def bang_memi (addr : (BitVec k_addr_width)) (valToWrite : (BitVec 8)) : SailM Unit := do
  let dummy ← do (write_mem_ea Write_plain 64 (sail_mask 64 addr) 1)
  let dummy2 ← do (write_mem Write_plain 64 (sail_mask 64 addr) 1 valToWrite)
  (log_memory_write addr 1 valToWrite)

def fault (_ : Unit) : SailM Bool := do
  readReg fault_reg

/-- Type quantifiers: lin_addr : Int -/
def canonical_address_p (lin_addr : Int) : SailM Bool := do
  (signed_byte_p_int 48 lin_addr)

def Mk_cr0bits (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_cr3bits (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_cr4bits (v : (BitVec 22)) : (BitVec 22) :=
  v

def Mk_ia32_eferbits (v : (BitVec 12)) : (BitVec 12) :=
  v

def Mk_segment_selectorbits (v : (BitVec 16)) : (BitVec 16) :=
  v

def _get_cr0bits_wp (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_cr3bits_pdb (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_cr4bits_smap (v : (BitVec 22)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_cr4bits_smep (v : (BitVec 22)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ia32_eferbits_nxe (v : (BitVec 12)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_rflagsbits_ac (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_segment_selectorbits_rpl (v : (BitVec 16)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def Mk_ia32e_page_tablesbits (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ia32e_pml4ebits (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ia32e_pml4ebits_pdpt (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_ia32e_page_tablesbits_a (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def accessed_bit (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_a (Mk_ia32e_page_tablesbits entry))

def Mk_ia32e_pdpte_1gb_pagebits (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ia32e_pdpte_pg_dirbits (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ia32e_pdpte_1gb_pagebits_page (v : (BitVec 64)) : (BitVec 22) :=
  (Sail.BitVec.extractLsb v 51 30)

def _get_ia32e_pdpte_pg_dirbits_pd (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def _get_ia32e_page_tablesbits_d (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def dirty_bit (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_d (Mk_ia32e_page_tablesbits entry))

def Mk_ia32e_pde_2mb_pagebits (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ia32e_pde_pg_tablebits (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ia32e_pde_2mb_pagebits_page (v : (BitVec 64)) : (BitVec 31) :=
  (Sail.BitVec.extractLsb v 51 21)

def _get_ia32e_pde_pg_tablebits_pt (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def Mk_ia32e_pte_4k_pagebits (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ia32e_pte_4k_pagebits_page (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)

def page_table_entry_addr (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) : SailM (BitVec 52) := do
  assert ((← (unsigned_byte_p_int 52 (BitVec.toNatInt base_addr))) && ((loghead_bits 12 base_addr) == 0x000#12)) "././paging.sail:76.85-76.86"
  (pure (changeSlice_bits base_addr 3 9 (Sail.BitVec.extractLsb lin_addr 20 12)))

def _get_ia32e_page_tablesbits_xd (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def page_execute_disable (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_xd (Mk_ia32e_page_tablesbits entry))

def page_fault_err_no (p_flag : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) (rsvd : (BitVec 1)) (smep : (BitVec 1)) (pae : (BitVec 1)) (nxe : (BitVec 1)) : Int :=
  (logior_int
    (if ((p_flag == 1#1) : Bool)
    then 1
    else 0)
    (if ((r_w_x == ":W") : Bool)
    then 2
    else 0))

/-- Type quantifiers: err_no : Int -/
def page_fault_exception (addr : (BitVec 48)) (err_no : Int) : SailM (Bool × Int) := do
  let old_faults ← (( do (fault ()) ) : SailM Bool )
  let new_faults : ((String × (Int × (sbits 48))) × Bool) :=
    ((":PAGE-FAULT", (err_no, addr)), old_faults)
  (x86_fault "(!fault new-faults x86)")
  (pure (true, 0))

def _get_ia32e_page_tablesbits_p (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def page_present (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_p (Mk_ia32e_page_tablesbits entry))

def _get_ia32e_page_tablesbits_r_w (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def page_read_write (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_r_w (Mk_ia32e_page_tablesbits entry))

def _get_ia32e_page_tablesbits_ps (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def page_size (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_ps (Mk_ia32e_page_tablesbits entry))

def _get_ia32e_page_tablesbits_u_s (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def page_user_supervisor (entry : (BitVec 64)) : (BitVec 1) :=
  (_get_ia32e_page_tablesbits_u_s (Mk_ia32e_page_tablesbits entry))

def paging_entry_no_page_fault_p (structure_type : (BitVec 2)) (lin_addr : (BitVec 48)) (entry : (BitVec 64)) (u_s_acc : (BitVec 1)) (r_w_acc : (BitVec 1)) (x_d_acc : (BitVec 1)) (wp : (BitVec 1)) (smep : (BitVec 1)) (smap : (BitVec 1)) (ac : (BitVec 1)) (nxe : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) (keywords : struct_paging_entry_no_page_fault_p) : SailM (Bool × Int) := do
  let entry : (BitVec 64) := (loghead_bits 64 entry)
  let page_present_var : (BitVec 1) := (page_present entry)
  if ((page_present_var == 0#1) : Bool)
  then
    (do
      let err_no : Int := (page_fault_err_no page_present_var r_w_x cpl 0#1 smep 1#1 nxe)
      (page_fault_exception lin_addr err_no))
  else
    (do
      let read_write : (BitVec 1) := (page_read_write entry)
      let r_w_all : (BitVec 1) := (read_write &&& r_w_acc)
      let user_supervisor : (BitVec 1) := (page_user_supervisor entry)
      let u_s_all : (BitVec 1) := (user_supervisor &&& u_s_acc)
      let execute_disable : (BitVec 1) := (page_execute_disable entry)
      let x_d_all : (BitVec 1) := (execute_disable &&& x_d_acc)
      let page_size_var : (BitVec 1) := (page_size entry)
      let rsvd : Int :=
        if ((((structure_type == 0b11#2) && (page_size_var == 1#1)) || (((! (structure_type == 0b00#2)) && ((! (structure_type == 0b11#2)) && ((page_size_var == 1#1) && (if ((structure_type == 0b01#2) : Bool)
                     then (! ((Sail.BitVec.extractLsb entry 20 13) == 0x00#8))
                     else (! ((Sail.BitVec.extractLsb entry 29 13) == 0b00000000000000000#17)))))) || ((nxe == 0#1) && (! (execute_disable == 0#1))))) : Bool)
        then 1
        else 0
      if ((rsvd == 1) : Bool)
      then
        (do
          let err_no : Int :=
            (page_fault_err_no page_present_var r_w_x cpl (bits_of_int rsvd 1) smep 1#1 nxe)
          (page_fault_exception lin_addr err_no))
      else
        (do
          if ((((r_w_x == ":R") && (if (((BitVec.toNatInt cpl) <b 3) : Bool)
                 then
                   (if ((u_s_all == 0#1) : Bool)
                   then false
                   else
                     (if ((smap == 0#1) : Bool)
                     then false
                     else ((keywords.supervisor_mode_access_type == 1) || (ac == 0#1))))
                 else (u_s_all == 0#1))) || (((r_w_x == ":W") && (if (((BitVec.toNatInt cpl) <b 3) : Bool)
                   then
                     (if ((u_s_all == 0#1) : Bool)
                     then ((wp == 1#1) && (r_w_all == 0#1))
                     else
                       (if ((wp == 0#1) : Bool)
                       then
                         (if ((smap == 0#1) : Bool)
                         then false
                         else ((keywords.supervisor_mode_access_type == 1) || (ac == 0#1)))
                       else
                         (if ((smap == 0#1) : Bool)
                         then (r_w_all == 0#1)
                         else
                           (if (((keywords.supervisor_mode_access_type == 0) && (ac == 1#1)) : Bool)
                           then (r_w_all == 0#1)
                           else true))))
                   else ((u_s_all == 0#1) || (r_w_all == 0#1)))) || ((r_w_x == ":X") && (if (((BitVec.toNatInt
                          cpl) <b 3) : Bool)
                   then
                     (if ((u_s_all == 0#1) : Bool)
                     then
                       (if ((nxe == 0#1) : Bool)
                       then false
                       else (x_d_all == 1#1))
                     else
                       (if ((smep == 0#1) : Bool)
                       then
                         (if ((nxe == 0#1) : Bool)
                         then false
                         else (x_d_all == 1#1))
                       else true))
                   else ((u_s_all == 0#1) || ((nxe == 1#1) && (x_d_all == 1#1))))))) : Bool)
          then
            (do
              let err_no : Int :=
                (page_fault_err_no page_present_var r_w_x cpl (bits_of_int rsvd 1) smep 1#1 nxe)
              (page_fault_exception lin_addr err_no))
          else (pure (false, 0))))

/-- Type quantifiers: addr : Int -/
def rm_low_32 (addr : Int) : SailM (BitVec 32) := do
  assert (! (← readReg app_view)) "./././physical_memory.sail:12.29-12.30"
  let byte0 ← (( do (pure (loghead_bits 8 (← (memi (bits_of_int addr 64))))) ) : SailM
    (BitVec 8) )
  let byte1 ← (( do (pure (loghead_bits 8 (← (memi (bits_of_int (1 +i addr) 64))))) ) : SailM
    (BitVec 8) )
  let word0 : (BitVec 16) :=
    ((bits_of_int (ash_left_int (BitVec.toNatInt byte1) 8) 16) ||| (Sail.BitVec.zeroExtend byte0 16))
  let byte2 ← (( do (pure (loghead_bits 8 (← (memi (bits_of_int (2 +i addr) 64))))) ) : SailM
    (BitVec 8) )
  let byte3 ← (( do (pure (loghead_bits 8 (← (memi (bits_of_int (3 +i addr) 64))))) ) : SailM
    (BitVec 8) )
  let word1 : (BitVec 16) :=
    ((bits_of_int (ash_left_int (BitVec.toNatInt byte3) 8) 16) ||| (Sail.BitVec.zeroExtend byte2 16))
  (pure ((bits_of_int (ash_left_int (BitVec.toNatInt word1) 16) 32) ||| (Sail.BitVec.zeroExtend
        word0 32)))

/-- Type quantifiers: addr : Int -/
def rm_low_64 (addr : Int) : SailM (BitVec 64) := do
  assert (! (← readReg app_view)) "./././physical_memory.sail:41.29-41.30"
  let dword0 ← (( do (rm_low_32 addr) ) : SailM (BitVec 32) )
  let dword1 ← (( do (rm_low_32 (4 +i addr)) ) : SailM (BitVec 32) )
  (pure ((bits_of_int (ash_left_int (BitVec.toNatInt dword1) 32) 64) ||| (Sail.BitVec.zeroExtend
        dword0 64)))

def _update_ia32e_page_tablesbits_a (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def set_accessed_bit (entry : (BitVec 64)) : (BitVec 64) :=
  (_update_ia32e_page_tablesbits_a (Mk_ia32e_page_tablesbits entry) 1#1)

def _update_ia32e_page_tablesbits_d (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def set_dirty_bit (entry : (BitVec 64)) : (BitVec 64) :=
  (_update_ia32e_page_tablesbits_d (Mk_ia32e_page_tablesbits entry) 1#1)

def wm_low_32 (addr : (BitVec 52)) (sailval : (BitVec 32)) : SailM Unit := do
  assert (! (← readReg app_view)) "./././physical_memory.sail:26.29-26.30"
  let addr : Int := (BitVec.toNatInt addr)
  let byte0 : (BitVec 8) := (Sail.BitVec.extractLsb sailval 7 0)
  let byte1 : (BitVec 8) := (Sail.BitVec.extractLsb sailval 15 8)
  let byte2 : (BitVec 8) := (Sail.BitVec.extractLsb sailval 23 16)
  let byte3 : (BitVec 8) := (Sail.BitVec.extractLsb sailval 31 24)
  (bang_memi (bits_of_int addr 64) byte0)
  (bang_memi (bits_of_int (1 +i addr) 64) byte1)
  (bang_memi (bits_of_int (2 +i addr) 64) byte2)
  (bang_memi (bits_of_int (3 +i addr) 64) byte3)

def wm_low_64 (addr : (BitVec 52)) (sailval : (BitVec 64)) : SailM Unit := do
  assert (! (← readReg app_view)) "./././physical_memory.sail:51.29-51.30"
  let addr : Int := (BitVec.toNatInt addr)
  let dword0 : (BitVec 32) := (Sail.BitVec.extractLsb sailval 31 0)
  let dword1 : (BitVec 32) := (Sail.BitVec.extractLsb sailval 63 32)
  (wm_low_32 (bits_of_int addr 52) dword0)
  (wm_low_32 (bits_of_int (4 +i addr) 52) dword1)

def ia32e_la_to_pa_page_table (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) (u_s_acc : (BitVec 1)) (r_w_acc : (BitVec 1)) (x_d_acc : (BitVec 1)) (wp : (BitVec 1)) (smep : (BitVec 1)) (smap : (BitVec 1)) (ac : (BitVec 1)) (nxe : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) : SailM Int := do
  assert (! (← readReg app_view)) "././paging.sail:217.29-217.30"
  let lin_addr ← (( do (binary_logext 48 (BitVec.toNatInt (loghead_bits 48 lin_addr))) ) : SailM
    Int )
  let base_addr : (BitVec 52) := (changeSlice_bits (loghead_bits 52 base_addr) 0 12 0x000#12)
  let p_entry_addr ← (( do (page_table_entry_addr (bits_of_int lin_addr 48) base_addr) ) : SailM
    (BitVec 52) )
  let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
  let (fault_flg, sailval) ← (( do
    (paging_entry_no_page_fault_p 0b00#2 (bits_of_int lin_addr 48) entry u_s_acc r_w_acc x_d_acc wp
      smep smap ac nxe r_w_x cpl { supervisor_mode_access_type := 0 }) ) : SailM (Bool × Int) )
  if (fault_flg : Bool)
  then (x86_model_error "Page-Fault")
  else (pure ())
  if ((← readReg marking_view) : Bool)
  then
    (do
      let accessed : (BitVec 1) := (accessed_bit entry)
      let dirty : (BitVec 1) := (dirty_bit entry)
      let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
        if ((accessed == 0#1) : Bool)
        then (true, (set_accessed_bit entry))
        else (false, (Mk_ia32e_page_tablesbits entry))
      let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
        if (((dirty == 0#1) && (r_w_x == ":W")) : Bool)
        then (true, (set_dirty_bit entry))
        else (updated?, entry)
      if (updated? : Bool)
      then (wm_low_64 p_entry_addr entry)
      else (pure ()))
  else (pure ())
  (pure (changeSlice_int
      (ash_left_int
        (BitVec.toNatInt (_get_ia32e_pte_4k_pagebits_page (Mk_ia32e_pte_4k_pagebits entry))) 12) 0
      12 (BitVec.toNatInt (get_slice_int 12 lin_addr 0))))

def page_directory_entry_addr (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) : SailM (BitVec 52) := do
  assert ((← (unsigned_byte_p_int 52 (BitVec.toNatInt base_addr))) && ((loghead_bits 12 base_addr) == 0x000#12)) "././paging.sail:83.85-83.86"
  (pure (changeSlice_bits base_addr 3 9 (Sail.BitVec.extractLsb lin_addr 29 21)))

def ia32e_la_to_pa_page_directory (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) (u_s_acc : (BitVec 1)) (r_w_acc : (BitVec 1)) (x_d_acc : (BitVec 1)) (wp : (BitVec 1)) (smep : (BitVec 1)) (smap : (BitVec 1)) (ac : (BitVec 1)) (nxe : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) : SailM Int := do
  assert (! (← readReg app_view)) "././paging.sail:252.29-252.30"
  let lin_addr ← (( do (binary_logext 48 (BitVec.toNatInt (loghead_bits 48 lin_addr))) ) : SailM
    Int )
  let base_addr : (BitVec 52) := (changeSlice_bits (loghead_bits 52 base_addr) 0 12 0x000#12)
  let p_entry_addr ← (( do (page_directory_entry_addr (bits_of_int lin_addr 48) base_addr) ) :
    SailM (BitVec 52) )
  let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
  let u_s_all : (BitVec 1) := (u_s_acc &&& (page_user_supervisor entry))
  let r_w_all : (BitVec 1) := (r_w_acc &&& (page_read_write entry))
  let x_d_all : (BitVec 1) := (x_d_acc &&& (page_execute_disable entry))
  let (fault_flg, sailval) ← (( do
    (paging_entry_no_page_fault_p 0b01#2 (bits_of_int lin_addr 48) entry u_s_all r_w_all x_d_all wp
      smep smap ac nxe r_w_x cpl { supervisor_mode_access_type := 0 }) ) : SailM (Bool × Int) )
  if (fault_flg : Bool)
  then (x86_model_error "Page-Fault")
  else (pure ())
  if (((page_size entry) == 1#1) : Bool)
  then
    (do
      if ((← readReg marking_view) : Bool)
      then
        (do
          let accessed : (BitVec 1) := (accessed_bit entry)
          let dirty : (BitVec 1) := (dirty_bit entry)
          let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
            if ((accessed == 0#1) : Bool)
            then (true, (set_accessed_bit entry))
            else (false, (Mk_ia32e_page_tablesbits entry))
          let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
            if (((dirty == 0#1) && (r_w_x == ":W")) : Bool)
            then (true, (set_dirty_bit entry))
            else (updated?, entry)
          if (updated? : Bool)
          then (wm_low_64 p_entry_addr entry)
          else (pure ()))
      else (pure ())
      (pure (changeSlice_int
          (ash_left_int
            (BitVec.toNatInt (_get_ia32e_pde_2mb_pagebits_page (Mk_ia32e_pde_2mb_pagebits entry)))
            21) 0 21 (BitVec.toNatInt (get_slice_int 21 lin_addr 0)))))
  else
    (do
      let page_table_base_addr : Int :=
        (ash_left_int
          (BitVec.toNatInt (_get_ia32e_pde_pg_tablebits_pt (Mk_ia32e_pde_pg_tablebits entry))) 12)
      let p_addr ← (( do
        (pure (bits_of_int
            (← (ia32e_la_to_pa_page_table (bits_of_int lin_addr 48)
                (bits_of_int page_table_base_addr 52) u_s_all r_w_all x_d_all wp smep smap ac nxe
                r_w_x cpl)) 52)) ) : SailM (BitVec 52) )
      if ((← readReg marking_view) : Bool)
      then
        (do
          let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
          let accessed : (BitVec 1) := (accessed_bit entry)
          let entry : ia32e_page_tablesbits :=
            if ((accessed == 0#1) : Bool)
            then (set_accessed_bit entry)
            else (Mk_ia32e_page_tablesbits entry)
          if ((accessed == 0#1) : Bool)
          then (wm_low_64 p_entry_addr entry)
          else (pure ()))
      else (pure ())
      (pure (BitVec.toNatInt p_addr)))

def page_dir_ptr_table_entry_addr (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) : SailM (BitVec 52) := do
  assert ((← (unsigned_byte_p_int 52 (BitVec.toNatInt base_addr))) && ((loghead_bits 12 base_addr) == 0x000#12)) "././paging.sail:90.85-90.86"
  (pure (changeSlice_bits base_addr 3 9 (Sail.BitVec.extractLsb lin_addr 38 30)))

def ia32e_la_to_pa_page_dir_ptr_table (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) (u_s_acc : (BitVec 1)) (r_w_acc : (BitVec 1)) (x_d_acc : (BitVec 1)) (wp : (BitVec 1)) (smep : (BitVec 1)) (smap : (BitVec 1)) (ac : (BitVec 1)) (nxe : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) : SailM Int := do
  assert (! (← readReg app_view)) "././paging.sail:311.29-311.30"
  let lin_addr ← (( do (binary_logext 48 (BitVec.toNatInt (loghead_bits 48 lin_addr))) ) : SailM
    Int )
  let base_addr : (BitVec 52) := (changeSlice_bits (loghead_bits 52 base_addr) 0 12 0x000#12)
  let p_entry_addr ← (( do (page_dir_ptr_table_entry_addr (bits_of_int lin_addr 48) base_addr) ) :
    SailM (BitVec 52) )
  let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
  let u_s_all : (BitVec 1) := (u_s_acc &&& (page_user_supervisor entry))
  let r_w_all : (BitVec 1) := (r_w_acc &&& (page_read_write entry))
  let x_d_all : (BitVec 1) := (x_d_acc &&& (page_execute_disable entry))
  let (fault_flg, sailval) ← (( do
    (paging_entry_no_page_fault_p 0b10#2 (bits_of_int lin_addr 48) entry u_s_all r_w_all x_d_all wp
      smep smap ac nxe r_w_x cpl { supervisor_mode_access_type := 0 }) ) : SailM (Bool × Int) )
  if (fault_flg : Bool)
  then (x86_model_error "Page-Fault")
  else (pure ())
  if (((page_size entry) == 1#1) : Bool)
  then
    (do
      if ((← readReg marking_view) : Bool)
      then
        (do
          let accessed : (BitVec 1) := (accessed_bit entry)
          let dirty : (BitVec 1) := (dirty_bit entry)
          let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
            if ((accessed == 0#1) : Bool)
            then (true, (set_accessed_bit entry))
            else (false, (Mk_ia32e_page_tablesbits entry))
          let (updated?, entry) : (Bool × ia32e_page_tablesbits) :=
            if (((dirty == 0#1) && (r_w_x == ":W")) : Bool)
            then (true, (set_dirty_bit entry))
            else (updated?, entry)
          if (updated? : Bool)
          then (wm_low_64 p_entry_addr entry)
          else (pure ()))
      else (pure ())
      (pure (changeSlice_int
          (ash_left_int
            (BitVec.toNatInt
              (_get_ia32e_pdpte_1gb_pagebits_page (Mk_ia32e_pdpte_1gb_pagebits entry))) 30) 0 30
          (BitVec.toNatInt (get_slice_int 30 lin_addr 0)))))
  else
    (do
      let page_directory_base_addr : Int :=
        (ash_left_int
          (BitVec.toNatInt (_get_ia32e_pdpte_pg_dirbits_pd (Mk_ia32e_pdpte_pg_dirbits entry))) 12)
      let p_addr ← (( do
        (pure (bits_of_int
            (← (ia32e_la_to_pa_page_directory (bits_of_int lin_addr 48)
                (bits_of_int page_directory_base_addr 52) u_s_all r_w_all x_d_all wp smep smap ac
                nxe r_w_x cpl)) 52)) ) : SailM (BitVec 52) )
      if ((← readReg marking_view) : Bool)
      then
        (do
          let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
          let accessed : (BitVec 1) := (accessed_bit entry)
          let entry : ia32e_page_tablesbits :=
            if ((accessed == 0#1) : Bool)
            then (set_accessed_bit entry)
            else (Mk_ia32e_page_tablesbits entry)
          if ((accessed == 0#1) : Bool)
          then (wm_low_64 p_entry_addr entry)
          else (pure ()))
      else (pure ())
      (pure (BitVec.toNatInt p_addr)))

def pml4_table_entry_addr (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) : SailM (BitVec 52) := do
  assert ((← (unsigned_byte_p_int 52 (BitVec.toNatInt base_addr))) && ((loghead_bits 12 base_addr) == 0x000#12)) "././paging.sail:97.85-97.86"
  (pure (changeSlice_bits base_addr 3 9 (Sail.BitVec.extractLsb lin_addr 47 39)))

def ia32e_la_to_pa_pml4_table (lin_addr : (BitVec 48)) (base_addr : (BitVec 52)) (wp : (BitVec 1)) (smep : (BitVec 1)) (smap : (BitVec 1)) (ac : (BitVec 1)) (nxe : (BitVec 1)) (r_w_x : String) (cpl : (BitVec 2)) : SailM (BitVec 52) := do
  assert (! (← readReg app_view)) "././paging.sail:370.29-370.30"
  let lin_addr ← (( do (binary_logext 48 (BitVec.toNatInt (loghead_bits 48 lin_addr))) ) : SailM
    Int )
  let base_addr : (BitVec 52) := (changeSlice_bits (loghead_bits 52 base_addr) 0 12 0x000#12)
  let p_entry_addr ← (( do (pml4_table_entry_addr (bits_of_int lin_addr 48) base_addr) ) : SailM
    (BitVec 52) )
  let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
  let u_s_all : (BitVec 1) := (page_user_supervisor entry)
  let r_w_all : (BitVec 1) := (page_read_write entry)
  let x_d_all : (BitVec 1) := (page_execute_disable entry)
  let (fault_flg, sailval) ← (( do
    (paging_entry_no_page_fault_p 0b11#2 (bits_of_int lin_addr 48) entry u_s_all r_w_all x_d_all wp
      smep smap ac nxe r_w_x cpl { supervisor_mode_access_type := 0 }) ) : SailM (Bool × Int) )
  if (fault_flg : Bool)
  then (x86_model_error "Page-Fault")
  else (pure ())
  let page_dir_ptr_table_base_addr : Int :=
    (ash_left_int (BitVec.toNatInt (_get_ia32e_pml4ebits_pdpt (Mk_ia32e_pml4ebits entry))) 12)
  let p_addr ← (( do
    (pure (bits_of_int
        (← (ia32e_la_to_pa_page_dir_ptr_table (bits_of_int lin_addr 48)
            (bits_of_int page_dir_ptr_table_base_addr 52) u_s_all r_w_all x_d_all wp smep smap ac
            nxe r_w_x cpl)) 52)) ) : SailM (BitVec 52) )
  if ((← readReg marking_view) : Bool)
  then
    (do
      let entry ← (( do (rm_low_64 (BitVec.toNatInt p_entry_addr)) ) : SailM (BitVec 64) )
      let accessed : (BitVec 1) := (accessed_bit entry)
      let entry : ia32e_page_tablesbits :=
        if ((accessed == 0#1) : Bool)
        then (set_accessed_bit entry)
        else (Mk_ia32e_page_tablesbits entry)
      if ((accessed == 0#1) : Bool)
      then (wm_low_64 p_entry_addr entry)
      else (pure ()))
  else (pure ())
  (pure p_addr)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 6 -/
def read_msr (idx : Nat) : SailM (BitVec 64) := do
  (pure (GetElem?.getElem! (← readReg msrs) idx))

def ia32e_la_to_pa (lin_addr : (BitVec 48)) (r_w_x : String) : SailM (BitVec 52) := do
  assert (! (← readReg app_view)) "././paging.sail:401.29-401.30"
  let lin_addr ← (( do (binary_logext 48 (BitVec.toNatInt (loghead_bits 48 lin_addr))) ) : SailM
    Int )
  let cr0 ← (( do (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg ctrs) 0) 32)) ) :
    SailM (BitVec 32) )
  let cr4 ← (( do (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg ctrs) 4) 22)) ) :
    SailM (BitVec 22) )
  let cpl ← (( do
    (pure (_get_segment_selectorbits_rpl
        (Mk_segment_selectorbits (GetElem?.getElem! (← readReg seg_visibles) 1)))) ) : SailM
    (BitVec 2) )
  let ia32_efer ← (( do (pure (Sail.BitVec.truncate (← (read_msr 0)) 12)) ) : SailM (BitVec 12)
    )
  let wp : (BitVec 1) := (_get_cr0bits_wp (Mk_cr0bits cr0))
  let smep : (BitVec 1) := (_get_cr4bits_smep (Mk_cr4bits cr4))
  let smap : (BitVec 1) := (_get_cr4bits_smap (Mk_cr4bits cr4))
  let ac ← (( do (pure (_get_rflagsbits_ac (← readReg rflags))) ) : SailM (BitVec 1) )
  let nxe : (BitVec 1) := (_get_ia32_eferbits_nxe (Mk_ia32_eferbits ia32_efer))
  let cr3 ← (( do (pure (GetElem?.getElem! (← readReg ctrs) 3)) ) : SailM (BitVec 64) )
  let pml4_table_base_addr : Int :=
    (ash_left_int (BitVec.toNatInt (_get_cr3bits_pdb (Mk_cr3bits cr3))) 12)
  (ia32e_la_to_pa_pml4_table (bits_of_int lin_addr 48) (bits_of_int pml4_table_base_addr 52) wp smep
    smap ac nxe r_w_x cpl)

/-- Type quantifiers: k_addr_width : Nat, n : Nat, k_addr_width > 0 ∧ n > 0 -/
def rb (n : Nat) (addr : (BitVec k_addr_width)) (access_kind : String) : SailM (BitVec (8 * n)) := do
  let result : (BitVec (8 * n)) := (BitVec.zero (8 *i n))
  let loop_offset_lower := 0
  let loop_offset_upper := (n -i 1)
  let mut loop_vars := result
  for offset in [loop_offset_lower:loop_offset_upper:1]i do
    let result := loop_vars
    loop_vars ← do
      if ((! (← (canonical_address_p ((BitVec.toInt addr) +i offset)))) : Bool)
      then (x86_model_error "rb: non-canonical address")
      else (pure ())
      let lin_addr : (BitVec 48) := (BitVec.addInt (sail_mask_signed 48 addr) offset)
      let phys_addr ← (( do
        if ((← readReg app_view) : Bool)
        then (pure (sail_mask_signed 52 lin_addr))
        else (ia32e_la_to_pa lin_addr access_kind) ) : SailM (BitVec 52) )
      (pure (Sail.BitVec.updateSubrange result ((8 *i offset) +i 7) (8 *i offset)
          (← (memi phys_addr))))
  (pure loop_vars)

/-- Type quantifiers: len : Int -/
def observe_mem_write (addr : (BitVec 48)) (len : Int) : Unit :=
  ()

/-- Type quantifiers: k_addr_width : Nat, n : Nat, k_addr_width > 0 ∧ n > 0 -/
def wb (n : Nat) (addr : (BitVec k_addr_width)) (access_kind : String) (value : (BitVec (8 * n))) : SailM Unit := do
  let loop_offset_lower := 0
  let loop_offset_upper := (n -i 1)
  let mut loop_vars := ()
  for offset in [loop_offset_lower:loop_offset_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((! (← (canonical_address_p ((BitVec.toInt addr) +i offset)))) : Bool)
      then
        (do
          let _ : Unit :=
            if ((offset != 0) : Bool)
            then (observe_mem_write (sail_mask_signed 48 addr) (offset -i 1))
            else ()
          (x86_model_error "wb: non-canonical address"))
      else (pure ())
      let lin_addr : (BitVec 48) := (BitVec.addInt (sail_mask_signed 48 addr) offset)
      let phys_addr ← (( do
        if ((← readReg app_view) : Bool)
        then (pure (sail_mask_signed 52 lin_addr))
        else (ia32e_la_to_pa lin_addr access_kind) ) : SailM (BitVec 52) )
      (bang_memi phys_addr (Sail.BitVec.extractLsb value ((8 *i offset) +i 7) (8 *i offset)))
  (pure loop_vars)
  let dummy := (observe_mem_write (sail_mask_signed 48 addr) n)
  (pure ())

def regval_into_reg (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_modr_m_mod (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_modr_m_r_m (v : (BitVec 8)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_modr_m_reg (v : (BitVec 8)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _get_sib_base (v : (BitVec 8)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_sib_index (v : (BitVec 8)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _get_sib_scale (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def undefined_rflagsbits (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_cr0bits_am (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 15 -/
def read_gpr (idx : Nat) : SailM (BitVec 64) := do
  match idx with
  | 0 => readReg rax
  | 1 => readReg rcx
  | 2 => readReg rdx
  | 3 => readReg rbx
  | 4 => readReg rsp
  | 5 => readReg rbp
  | 6 => readReg rsi
  | 7 => readReg rdi
  | 8 => readReg r8
  | 9 => readReg r9
  | 10 => readReg r10
  | 11 => readReg r11
  | 12 => readReg r12
  | 13 => readReg r13
  | 14 => readReg r14
  | _ => readReg r15

/-- Type quantifiers: regNum : Int -/
def rgfi (regNum : Int) : SailM (BitVec 64) := do
  assert ((0 ≤b regNum) && (regNum <b 16)) "register_accessors.sail:6.36-6.37"
  (pure (regval_from_reg (← (read_gpr regNum))))

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 15 -/
def log_gpr_write (idx : Nat) : SailM Unit := do
  match idx with
  | 0 => (pure (print_bits "rax = " (← (rgfi 0))))
  | 1 => (pure (print_bits "rcx = " (← (rgfi 1))))
  | 2 => (pure (print_bits "rdx = " (← (rgfi 2))))
  | 3 => (pure (print_bits "rbx = " (← (rgfi 3))))
  | 4 => (pure (print_bits "rsp = " (← (rgfi 4))))
  | 5 => (pure (print_bits "rbp = " (← (rgfi 5))))
  | 6 => (pure (print_bits "rsi = " (← (rgfi 6))))
  | 7 => (pure (print_bits "rdi = " (← (rgfi 7))))
  | 8 => (pure (print_bits "r8 = " (← (rgfi 8))))
  | 9 => (pure (print_bits "r9 = " (← (rgfi 9))))
  | 10 => (pure (print_bits "r10 = " (← (rgfi 10))))
  | 11 => (pure (print_bits "r11 = " (← (rgfi 11))))
  | 12 => (pure (print_bits "r12 = " (← (rgfi 12))))
  | 13 => (pure (print_bits "r13 = " (← (rgfi 13))))
  | 14 => (pure (print_bits "r14 = " (← (rgfi 14))))
  | _ => (pure (print_bits "r15 = " (← (rgfi 15))))

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 15 -/
def write_gpr (idx : Nat) (value : (BitVec 64)) : SailM Unit := do
  match idx with
  | 0 => writeReg rax value
  | 1 => writeReg rcx value
  | 2 => writeReg rdx value
  | 3 => writeReg rbx value
  | 4 => writeReg rsp value
  | 5 => writeReg rbp value
  | 6 => writeReg rsi value
  | 7 => writeReg rdi value
  | 8 => writeReg r8 value
  | 9 => writeReg r9 value
  | 10 => writeReg r10 value
  | 11 => writeReg r11 value
  | 12 => writeReg r12 value
  | 13 => writeReg r13 value
  | 14 => writeReg r14 value
  | _ => writeReg r15 value
  if ((← readReg log_register_writes) : Bool)
  then (log_gpr_write idx)
  else (pure ())

/-- Type quantifiers: regNum : Int -/
def write_rgfi (regNum : Int) (regval_to_write : (BitVec 64)) : SailM Unit := do
  assert ((0 ≤b regNum) && (regNum <b 16)) "register_accessors.sail:12.36-12.37"
  (write_gpr regNum (regval_into_reg regval_to_write))

def log_rip_write (_ : Unit) : SailM Unit := do
  (pure (print_bits "rip = " (← (read_rip ()))))

def write_rip (value : (BitVec 48)) : SailM Unit := do
  writeReg rip (regval_into_reg (Sail.BitVec.signExtend value 64))
  if ((← readReg log_register_writes) : Bool)
  then (log_rip_write ())
  else (pure ())

def in_64bit_mode (proc_mode : proc_mode) : Bool :=
  match proc_mode with
  | .Mode_64bit => true
  | _ => false

def in_compatibility_mode (proc_mode : proc_mode) : Bool :=
  match proc_mode with
  | .Mode_Compatibility => true
  | _ => false

def _get_prefixes_adr (v : (BitVec 52)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 43 36)

def _get_prefixes_opr (v : (BitVec 52)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 35 28)

def _get_prefixes_seg (v : (BitVec 52)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 27 20)

def Mk_code_segment_descriptor_attributesbits (v : (BitVec 16)) : (BitVec 16) :=
  v

def _get_code_segment_descriptor_attributesbits_d (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_code_segment_descriptor_attributesbits_r (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def Mk_data_segment_descriptor_attributesbits (v : (BitVec 16)) : (BitVec 16) :=
  v

def _get_data_segment_descriptor_attributesbits_d_b (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_data_segment_descriptor_attributesbits_e (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_data_segment_descriptor_attributesbits_w (v : (BitVec 16)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def reg_index (reg : (BitVec 3)) (rex_byte : (BitVec 8)) (index : (BitVec 2)) : (BitVec 4) :=
  if ((logbitp_bits (BitVec.toNatInt index) rex_byte) : Bool)
  then (0x8#4 ||| (Sail.BitVec.zeroExtend reg 4))
  else (Sail.BitVec.zeroExtend reg 4)

def rr08 (reg : (BitVec 4)) (rex : (BitVec 8)) : SailM (BitVec 8) := do
  let reg : Nat := (BitVec.toNatInt reg)
  if (((! (rex == 0x00#8)) || (reg <b 4)) : Bool)
  then
    (do
      let qword ← (( do (rgfi reg) ) : SailM (sbits 64) )
      (pure (Sail.BitVec.truncate qword 8)))
  else
    (do
      let qword ← (( do (rgfi (BitVec.toNatInt (bits_of_int (reg -i 4) 4))) ) : SailM (sbits 64) )
      (pure (Sail.BitVec.extractLsb qword 15 8)))

def wr08 (reg : (BitVec 4)) (rex : (BitVec 8)) (byte : (BitVec 8)) : SailM Unit := do
  let reg : Nat := (BitVec.toNatInt reg)
  if (((! (rex == 0x00#8)) || (reg <b 4)) : Bool)
  then
    (do
      let qword ← (( do (rgfi reg) ) : SailM (sbits 64) )
      (write_rgfi reg (changeSlice_bits (Sail.BitVec.extractLsb qword 63 0) 0 8 byte)))
  else
    (do
      let index : (BitVec 4) := (bits_of_int ((BitVec.toNatInt (bits_of_int reg 4)) -i 4) 4)
      let qword ← (( do (rgfi (BitVec.toNatInt index)) ) : SailM (sbits 64) )
      (write_rgfi (BitVec.toNatInt index)
        (changeSlice_bits (Sail.BitVec.extractLsb qword 63 0) 8 8 byte)))

def rr16 (reg : (BitVec 4)) : SailM (BitVec 16) := do
  (pure (Sail.BitVec.truncate (← (rgfi (BitVec.toNatInt reg))) 16))

def wr16 (reg : (BitVec 4)) (sailval : (BitVec 16)) : SailM Unit := do
  let qword ← (( do (rgfi (BitVec.toNatInt reg)) ) : SailM (sbits 64) )
  (write_rgfi (BitVec.toNatInt reg)
    (changeSlice_bits (Sail.BitVec.extractLsb qword 63 0) 0 16 sailval))

def rr32 (reg : (BitVec 4)) : SailM (BitVec 32) := do
  (pure (Sail.BitVec.truncate (← (rgfi (BitVec.toNatInt reg))) 32))

def wr32 (reg : (BitVec 4)) (sailval : (BitVec 32)) : SailM Unit := do
  (write_rgfi (BitVec.toNatInt reg) (Sail.BitVec.zeroExtend sailval 64))

def rr64 (reg : (BitVec 4)) : SailM (BitVec 64) := do
  (rgfi (BitVec.toNatInt reg))

def wr64 (reg : (BitVec 4)) (sailval : (BitVec 64)) : SailM Unit := do
  (write_rgfi (BitVec.toNatInt reg) sailval)

def rgfi_size (nbytes : (BitVec 4)) (index : (BitVec 4)) (rex : (BitVec 8)) : SailM (BitVec 64) := do
  let v_8 := nbytes
  if ((eq_bits_nat v_8 1) : Bool)
  then (pure (Sail.BitVec.zeroExtend (← (rr08 index rex)) 64))
  else
    (do
      if ((eq_bits_nat v_8 2) : Bool)
      then (pure (Sail.BitVec.zeroExtend (← (rr16 index)) 64))
      else
        (do
          if ((eq_bits_nat v_8 4) : Bool)
          then (pure (Sail.BitVec.zeroExtend (← (rr32 index)) 64))
          else
            (do
              if ((eq_bits_nat v_8 8) : Bool)
              then (rr64 index)
              else (pure 0x0000000000000000#64))))

def write_rgfi_size (nbytes : (BitVec 4)) (index : (BitVec 4)) (sailval : (BitVec 64)) (rex : (BitVec 8)) : SailM Unit := do
  let v_12 := nbytes
  if ((eq_bits_nat v_12 1) : Bool)
  then (wr08 index rex (Sail.BitVec.truncate sailval 8))
  else
    (do
      if ((eq_bits_nat v_12 2) : Bool)
      then (wr16 index (Sail.BitVec.truncate sailval 16))
      else
        (do
          if ((eq_bits_nat v_12 4) : Bool)
          then (wr32 index (Sail.BitVec.truncate sailval 32))
          else
            (do
              if ((eq_bits_nat v_12 8) : Bool)
              then (wr64 index sailval)
              else (pure ()))))

/-- Type quantifiers: seg_reg : Nat, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def segment_base_and_bounds (proc_mode : proc_mode) (seg_reg : Nat) : SailM ((BitVec 64) × Int × (BitVec 32)) := do
  if ((in_64bit_mode proc_mode) : Bool)
  then
    (do
      if ((seg_reg == 4) : Bool)
      then (pure ((← (read_msr 1)), 0, 0x00000000#32))
      else
        (do
          if ((seg_reg == 5) : Bool)
          then (pure ((← (read_msr 2)), 0, 0x00000000#32))
          else (pure (0x0000000000000000#64, 0, 0x00000000#32))))
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let base ← (( do
            (pure (loghead_bits 64 (GetElem?.getElem! (← readReg seg_hidden_bases) seg_reg))) ) :
            SailM (BitVec 64) )
          let limit ← (( do
            (pure (loghead_bits 32 (GetElem?.getElem! (← readReg seg_hidden_limits) seg_reg))) ) :
            SailM (BitVec 32) )
          let attr ← (( do
            (pure (loghead_bits 16 (GetElem?.getElem! (← readReg seg_hidden_attrs) seg_reg))) ) :
            SailM (BitVec 16) )
          let d_b : (BitVec 1) :=
            if ((seg_reg == 1) : Bool)
            then
              (_get_code_segment_descriptor_attributesbits_d
                (Mk_code_segment_descriptor_attributesbits attr))
            else
              (_get_data_segment_descriptor_attributesbits_d_b
                (Mk_data_segment_descriptor_attributesbits attr))
          let e : (BitVec 1) :=
            if ((seg_reg == 1) : Bool)
            then 0#1
            else
              (_get_data_segment_descriptor_attributesbits_e
                (Mk_data_segment_descriptor_attributesbits attr))
          let lower : Int :=
            if ((e == 1#1) : Bool)
            then (1 +i (BitVec.toNatInt limit))
            else 0
          let upper : (BitVec 32) :=
            if ((e == 1#1) : Bool)
            then
              (if ((d_b == 1#1) : Bool)
              then 0xFFFFFFFF#32
              else 0x0000FFFF#32)
            else limit
          (pure ((Sail.BitVec.zeroExtend (Sail.BitVec.truncate base 32) 64), lower, upper)))
      else (pure (0x0000000000000000#64, 0, 0x00000000#32)))

/-- Type quantifiers: nbytes : Nat, seg_reg : Nat, 0 ≤ seg_reg ∧ seg_reg ≤ 5, nbytes ∈
  {1, 2, 4, 6, 8, 10, 16, 32, 64} -/
def ea_to_la (proc_mode : proc_mode) (eff_addr : (BitVec 64)) (seg_reg : Nat) (nbytes : Nat) : SailM (BitVec 64) := do
  if ((in_64bit_mode proc_mode) : Bool)
  then
    (do
      let lin_addr ← (( do
        if (((seg_reg == 4) || (seg_reg == 5)) : Bool)
        then
          (do
            let (base, _, _) ← (( do (segment_base_and_bounds Mode_64bit seg_reg) ) : SailM
              ((BitVec 64) × Int × (BitVec 32)) )
            (pure (bits_of_int ((BitVec.toNatInt base) +i (BitVec.toNatInt eff_addr)) 64)))
        else (pure eff_addr) ) : SailM (sbits 64) )
      if ((! (← (canonical_address_p (BitVec.toInt lin_addr)))) : Bool)
      then (x86_model_error ":NON-CANONICAL-ADDRESS")
      else (pure ())
      (pure lin_addr))
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          if (((! (seg_reg == 1)) && ((! (seg_reg == 2)) && (← do
                   (pure ((BitVec.toNatInt (GetElem?.getElem! (← readReg seg_visibles) seg_reg)) <b 4))))) : Bool)
          then (x86_model_error ":NULL-SEGMENT-SELECTOR")
          else (pure ())
          let (base, lower_bound, upper_bound) ← (( do (segment_base_and_bounds proc_mode seg_reg)
            ) : SailM ((BitVec 64) × Int × (BitVec 32)) )
          let base : (BitVec 32) := (Sail.BitVec.truncate base 32)
          let lower_bound : (BitVec 33) := (bits_of_int lower_bound 33)
          let first_addr : (sbits 64) := eff_addr
          let last_addr : Int := ((BitVec.toInt eff_addr) +i (nbytes +i (Neg.neg 1)))
          if ((! (((BitVec.toNatInt lower_bound) ≤b (BitVec.toInt first_addr)) && ((last_addr ≤b (BitVec.toNatInt
                     upper_bound)) : Bool))) : Bool)
          then (x86_model_error ":SEGMENT-LIMIT-FAIL")
          else (pure ())
          let lin_addr : (BitVec 32) :=
            (bits_of_int
              ((BitVec.toNatInt base) +i (BitVec.toNatInt (Sail.BitVec.truncate eff_addr 32))) 32)
          (pure (Sail.BitVec.zeroExtend lin_addr 64)))
      else (x86_model_error ":UNIMPLEMENTED-PROC-MODE"))

/-- Type quantifiers: k_ex33755_ : Bool, operand_size : Nat, operand_size ∈
  {1, 2, 4, 6, 8, 10, 16, 32, 64} -/
def address_aligned_p (addr : (BitVec 48)) (operand_size : Nat) (memory_ptr? : Bool) : SailM Bool := do
  match operand_size with
  | 1 => (pure true)
  | 6 => (pure ((addr &&& 0x000000000003#48) == 0x000000000000#48))
  | 10 => (pure ((addr &&& 0x000000000007#48) == 0x000000000000#48))
  | _ =>
    (do
      if ((memory_ptr? && (operand_size == 4)) : Bool)
      then (pure ((addr &&& 0x000000000001#48) == 0x000000000000#48))
      else
        (pure ((addr &&& (bits_of_int (← (check_range 0 65 (operand_size -i 1))) 48)) == 0x000000000000#48)))

/-- Type quantifiers: k_ex33760_ : Bool, k_ex33759_ : Bool, seg_reg : Nat, nbytes : Nat, addr_size :
  Nat, addr_size ∈ {2, 4, 8}, nbytes ∈ {1, 2, 4, 6, 8, 10, 16}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def check_linear_memory_access (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (lin_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (access_kind : String) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM Unit := do
  if ((! ((! check_alignment?) || (← (address_aligned_p (Sail.BitVec.truncate lin_addr 48) nbytes
             mem_ptr?)))) : Bool)
  then (x86_fault ":UNALIGNED-LINEAR-ADDRESS")
  else (pure ())

def select_base_register (proc_mode : proc_mode) (rex_byte : (BitVec 8)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) : (Option Nat) :=
  none

def select_address_size (proc_mode : proc_mode) (prefixes : (Option (BitVec 52))) : SailM Int := do
  let p4? : Bool :=
    match prefixes with
    | .some prefixes => (0x67#8 == (_get_prefixes_adr prefixes))
    | none => false
  if ((in_64bit_mode proc_mode) : Bool)
  then
    (if (p4? : Bool)
    then (pure 4)
    else (pure 8))
  else
    (do
      let cs_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 1)) ) : SailM
        (BitVec 16) )
      let cs_d : (BitVec 1) :=
        (_get_code_segment_descriptor_attributesbits_d
          (Mk_code_segment_descriptor_attributesbits cs_attr))
      if ((cs_d == 1#1) : Bool)
      then
        (if (p4? : Bool)
        then (pure 2)
        else (pure 4))
      else
        (if (p4? : Bool)
        then (pure 4)
        else (pure 2)))

def select_segment_register (proc_mode : proc_mode) (prefixes : (BitVec 52)) (mod_var : (BitVec 2)) (r_m : (BitVec 3)) (sib : (BitVec 8)) : SailM Nat := do
  let v_28 := (_get_prefixes_seg prefixes)
  if ((eq_bits_nat v_28 46) : Bool)
  then (pure 1)
  else
    (do
      if ((eq_bits_nat v_28 54) : Bool)
      then (pure 2)
      else
        (do
          if ((eq_bits_nat v_28 62) : Bool)
          then (pure 3)
          else
            (do
              if ((eq_bits_nat v_28 38) : Bool)
              then (pure 0)
              else
                (do
                  if ((eq_bits_nat v_28 100) : Bool)
                  then (pure 4)
                  else
                    (do
                      if ((eq_bits_nat v_28 101) : Bool)
                      then (pure 5)
                      else
                        (do
                          let addr_size ← (( do (select_address_size proc_mode (some prefixes)) )
                            : SailM Int )
                          if ((addr_size == 2) : Bool)
                          then
                            (if (((! (mod_var == 0b11#2)) && ((r_m == 0b010#3) || (r_m == 0b011#3))) : Bool)
                            then (pure 2)
                            else (pure 3))
                          else
                            (if (((((mod_var == 0b01#2) || (mod_var == 0b10#2)) && (r_m == 0b101#3)) || ((! (mod_var == 0b11#2)) && ((r_m == 0b100#3) && ((_get_sib_base
                                         sib) == 0b100#3)))) : Bool)
                            then (pure 2)
                            else (pure 3))))))))

/-- Type quantifiers: k_ex33764_ : Bool, k_ex33763_ : Bool, seg_reg : Nat, addr_size : Nat, nbytes :
  Nat, nbytes ∈ {1, 2, 4, 6, 8, 10, 16}, addr_size ∈ {2, 4, 8}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def load_bytes_from_ea (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (r_x : String) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM (BitVec (8 * nbytes)) := do
  let cs_attrs ← do
    (pure (Mk_code_segment_descriptor_attributesbits
        (GetElem?.getElem! (← readReg seg_hidden_attrs) 1)))
  if (((! (in_64bit_mode proc_mode)) && ((seg_reg == 1) && ((r_x == ":R") && ((_get_code_segment_descriptor_attributesbits_r
               cs_attrs) == 0#1)))) : Bool)
  then (x86_fault ":EXECUTE-ONLY-CODE-SEGMENT")
  else
    (do
      let lin_addr ← (( do (ea_to_la proc_mode eff_addr seg_reg nbytes) ) : SailM (sbits 64) )
      (check_linear_memory_access proc_mode addr_size nbytes lin_addr base_reg seg_reg r_x
        check_alignment? mem_ptr?)
      (rb nbytes lin_addr r_x))

/-- Type quantifiers: k_ex33768_ : Bool, k_ex33767_ : Bool, seg_reg : Nat, addr_size : Nat, nbytes :
  Nat, nbytes ∈ {1, 2, 4, 6, 8, 10, 16}, addr_size ∈ {2, 4, 8}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def store_bytes_to_ea (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (data : (BitVec (8 * nbytes))) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM Unit := do
  let seg_attrs ← do
    (pure (Mk_data_segment_descriptor_attributesbits
        (GetElem?.getElem! (← readReg seg_hidden_attrs) seg_reg)))
  if (((! (in_64bit_mode proc_mode)) && ((seg_reg == 1) || ((_get_data_segment_descriptor_attributesbits_w
             seg_attrs) == 0#1))) : Bool)
  then (x86_fault ":NON-WRITABLE-SEGMENT")
  else
    (do
      let lin_addr ← (( do (ea_to_la proc_mode eff_addr seg_reg nbytes) ) : SailM (sbits 64) )
      (check_linear_memory_access proc_mode addr_size nbytes lin_addr base_reg seg_reg ":W"
        check_alignment? mem_ptr?)
      (wb nbytes lin_addr ":W" data))

/-- Type quantifiers: k_ex33773_ : Bool, k_ex33772_ : Bool, seg_reg : Nat, nbytes : Nat, addr_size :
  Nat, addr_size ∈ {2, 4, 8}, nbytes ∈ {1, 2, 4, 6, 8}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def rime_size (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (r_x : String) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM (BitVec 64) := do
  (pure (Sail.BitVec.signExtend
      (← (load_bytes_from_ea proc_mode addr_size nbytes eff_addr base_reg seg_reg r_x
          check_alignment? mem_ptr?)) 64))

/-- Type quantifiers: k_ex33777_ : Bool, k_ex33776_ : Bool, seg_reg : Nat, addr_size : Nat, nbytes :
  Nat, nbytes ∈ {1, 2, 4, 6, 8, 10, 16}, addr_size ∈ {2, 4, 8}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def wme_size (proc_mode : proc_mode) (addr_size : Nat) (nbytes : Nat) (eff_addr : (BitVec 64)) (base_reg : (Option Nat)) (seg_reg : Nat) (data : (BitVec 128)) (check_alignment? : Bool) (mem_ptr? : Bool) : SailM Unit := do
  (store_bytes_to_ea proc_mode addr_size nbytes eff_addr base_reg seg_reg
    (Sail.BitVec.truncate data (8 *i nbytes)) check_alignment? mem_ptr?)

def add_to_iptr (proc_mode : proc_mode) (iptr : (BitVec 48)) (delta : (BitVec 48)) : SailM (BitVec 48) := do
  let iptr_plus_delta : (sbits 49) := (bits_of_int ((BitVec.toInt iptr) +i (BitVec.toInt delta)) 49)
  if ((in_64bit_mode proc_mode) : Bool)
  then
    (do
      if ((← (canonical_address_p (BitVec.toInt iptr_plus_delta))) : Bool)
      then (pure (Sail.BitVec.truncate iptr_plus_delta 48))
      else (x86_model_error ":NON-CANONICAL-INSTRUCTION-POINTER"))
  else
    (do
      if ((in_compatibility_mode proc_mode) : Bool)
      then
        (do
          let cs_limit ← (( do
            (pure (loghead_bits 32 (GetElem?.getElem! (← readReg seg_hidden_limits) 1))) ) : SailM
            (BitVec 32) )
          if (((0 ≤b (BitVec.toInt iptr_plus_delta)) && (((BitVec.toInt iptr_plus_delta) ≤b (BitVec.toNatInt
                   cs_limit)) : Bool)) : Bool)
          then
            (pure (Sail.BitVec.truncate
                (Sail.BitVec.zeroExtend (Sail.BitVec.truncate iptr_plus_delta 32) 49) 48))
          else (x86_model_error ":OUT-OF-SEGMENT-INSTRUCTION-POINTER"))
      else (x86_model_error ":UNIMPLEMENTED-PROC-MODE"))

def write_iptr (proc_mode : proc_mode) (iptr : (BitVec 48)) : SailM Unit := do
  if ((in_64bit_mode proc_mode) : Bool)
  then (write_rip iptr)
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
          then (write_rip (Sail.BitVec.zeroExtend (Sail.BitVec.truncate iptr 32) 48))
          else
            (do
              let rip_var ← (( do (read_rip ()) ) : SailM (sbits 48) )
              let rip_new : (sbits 48) :=
                (changeSlice_bits rip_var 0 16 (Sail.BitVec.truncate iptr 16))
              (write_rip rip_new)))
      else (pure ()))

def x86_effective_addr_from_sib (proc_mode : proc_mode) (temp_rip : (BitVec 48)) (rex_byte : (BitVec 8)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) : SailM (Int × (BitVec 64) × Int) := do
  let b : (BitVec 3) := (_get_sib_base sib)
  let check_alignment? : Bool := false
  let (base, displacement, nrip_bytes) ← (( do
    let v_34 := mod_var
    if ((eq_bits_nat v_34 0) : Bool)
    then
      (do
        if ((b == 0b101#3) : Bool)
        then
          (do
            let dword ← (( do
              (rime_size proc_mode (← (select_address_size proc_mode none)) 4
                (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" check_alignment? false) ) : SailM
              (sbits 64) )
            (pure (0x0000000000000000#64, dword, 4)))
        else
          (pure ((← do
              if ((in_64bit_mode proc_mode) : Bool)
              then (rgfi (BitVec.toNatInt (reg_index b rex_byte 0b00#2)))
              else (pure (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend b 4))) 64))), 0x0000000000000000#64, 0)))
    else
      (do
        if ((eq_bits_nat v_34 1) : Bool)
        then
          (do
            let byte ← (( do
              (rime_size proc_mode (← (select_address_size proc_mode none)) 1
                (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" check_alignment? false) ) : SailM
              (sbits 64) )
            (pure ((← do
                if ((in_64bit_mode proc_mode) : Bool)
                then (rgfi (BitVec.toNatInt (reg_index b rex_byte 0b00#2)))
                else (pure (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend b 4))) 64))), byte, 1)))
        else
          (do
            if ((eq_bits_nat v_34 2) : Bool)
            then
              (do
                let dword ← (( do
                  (rime_size proc_mode (← (select_address_size proc_mode none)) 4
                    (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" check_alignment? false) ) :
                  SailM (sbits 64) )
                (pure ((← do
                    if ((in_64bit_mode proc_mode) : Bool)
                    then (rgfi (BitVec.toNatInt (reg_index b rex_byte 0b00#2)))
                    else
                      (pure (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend b 4))) 64))), dword, 4)))
            else (x86_model_error "mod-can-not-be-anything-other-than-0-1-or-2"))) ) : SailM
    ((sbits 64) × (sbits 64) × Int) )
  let ix : (BitVec 4) := (reg_index (_get_sib_index sib) rex_byte 0b01#2)
  let index ← (( do
    let v_37 := ix
    if ((eq_bits_nat v_37 4) : Bool)
    then (pure 0x0000000000000000#64)
    else
      (do
        if ((in_64bit_mode proc_mode) : Bool)
        then (rgfi (BitVec.toNatInt ix))
        else
          (pure (Sail.BitVec.signExtend (Sail.BitVec.truncate (← (rgfi (BitVec.toNatInt ix))) 32)
              64))) ) : SailM (sbits 64) )
  let scale : (BitVec 2) := (_get_sib_scale sib)
  let scaled_index : Int := (ash_left_int (BitVec.toInt index) (BitVec.toNatInt scale))
  let effective_addr : Int := ((BitVec.toInt base) +i scaled_index)
  (pure (effective_addr, displacement, nrip_bytes))

def x86_effective_addr_16_disp (proc_mode : proc_mode) (temp_rip : (BitVec 48)) (mod_var : (BitVec 2)) : SailM ((BitVec 64) × Int) := do
  let v_38 := mod_var
  if ((eq_bits_nat v_38 0) : Bool)
  then (pure (0x0000000000000000#64, 0))
  else
    (do
      if ((eq_bits_nat v_38 1) : Bool)
      then
        (do
          let byte ← (( do
            (rime_size proc_mode (← (select_address_size proc_mode none)) 1
              (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM (sbits 64) )
          (pure (byte, 1)))
      else
        (do
          if ((eq_bits_nat v_38 2) : Bool)
          then
            (do
              let word ← (( do
                (rime_size proc_mode (← (select_address_size proc_mode none)) 2
                  (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM (sbits 64)
                )
              (pure (word, 2)))
          else (x86_model_error "mod-value-wrong")))

def x86_effective_addr_16 (proc_mode : proc_mode) (temp_rip : (BitVec 48)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) : SailM ((BitVec 16) × Int) := do
  let v_41 := r_m
  if ((eq_bits_nat v_41 0) : Bool)
  then
    (do
      let bx ← (( do (rr16 0x3#4) ) : SailM (BitVec 16) )
      let si ← (( do (rr16 0x6#4) ) : SailM (BitVec 16) )
      let (disp, increment_rip_by) ← (( do (x86_effective_addr_16_disp proc_mode temp_rip mod_var)
        ) : SailM ((sbits 64) × Int) )
      (pure ((bits_of_int ((BitVec.toNatInt bx) +i ((BitVec.toNatInt si) +i (BitVec.toInt disp))) 16), increment_rip_by)))
  else
    (do
      if ((eq_bits_nat v_41 1) : Bool)
      then
        (do
          let bx ← (( do (rr16 0x3#4) ) : SailM (BitVec 16) )
          let di ← (( do (rr16 0x7#4) ) : SailM (BitVec 16) )
          let (disp, increment_rip_by) ← (( do
            (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) : SailM ((sbits 64) × Int) )
          (pure ((bits_of_int
              ((BitVec.toNatInt bx) +i ((BitVec.toNatInt di) +i (BitVec.toInt disp))) 16), increment_rip_by)))
      else
        (do
          if ((eq_bits_nat v_41 2) : Bool)
          then
            (do
              let bp ← (( do (rr16 0x5#4) ) : SailM (BitVec 16) )
              let si ← (( do (rr16 0x6#4) ) : SailM (BitVec 16) )
              let (disp, increment_rip_by) ← (( do
                (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) : SailM
                ((sbits 64) × Int) )
              (pure ((bits_of_int
                  ((BitVec.toNatInt bp) +i ((BitVec.toNatInt si) +i (BitVec.toInt disp))) 16), increment_rip_by)))
          else
            (do
              if ((eq_bits_nat v_41 3) : Bool)
              then
                (do
                  let bp ← (( do (rr16 0x5#4) ) : SailM (BitVec 16) )
                  let di ← (( do (rr16 0x7#4) ) : SailM (BitVec 16) )
                  let (disp, increment_rip_by) ← (( do
                    (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) : SailM
                    ((sbits 64) × Int) )
                  (pure ((bits_of_int
                      ((BitVec.toNatInt bp) +i ((BitVec.toNatInt di) +i (BitVec.toInt disp))) 16), increment_rip_by)))
              else
                (do
                  if ((eq_bits_nat v_41 4) : Bool)
                  then
                    (do
                      let si ← (( do (rr16 0x6#4) ) : SailM (BitVec 16) )
                      let (disp, increment_rip_by) ← (( do
                        (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) : SailM
                        ((sbits 64) × Int) )
                      (pure ((bits_of_int ((BitVec.toNatInt si) +i (BitVec.toInt disp)) 16), increment_rip_by)))
                  else
                    (do
                      if ((eq_bits_nat v_41 5) : Bool)
                      then
                        (do
                          let di ← (( do (rr16 0x7#4) ) : SailM (BitVec 16) )
                          let (disp, increment_rip_by) ← (( do
                            (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) : SailM
                            ((sbits 64) × Int) )
                          (pure ((bits_of_int ((BitVec.toNatInt di) +i (BitVec.toInt disp)) 16), increment_rip_by)))
                      else
                        (do
                          if ((eq_bits_nat v_41 6) : Bool)
                          then
                            (do
                              let v_48 := mod_var
                              if ((eq_bits_nat v_48 0) : Bool)
                              then
                                (do
                                  let disp ← (( do
                                    (rime_size proc_mode (← (select_address_size proc_mode none))
                                      2 (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false)
                                    ) : SailM (sbits 64) )
                                  (pure ((Sail.BitVec.truncate disp 16), 2)))
                              else
                                (do
                                  let bp ← (( do (rr16 0x5#4) ) : SailM (BitVec 16) )
                                  let (disp, increment_rip_by) ← (( do
                                    (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) :
                                    SailM ((sbits 64) × Int) )
                                  (pure ((bits_of_int ((BitVec.toNatInt bp) +i (BitVec.toInt disp))
                                      16), increment_rip_by))))
                          else
                            (do
                              if ((eq_bits_nat v_41 7) : Bool)
                              then
                                (do
                                  let bx ← (( do (rr16 0x3#4) ) : SailM (BitVec 16) )
                                  let (disp, increment_rip_by) ← (( do
                                    (x86_effective_addr_16_disp proc_mode temp_rip mod_var) ) :
                                    SailM ((sbits 64) × Int) )
                                  (pure ((bits_of_int ((BitVec.toNatInt bx) +i (BitVec.toInt disp))
                                      16), increment_rip_by)))
                              else (x86_model_error ":R/M-OUT-OF-RANGE"))))))))

/-- Type quantifiers: k_ex33778_ : Bool -/
def x86_effective_addr_32_64 (proc_mode : proc_mode) (p4 : Bool) (temp_rip : (BitVec 48)) (rex_byte : (BitVec 8)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) (num_imm_bytes : (BitVec 3)) : SailM ((BitVec 64) × Int) := do
  let (addr, displacement, increment_rip_by) ← (( do
    let v_50 := mod_var
    if ((eq_bits_nat v_50 0) : Bool)
    then
      (do
        let v_51 := r_m
        if ((eq_bits_nat v_51 4) : Bool)
        then (x86_effective_addr_from_sib proc_mode temp_rip rex_byte mod_var sib)
        else
          (do
            if ((eq_bits_nat v_51 5) : Bool)
            then
              (do
                if ((in_64bit_mode proc_mode) : Bool)
                then
                  (do
                    let dword ← (( do
                      (rime_size Mode_64bit (← (select_address_size proc_mode none)) 4
                        (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM
                      (sbits 64) )
                    let next_rip ← (( do
                      (add_to_iptr Mode_64bit temp_rip
                        (bits_of_int (4 +i (BitVec.toNatInt num_imm_bytes)) 48)) ) : SailM
                      (sbits 48) )
                    (pure ((BitVec.toInt next_rip), dword, 4)))
                else
                  (do
                    let dword ← (( do
                      (rime_size proc_mode (← (select_address_size proc_mode none)) 4
                        (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM
                      (sbits 64) )
                    (pure ((BitVec.toInt 0x000000000000#48), dword, 4))))
            else
              (pure ((← do
                  if ((in_64bit_mode proc_mode) : Bool)
                  then
                    (pure (BitVec.toInt
                        (← (rgfi (BitVec.toNatInt (reg_index r_m rex_byte 0b00#2))))))
                  else
                    (pure (BitVec.toInt
                        (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend r_m 4))) 64)))), 0x0000000000000000#64, 0))))
    else
      (do
        if ((eq_bits_nat v_50 1) : Bool)
        then
          (do
            let v_54 := r_m
            if ((eq_bits_nat v_54 4) : Bool)
            then (x86_effective_addr_from_sib proc_mode temp_rip rex_byte mod_var sib)
            else
              (do
                let byte2 ← (( do
                  (rime_size proc_mode (← (select_address_size proc_mode none)) 1
                    (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM
                  (sbits 64) )
                let reg ← (( do
                  if ((in_64bit_mode proc_mode) : Bool)
                  then (rgfi (BitVec.toNatInt (reg_index r_m rex_byte 0b00#2)))
                  else
                    (pure (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend r_m 4))) 64)) )
                  : SailM (sbits 64) )
                (pure ((BitVec.toInt reg), byte2, 1))))
        else
          (do
            if ((eq_bits_nat v_50 2) : Bool)
            then
              (do
                let v_56 := r_m
                if ((eq_bits_nat v_56 4) : Bool)
                then (x86_effective_addr_from_sib proc_mode temp_rip rex_byte mod_var sib)
                else
                  (do
                    let dword ← (( do
                      (rime_size proc_mode (← (select_address_size proc_mode none)) 4
                        (Sail.BitVec.signExtend temp_rip 64) none 1 ":X" false false) ) : SailM
                      (sbits 64) )
                    let reg ← (( do
                      if ((in_64bit_mode proc_mode) : Bool)
                      then (rgfi (BitVec.toNatInt (reg_index r_m rex_byte 0b00#2)))
                      else
                        (pure (Sail.BitVec.zeroExtend (← (rr32 (Sail.BitVec.zeroExtend r_m 4))) 64))
                      ) : SailM (sbits 64) )
                    (pure ((BitVec.toInt reg), dword, 4))))
            else (x86_model_error "mod-value-wrong"))) ) : SailM (Int × (sbits 64) × Int) )
  let dst_base : Int := (addr +i (BitVec.toInt displacement))
  let dst_base : (sbits 64) :=
    if ((in_64bit_mode proc_mode) : Bool)
    then
      (if (p4 : Bool)
      then (Sail.BitVec.zeroExtend (bits_of_int dst_base 32) 64)
      else (bits_of_int dst_base 64))
    else (Sail.BitVec.zeroExtend (bits_of_int dst_base 32) 64)
  (pure (dst_base, increment_rip_by))

def x86_effective_addr (proc_mode : proc_mode) (prefixes : (BitVec 52)) (temp_rip : (BitVec 48)) (rex_byte : (BitVec 8)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) (num_imm_bytes : (BitVec 3)) : SailM ((BitVec 64) × Int) := do
  let p4 := (0x67#8 == (_get_prefixes_adr prefixes))
  if ((2 == (← (select_address_size proc_mode (some prefixes)))) : Bool)
  then
    (do
      let (elem1, elem2) ← (( do (x86_effective_addr_16 proc_mode temp_rip r_m mod_var) ) : SailM
        ((BitVec 16) × Int) )
      (pure ((Sail.BitVec.zeroExtend elem1 64), elem2)))
  else (x86_effective_addr_32_64 proc_mode p4 temp_rip rex_byte r_m mod_var sib num_imm_bytes)

def alignment_checking_enabled_p (_ : Unit) : SailM Bool := do
  let cr0 ← (( do (pure (Sail.BitVec.truncate (GetElem?.getElem! (← readReg ctrs) 0) 32)) ) :
    SailM (BitVec 32) )
  let am : (BitVec 1) := (_get_cr0bits_am (Mk_cr0bits cr0))
  let ac ← (( do
    let rflags_var ← (( do readReg rflags ) : SailM rflagsbits )
    (pure (Sail.BitVec.zeroExtend (_get_rflagsbits_ac rflags_var) 2)) ) : SailM (BitVec 2) )
  let cpl ← (( do
    (pure (_get_segment_selectorbits_rpl
        (Mk_segment_selectorbits (GetElem?.getElem! (← readReg seg_visibles) 1)))) ) : SailM
    (BitVec 2) )
  (pure ((am == 1#1) && ((ac == 0b01#2) && (cpl == 0b11#2))))

/-- Type quantifiers: seg_reg : Nat, k_ex33781_ : Bool, k_ex33780_ : Bool, operand_size : Nat, operand_size
  ∈ {1, 2, 4, 6, 8, 10, 16}, 0 ≤ seg_reg ∧ seg_reg ≤ 5 -/
def x86_operand_to_reg_mem (proc_mode : proc_mode) (operand_size : Nat) (inst_ac? : Bool) (memory_ptr? : Bool) (operand : (BitVec 128)) (seg_reg : Nat) (addr : (BitVec 64)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (r_m : (BitVec 3)) (mod_var : (BitVec 2)) (sib : (BitVec 8)) : SailM Unit := do
  if ((mod_var == 0b11#2) : Bool)
  then
    (write_rgfi_size (bits_of_int operand_size 4) (reg_index r_m rex_byte 0b00#2)
      (Sail.BitVec.truncate operand 64) rex_byte)
  else
    (do
      let check_alignment? ← (( do (pure (inst_ac? && (← (alignment_checking_enabled_p ())))) )
        : SailM Bool )
      let addr_size ← do (select_address_size proc_mode (some prefixes))
      let base_reg : (Option base_reg_idx) :=
        (select_base_register proc_mode rex_byte r_m mod_var sib)
      (wme_size proc_mode addr_size operand_size addr base_reg seg_reg operand check_alignment?
        memory_ptr?))

/-- Type quantifiers: k_ex33787_ : Bool, k_ex33786_ : Bool, k_ex33785_ : Bool, k_ex33784_ : Bool, k_ex33783_
  : Bool -/
def select_operand_size (proc_mode : proc_mode) (byte_operand? : Bool) (rex_byte : (BitVec 8)) (imm? : Bool) (prefixes : (BitVec 52)) (default64? : Bool) (ignore_rex? : Bool) (ignore_p3_64? : Bool) : SailM Int := do
  if (byte_operand? : Bool)
  then (pure 1)
  else
    (do
      if ((in_64bit_mode proc_mode) : Bool)
      then
        (if (((logbitp_bits 3 rex_byte) && (! ignore_rex?)) : Bool)
        then
          (if (imm? : Bool)
          then (pure 4)
          else (pure 8))
        else
          (if (((0x66#8 == (_get_prefixes_opr prefixes)) && (! ignore_p3_64?)) : Bool)
          then (pure 2)
          else
            (if (default64? : Bool)
            then (pure 8)
            else (pure 4))))
      else
        (do
          let cs_attr ← (( do (pure (GetElem?.getElem! (← readReg seg_hidden_attrs) 1)) ) :
            SailM (BitVec 16) )
          let cs_d : (BitVec 1) :=
            (_get_code_segment_descriptor_attributesbits_d
              (Mk_code_segment_descriptor_attributesbits cs_attr))
          let p3? : Bool := (0x66#8 == (_get_prefixes_opr prefixes))
          if ((cs_d == 1#1) : Bool)
          then
            (if (p3? : Bool)
            then (pure 2)
            else (pure 4))
          else
            (if (p3? : Bool)
            then (pure 4)
            else (pure 2))))

def check_instruction_length (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (delta_rip : (BitVec 3)) : (Option Int) :=
  let start_rip : Int := (BitVec.toInt start_rip)
  let temp_rip : Int := (BitVec.toInt temp_rip)
  let delta_rip : Nat := (BitVec.toNatInt delta_rip)
  let end_rip : (sbits 49) :=
    (bits_of_int
      ((BitVec.toInt (bits_of_int temp_rip 48)) +i (BitVec.toNatInt (bits_of_int delta_rip 3))) 49)
  let length : (sbits 50) :=
    (bits_of_int ((BitVec.toInt end_rip) -i (BitVec.toInt (bits_of_int start_rip 48))) 50)
  if ((15 <b (BitVec.toInt length)) : Bool)
  then (some (BitVec.toInt length))
  else none

def x86_mov_op_en_mr (proc_mode : proc_mode) (start_rip : (BitVec 48)) (temp_rip : (BitVec 48)) (prefixes : (BitVec 52)) (rex_byte : (BitVec 8)) (opcode : (BitVec 8)) (modr_m : (BitVec 8)) (sib : (BitVec 8)) : SailM Unit := do
  let ctx : String := "X86-MOV-OP/EN-MR"
  let r_m : (BitVec 3) := (_get_modr_m_r_m modr_m)
  let mod_var : (BitVec 2) := (_get_modr_m_mod modr_m)
  let reg : (BitVec 3) := (_get_modr_m_reg modr_m)
  let p2 : (BitVec 8) := (_get_prefixes_seg prefixes)
  let p4? : Bool := (0x67#8 == (_get_prefixes_adr prefixes))
  let byte_operand? : Bool := (opcode == 0x88#8)
  let operand_size ← (( do
    (select_operand_size proc_mode byte_operand? rex_byte false prefixes false false false) ) :
    SailM Int )
  let register_var ← (( do
    (rgfi_size (bits_of_int operand_size 4) (reg_index reg rex_byte 0b10#2) rex_byte) ) : SailM
    (BitVec 64) )
  let (addr, increment_rip_by) ← (( do
    if ((mod_var == 0b11#2) : Bool)
    then (pure (0x0000000000000000#64, 0))
    else (x86_effective_addr proc_mode prefixes temp_rip rex_byte r_m mod_var sib 0b000#3) ) : SailM
    ((sbits 64) × Int) )
  let increment_rip_by : (BitVec 3) := (bits_of_int increment_rip_by 3)
  let seg_reg ← (( do (select_segment_register proc_mode prefixes mod_var r_m sib) ) : SailM
    seg_reg_idx )
  let temp_rip ← (( do
    (add_to_iptr proc_mode temp_rip (Sail.BitVec.zeroExtend increment_rip_by 48)) ) : SailM
    (sbits 48) )
  let badlength? : (Option Int) := (check_instruction_length start_rip temp_rip 0b000#3)
  if ((is_some badlength?) : Bool)
  then (x86_fault "(!!FAULT-FRESH :GP 0 :INSTRUCTION-LENGTH BADLENGTH?)")
  else (pure ())
  let inst_ac? : Bool := true
  (x86_operand_to_reg_mem proc_mode operand_size inst_ac? false
    (Sail.BitVec.zeroExtend register_var 128) seg_reg addr prefixes rex_byte r_m mod_var sib)
  (write_iptr proc_mode temp_rip)

end X86Registers.Functions
