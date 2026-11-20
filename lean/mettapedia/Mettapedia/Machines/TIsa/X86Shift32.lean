import Mettapedia.Machines.TIsa.X86Shift
import Mettapedia.Machines.TIsa.X86DataStore

/-!
# Original dword shift results and register forms

The three original 32-bit primitives compute Shift.evaluate. Register
instruction contracts retain the hardware count mask and zero extension.
The effective REX byte is zero for low registers, matching omitted prefixes.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Shift32
open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1
local instance : MemoryPrimitives := X86Memory.ordinary

theorem left_bits (value : BitVec 32) (count : BitVec 6) :
    Functions.bits_of_int (Functions.ash_left_int (Sail.BitVec.toNatInt value)
      (Sail.BitVec.toNatInt count)) 32 = value <<< count.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [X86Alu.bits_of_int_eq,Functions.ash_left_int,Sail.BitVec.toNatInt,
    BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((value.toNat : Int) * (2 : Int) ^ count.toNat % (2 ^ 32 : Nat)).toNat = _
  norm_cast

theorem negative_count : ∀ count : BitVec 6,
    (Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 33).toInt = -(count.toNat : Int) := by decide

theorem right_bits (value : BitVec 32) (count : BitVec 6) :
    Functions.bits_of_int
      (Functions.ash_int (Sail.BitVec.toNatInt value)
        (Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 33).toInt) 32 =
      value >>> count.toNat := by
  rw [negative_count,X86Shift.negative_shift,X86Alu.bits_of_int_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Sail.BitVec.toNatInt]
  norm_cast
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt)

theorem parity_executes (state : State) (value : BitVec 32) :
    ∃ result, (Functions.pf_spec32 value).run state = .ok result state := by
  unfold Functions.pf_spec32 Functions.logbitp_int
  simp only [run_bind,run_assert,show ((0 : Int) ≥b 0) = true from rfl,ite_true]
  exact ⟨_,rfl⟩

theorem slice_executes (state : State) (value : BitVec 32) (low : Fin 32) :
    (Functions.bitslice value (low.val : Int) 1).run state =
      .ok (Sail.BitVec.extractLsb value low.val low.val) state := by
  fin_cases low <;> rfl

theorem left_value (state : State) (value : BitVec 32) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.sal_shl_spec_32 value count flags).run state =
      .ok (value <<< count.toNat,output,mask) state := by
  unfold Functions.sal_shl_spec_32
  dsimp only
  rw [left_bits]
  by_cases zero : Functions.eq_bits_nat count 0 = true
  · simp only [zero,ite_true,pure_bind,run_pure]
    exact ⟨_,_,rfl⟩
  · simp only [zero,Bool.false_eq_true,ite_false]
    by_cases one : Functions.eq_bits_nat count 1 = true
    · simp only [one,ite_true]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value <<< count.toNat)
      simp only [run_bind,parityRun]
      obtain ⟨bit,bitRun⟩ := X86Shift.xor_bit_executes state (Sail.BitVec.extractLsb value 31 31)
        (Functions.logbit_bits 31 (value <<< count.toNat))
      simp only [bitRun]
      exact ⟨_,_,rfl⟩
    · simp only [one,Bool.false_eq_true,ite_false]
      by_cases large : ((32 : Int) ≤b Sail.BitVec.toNatInt count) = true
      · simp only [large,ite_true]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value <<< count.toNat)
        simp only [run_bind,parityRun]
        exact ⟨_,_,rfl⟩
      · simp only [large,Bool.false_eq_true,ite_false]
        have positive : 0 < count.toNat := by
          simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,beq_iff_eq] at zero
          omega
        have small : count.toNat < 32 := by
          change ¬decide (32 ≤ (count.toNat : Int)) = true at large
          simp only [decide_eq_true_eq] at large
          omega
        have low : 32 - (count.toNat : Int) = ((32 - count.toNat : Nat) : Int) := by omega
        rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
        simp only [run_bind,slice_executes state value ⟨32 - count.toNat,by omega⟩]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value <<< count.toNat)
        simp only [parityRun]
        exact ⟨_,_,rfl⟩

def raw (value : BitVec 32) (count : BitVec 6) : SailM Int := do
  let negative := Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 33
  let unsigned := Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt value) negative.toInt) 32
  if (Functions.logbit_bits 31 value == (1#1)) then
    pure (Functions.loghead_int 32
      (Functions.ash_int (← Functions.binary_logext 32 (Sail.BitVec.toNatInt value)) negative.toInt))
  else pure (Sail.BitVec.toNatInt unsigned)

theorem raw_executes (state : State) (value : BitVec 32) (count : BitVec 6) :
    (raw value count).run state = .ok (Sail.BitVec.toNatInt (value.sshiftRight count.toNat)) state := by
  unfold raw
  dsimp only
  have signBit : Functions.logbit_bits (31 : Int) value = BitVec.ofBool value.msb := X86Shift.bit_msb 31 value
  rw [signBit]
  have choose : ∀ bit : Bool, (BitVec.ofBool bit == (1#1)) = bit := by decide
  rw [choose]
  cases sign : value.msb with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    rw [right_bits,BitVec.sshiftRight_eq_of_msb_false sign]
    rfl
  | true =>
    simp only [ite_true]
    have extend : (Functions.binary_logext 32 (Sail.BitVec.toNatInt value)).run state =
        .ok value.toInt state := X86SignExtension.logext state 31 value
    rw [run_bind,extend]
    simp only [run_pure,negative_count,X86Shift.negative_shift]
    have head : Functions.loghead_int 32 (value.toInt / (2 ^ count.toNat : Int)) =
        ((BitVec.ofInt 32 (value.toInt / (2 ^ count.toNat : Int))).toNat : Int) :=
      X86SignExtension.loghead 32 _
    rw [head,BitVec.sshiftRight_eq,Int.shiftRight_eq_div_pow]
    rfl

theorem right_value (state : State) (value : BitVec 32) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.shr_spec_32 value count flags).run state =
      .ok (value >>> count.toNat,output,mask) state := by
  unfold Functions.shr_spec_32
  dsimp only
  rw [right_bits]
  by_cases zero : Functions.eq_bits_nat count 0 = true
  · simp only [zero,ite_true,pure_bind,run_pure]
    exact ⟨_,_,rfl⟩
  · simp only [zero,Bool.false_eq_true,ite_false]
    by_cases one : Functions.eq_bits_nat count 1 = true
    · simp only [one,ite_true]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value >>> count.toNat)
      simp only [run_bind,parityRun]
      exact ⟨_,_,rfl⟩
    · simp only [one,Bool.false_eq_true,ite_false]
      by_cases large : ((32 : Int) ≤b Sail.BitVec.toNatInt count) = true
      · simp only [large,ite_true]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value >>> count.toNat)
        simp only [run_bind,parityRun]
        exact ⟨_,_,rfl⟩
      · simp only [large,Bool.false_eq_true,ite_false]
        have small : count.toNat < 32 := by
          change ¬decide (32 ≤ (count.toNat : Int)) = true at large
          simp only [decide_eq_true_eq] at large
          omega
        have positive : 0 < count.toNat := by
          simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,beq_iff_eq] at zero
          omega
        have low : (count.toNat : Int) - 1 = ((count.toNat - 1 : Nat) : Int) := by omega
        rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
        simp only [run_bind,slice_executes state value ⟨count.toNat - 1,by omega⟩]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value >>> count.toNat)
        simp only [parityRun]
        exact ⟨_,_,rfl⟩


theorem signed_value (state : State) (value : BitVec 32) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.sar_spec_32 value count flags).run state =
      .ok (value.sshiftRight count.toNat,output,mask) state := by
  unfold Functions.sar_spec_32
  dsimp only
  have computed := raw_executes state value count
  unfold raw at computed
  dsimp only at computed
  rw [run_bind,computed]
  dsimp only
  have recoded : Functions.bits_of_int (Sail.BitVec.toNatInt (value.sshiftRight count.toNat)) 32 =
      value.sshiftRight count.toNat := by
    rw [X86Alu.bits_of_int_eq]
    simp only [Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,BitVec.ofInt_natCast,
      BitVec.ofNat_toNat,BitVec.setWidth_eq]
  simp only [recoded]
  by_cases zero : Functions.eq_bits_nat count 0 = true
  · simp only [zero,ite_true,pure_bind,run_pure]
    exact ⟨_,_,rfl⟩
  · simp only [zero,Bool.false_eq_true,ite_false]
    by_cases one : Functions.eq_bits_nat count 1 = true
    · simp only [one,ite_true]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value.sshiftRight count.toNat)
      simp only [run_bind,parityRun]
      exact ⟨_,_,rfl⟩
    · simp only [one,Bool.false_eq_true,ite_false]
      by_cases large : ((32 : Int) ≤b Sail.BitVec.toNatInt count) = true
      · simp only [large,ite_true]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value.sshiftRight count.toNat)
        simp only [run_bind,parityRun]
        exact ⟨_,_,rfl⟩
      · simp only [large,Bool.false_eq_true,ite_false]
        have small : count.toNat < 32 := by
          change ¬decide (32 ≤ (count.toNat : Int)) = true at large
          simp only [decide_eq_true_eq] at large
          omega
        have positive : 0 < count.toNat := by
          simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,beq_iff_eq] at zero
          omega
        have low : (count.toNat : Int) - 1 = ((count.toNat - 1 : Nat) : Int) := by omega
        rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
        simp only [run_bind,slice_executes state value ⟨count.toNat - 1,by omega⟩]
        obtain ⟨parity,parityRun⟩ := parity_executes state (value.sshiftRight count.toNat)
        simp only [parityRun]
        exact ⟨_,_,rfl⟩


def rex32 (destination : Fin 16) : BitVec 8 :=
  if destination.val < 8 then (0#8) else X86RegisterEncoding.rex false 0 destination

theorem rex_w_zero : ∀ destination : Fin 16, Functions.logbitp_bits 3 (rex32 destination) = false := by decide

theorem decoded_destination : ∀ operation : Shift, ∀ destination : Fin 16,
    Functions.reg_index
      (Functions._get_modr_m_r_m (X86RegisterEncoding.modRM (X86Shift.extension operation) destination))
      (rex32 destination) (0#2) = BitVec.ofNat 4 destination.val := by
  intro operation
  cases operation <;> decide

theorem operand_size (destination : Fin 16) (prefixes : BitVec 52)
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8)) :
    Functions.select_operand_size .Mode_64bit false (rex32 destination) false prefixes
      false false false = (pure 4 : SailM Int) := by
  simp [Functions.select_operand_size,Functions.in_64bit_mode,rex_w_zero,operandOverride]

theorem operand_register (operation : Shift) (state : State) (destination : Fin 16) (value : Word)
    (prefixes : BitVec 52) (pointer : BitVec 48) (immediate : BitVec 3)
    (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 4 true false 3
      prefixes pointer (rex32 destination)
      (Functions._get_modr_m_r_m (X86RegisterEncoding.modRM (X86Shift.extension operation) destination))
      (3#2) (0#8) immediate).run state =
        .ok ((low32 value).zeroExtend 128,(0 : Int),(0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl,ite_true,pure_bind]
  rw [show Functions.bits_of_int ((4 : Nat) : Int) 4 = (4#4) from rfl,decoded_destination]
  rw [run_bind,run_bind,X86DataStore.read_register32 state destination value (rex32 destination) known]
  simp only [X86DataStore.widen32]
  rfl

theorem write_action (operation : Shift) (destination : Fin 16) (value : BitVec 32)
    (prefixes : BitVec 52) :
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3 (0#64) prefixes
      (rex32 destination)
      (Functions._get_modr_m_r_m (X86RegisterEncoding.modRM (X86Shift.extension operation) destination))
      (3#2) (0#8) = Functions.wr32 (BitVec.ofNat 4 destination.val) value := by
  have cut : Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32 = value := by
    change ((value.setWidth 128).setWidth 64).setWidth 32 = value
    rw [BitVec.setWidth_setWidth (by decide),BitVec.setWidth_setWidth (by decide),BitVec.setWidth_eq]
  change Functions.wr32
    (Functions.reg_index
      (Functions._get_modr_m_r_m (X86RegisterEncoding.modRM (X86Shift.extension operation) destination))
      (rex32 destination) (0#2))
    (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32) = _
  rw [cut,decoded_destination]

theorem write_operand (operation : Shift) (state : State) (destination : Fin 16) (value : BitVec 32)
    (prefixes : BitVec 52) (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false (value.zeroExtend 128) 3 (0#64) prefixes
      (rex32 destination)
      (Functions._get_modr_m_r_m (X86RegisterEncoding.modRM (X86Shift.extension operation) destination))
      (3#2) (0#8)).run state = .ok () (put state destination (value.zeroExtend 64)) := by
  rw [write_action]
  exact wr32_exact state destination value quiet

def specification : Shift → BitVec 32 → BitVec 6 → BitVec 32 → SailM (Word × BitVec 32 × BitVec 32)
  | .left,value,count,flags => Functions.sal_shl_spec 4 (value.zeroExtend 64) count flags
  | .rightUnsigned,value,count,flags => Functions.shr_spec 4 (value.zeroExtend 64) count flags
  | .rightSigned,value,count,flags => Functions.sar_spec 4 (value.zeroExtend 64) count flags

theorem spec_executes (operation : Shift) (state : State) (value : BitVec 32) (count : BitVec 6)
    (flags : BitVec 32) :
    ∃ output mask, (specification operation value count flags).run state =
      .ok ((operation.evaluate value count.toNat).zeroExtend 64,output,mask) state := by
  have cut : Sail.BitVec.truncate (value.zeroExtend 64) 32 = value := by
    apply BitVec.eq_of_getLsbD_eq
    intro index within
    simp [Sail.BitVec.truncate,within]
  cases operation with
  | left =>
    obtain ⟨output,mask,run⟩ := left_value state value count flags
    refine ⟨output,mask,?_⟩
    change (do
      let result ← Functions.sal_shl_spec_32 (Sail.BitVec.truncate (value.zeroExtend 64) 32) count flags
      pure (Sail.BitVec.zeroExtend result.1 64,result.2.1,result.2.2)).run state = _
    rw [cut,run_bind,run]
    rfl
  | rightUnsigned =>
    obtain ⟨output,mask,run⟩ := right_value state value count flags
    refine ⟨output,mask,?_⟩
    change (do
      let result ← Functions.shr_spec_32 (Sail.BitVec.truncate (value.zeroExtend 64) 32) count flags
      pure (Sail.BitVec.zeroExtend result.1 64,result.2.1,result.2.2)).run state = _
    rw [cut,run_bind,run]
    rfl
  | rightSigned =>
    obtain ⟨output,mask,run⟩ := signed_value state value count flags
    refine ⟨output,mask,?_⟩
    change (do
      let result ← Functions.sar_spec_32 (Sail.BitVec.truncate (value.zeroExtend 64) 32) count flags
      pure (Sail.BitVec.zeroExtend result.1 64,result.2.1,result.2.2)).run state = _
    rw [cut,run_bind,run]
    rfl

#print axioms write_action
#print axioms operand_register
#print axioms write_operand
#print axioms spec_executes
#print axioms left_bits
#print axioms right_bits
#print axioms left_value
#print axioms right_value
#print axioms signed_value
end Mettapedia.Machines.TIsa.X86Shift32
