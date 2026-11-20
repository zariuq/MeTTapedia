import Mettapedia.Machines.TIsa.X86SubByteImmediate
import Mettapedia.Machines.TIsa.X86MaskedFlags
import Mettapedia.Machines.TIsa.X86SignExtension
import Mettapedia.Machines.TIsa.P1Scalar

/-!
# Original fetched 64-bit immediate SHL, SHR and SAR

The retained Sail dependency closure contains the full shift/rotate handler.
This module proves its C1 /4, /5 and /7 register cases through the original fetch
and dispatch, including immediate reads, masked counts, flags and frames.
Narrow widths and complete source-template joins remain separate.
-/

set_option autoImplicit false

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/ShiftFunctions.lean.inc"
  sha256 "24c26d340b825c300ff27b0c5e2b312af985cc033a07587ae194c28ee896b24d"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86Shift
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open Sail.ConcurrencyInterfaceV1 X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary

elab "tisa_shift_strict " inner:tactic : tactic =>
  Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
    Lean.Elab.Tactic.evalTactic inner

theorem left_bits (value : Word) (count : BitVec 6) :
    Functions.bits_of_int (Functions.ash_left_int (Sail.BitVec.toNatInt value)
      (Sail.BitVec.toNatInt count)) 64 = value <<< count.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [X86Alu.bits_of_int_eq,Functions.ash_left_int,Sail.BitVec.toNatInt,
    BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  change ((value.toNat : Int) * (2 : Int) ^ count.toNat % (2 ^ 64 : Nat)).toNat = _
  norm_cast

theorem xor_bit_executes (state : State) (left right : BitVec 1) :
    ∃ result, (Functions.b_xor (Sail.BitVec.toNatInt left) (Sail.BitVec.toNatInt right)).run state =
      .ok result state := by
  have valid : ∀ left right : BitVec 1, ((0 ≤b Sail.BitVec.toNatInt left) &&
      ((Sail.BitVec.toNatInt left ≤b 1) && ((0 ≤b Sail.BitVec.toNatInt right) &&
        (Sail.BitVec.toNatInt right ≤b 1)))) = true := by decide
  unfold Functions.b_xor
  rw [valid left right]
  simp only [run_bind,run_assert,ite_true]
  by_cases l : Sail.BitVec.toNatInt left == 0 <;>
    by_cases r : Sail.BitVec.toNatInt right == 0 <;>
    simp only [l,r,Bool.false_eq_true,ite_false,ite_true,run_pure] <;> exact ⟨_,rfl⟩

theorem parity_executes (state : State) (value : Word) :
    ∃ result, (Functions.pf_spec64 value).run state = .ok result state := by
  unfold Functions.pf_spec64 Functions.logbitp_int
  simp only [run_bind,run_assert,show ((0 : Int) ≥b 0) = true from rfl,ite_true]
  exact ⟨_,rfl⟩

theorem slice_executes (state : State) (value : Word) (low : Fin 64) :
    (Functions.bitslice value (low.val : Int) 1).run state =
      .ok (Sail.BitVec.extractLsb value low.val low.val) state := by
  fin_cases low <;> rfl

theorem left_value (state : State) (value : Word) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.sal_shl_spec_64 value count flags).run state =
      .ok (value <<< count.toNat,output,mask) state := by
  unfold Functions.sal_shl_spec_64
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
      obtain ⟨bit,bitRun⟩ := xor_bit_executes state (Sail.BitVec.extractLsb value 63 63)
        (Functions.logbit_bits 63 (value <<< count.toNat))
      simp only [bitRun]
      exact ⟨_,_,rfl⟩
    · simp only [one,Bool.false_eq_true,ite_false]
      have small : ((64 : Int) ≤b Sail.BitVec.toNatInt count) = false := by
        have bound := count.isLt
        simp only [Sail.BitVec.toNatInt,Int.ofNat_eq_natCast]
        exact decide_eq_false (by omega)
      simp only [small,Bool.false_eq_true,ite_false]
      have positive : 0 < count.toNat := by
        simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,
          beq_iff_eq] at zero
        omega
      have low : 64 - (count.toNat : Int) = ((64 - count.toNat : Nat) : Int) := by
        have bound := count.isLt
        omega
      rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
      simp only [run_bind,slice_executes state value ⟨64 - count.toNat,by omega⟩]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value <<< count.toNat)
      simp only [parityRun]
      exact ⟨_,_,rfl⟩

theorem divide_iterate (value : Int) (count : Nat) :
    Sail.Nat.iterate (fun x : Int => x / 2) count value = value / (2 ^ count : Int) := by
  induction count generalizing value with
  | zero => simp [Sail.Nat.iterate]
  | succ count ih =>
    rw [Sail.Nat.iterate,ih,Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 2)]
    simp [Int.pow_succ,Int.mul_comm]

theorem negative_shift (value : Int) (count : Nat) :
    Functions.ash_int value (-(count : Int)) = value / (2 ^ count : Int) := by
  cases count with
  | zero => simp [Functions.ash_int]
  | succ count =>
    change Sail.Nat.iterate (fun x : Int => x / 2) (count + 1) value = _
    exact divide_iterate value (count + 1)

theorem negative_count : ∀ count : BitVec 6,
    (Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 65).toInt = -(count.toNat : Int) := by decide

theorem right_bits (value : Word) (count : BitVec 6) :
    Functions.bits_of_int
      (Functions.ash_int (Sail.BitVec.toNatInt value)
        (Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 65).toInt) 64 =
      value >>> count.toNat := by
  rw [negative_count,negative_shift,X86Alu.bits_of_int_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Sail.BitVec.toNatInt]
  norm_cast
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt)

theorem right_value (state : State) (value : Word) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.shr_spec_64 value count flags).run state =
      .ok (value >>> count.toNat,output,mask) state := by
  unfold Functions.shr_spec_64
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
      have small : ∀ count : BitVec 6, ((64 : Int) ≤b Sail.BitVec.toNatInt count) = false := by decide
      simp only [small,Bool.false_eq_true,ite_false]
      have positive : 0 < count.toNat := by
        simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,beq_iff_eq] at zero
        omega
      have low : (count.toNat : Int) - 1 = ((count.toNat - 1 : Nat) : Int) := by omega
      rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
      simp only [run_bind,slice_executes state value ⟨count.toNat - 1,by have := count.isLt; omega⟩]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value >>> count.toNat)
      simp only [parityRun]
      exact ⟨_,_,rfl⟩

theorem count_mask64 : ∀ count : BitVec 8,
    Sail.BitVec.truncate ((Functions.bits_of_int 63 128) &&& count.zeroExtend 128) 6 =
      count.setWidth 6 := by decide

theorem count_mask32 : ∀ count : BitVec 8,
    Sail.BitVec.truncate ((Functions.bits_of_int 31 128) &&& count.zeroExtend 128) 6 =
      (count &&& 31).setWidth 6 := by decide

theorem bit_msb (width : Nat) (value : BitVec (width + 1)) :
    Functions.logbit_bits (width : Int) value = BitVec.ofBool value.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have zero : index = 0 := by omega
  subst index
  simp [Functions.logbit_bits,Sail.BitVec.length,Sail.BitVec.join1,Sail.BitVec.access,
    BitVec.msb_eq_getLsbD_last,List.map]
  have singleton (bit : Bool) : BitVec.ofBoolListBE [bit] = BitVec.ofBool bit := by cases bit <;> rfl
  rw [singleton]
  simp

theorem normalized (width : Nat) (value : Int) :
    Functions.bits_of_int (Functions.loghead_int (width : Int) value) width = BitVec.ofInt width value := by
  rw [X86SignExtension.loghead,X86Alu.bits_of_int_eq,BitVec.ofInt_natCast]
  simpa only [BitVec.setWidth_eq] using BitVec.ofNat_toNat width (BitVec.ofInt width value)

def raw (value : Word) (count : BitVec 6) : SailM Int := do
  let negative := Functions.bits_of_int (-(Sail.BitVec.toNatInt count)) 65
  let unsigned := Functions.bits_of_int (Functions.ash_int (Sail.BitVec.toNatInt value) negative.toInt) 64
  if (Functions.logbit_bits 63 value == (1#1)) then
    pure (Functions.loghead_int 64
      (Functions.ash_int (← Functions.binary_logext 64 (Sail.BitVec.toNatInt value)) negative.toInt))
  else pure (Sail.BitVec.toNatInt unsigned)

theorem raw_executes (state : State) (value : Word) (count : BitVec 6) :
    (raw value count).run state = .ok (Sail.BitVec.toNatInt (value.sshiftRight count.toNat)) state := by
  unfold raw
  dsimp only
  have signBit : Functions.logbit_bits (63 : Int) value = BitVec.ofBool value.msb := bit_msb 63 value
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
    have extend : (Functions.binary_logext 64 (Sail.BitVec.toNatInt value)).run state =
        .ok value.toInt state := X86SignExtension.logext state 63 value
    rw [run_bind,extend]
    simp only [run_pure,negative_count,negative_shift]
    have head : Functions.loghead_int 64 (value.toInt / (2 ^ count.toNat : Int)) =
        ((BitVec.ofInt 64 (value.toInt / (2 ^ count.toNat : Int))).toNat : Int) :=
      X86SignExtension.loghead 64 _
    rw [head,BitVec.sshiftRight_eq,Int.shiftRight_eq_div_pow]
    rfl

theorem signed_value (state : State) (value : Word) (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (Functions.sar_spec_64 value count flags).run state =
      .ok (value.sshiftRight count.toNat,output,mask) state := by
  unfold Functions.sar_spec_64
  dsimp only
  have computed := raw_executes state value count
  unfold raw at computed
  dsimp only at computed
  rw [run_bind,computed]
  dsimp only
  have recoded : Functions.bits_of_int (Sail.BitVec.toNatInt (value.sshiftRight count.toNat)) 64 =
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
      have small : ∀ count : BitVec 6, ((64 : Int) ≤b Sail.BitVec.toNatInt count) = false := by decide
      simp only [small,Bool.false_eq_true,ite_false]
      have positive : 0 < count.toNat := by
        simp only [Functions.eq_bits_nat,Sail.BitVec.toNatInt,Int.ofNat_eq_natCast,beq_iff_eq] at zero
        omega
      have low : (count.toNat : Int) - 1 = ((count.toNat - 1 : Nat) : Int) := by omega
      rw [show Sail.BitVec.toNatInt count = (count.toNat : Int) from rfl,low]
      simp only [run_bind,slice_executes state value ⟨count.toNat - 1,by have := count.isLt; omega⟩]
      obtain ⟨parity,parityRun⟩ := parity_executes state (value.sshiftRight count.toNat)
      simp only [parityRun]
      exact ⟨_,_,rfl⟩

def extension : Shift → Fin 16
  | .left => 4 | .rightUnsigned => 5 | .rightSigned => 7

def evaluate : Shift → Word → BitVec 6 → Word
  | .left,value,count => value <<< count.toNat
  | .rightUnsigned,value,count => value >>> count.toNat
  | .rightSigned,value,count => value.sshiftRight count.toNat

def specification : Shift → Word → BitVec 6 → BitVec 32 → SailM (Word × BitVec 32 × BitVec 32)
  | .left => Functions.sal_shl_spec 8
  | .rightUnsigned => Functions.shr_spec 8
  | .rightSigned => Functions.sar_spec 8

theorem spec_executes (operation : Shift) (state : State) (value : Word)
    (count : BitVec 6) (flags : BitVec 32) :
    ∃ output mask, (specification operation value count flags).run state =
      .ok (evaluate operation value count,output,mask) state := by
  cases operation with
  | left => exact left_value state value count flags
  | rightUnsigned => exact right_value state value count flags
  | rightSigned => exact signed_value state value count flags

theorem operand_register (state : State) (source destination : Fin 16) (value : Word)
    (prefixes : BitVec 52) (pointer : BitVec 48) (immediate : BitVec 3)
    (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer (rex true source destination)
      (Functions._get_modr_m_r_m (modRM source destination)) (3#2) (0#8) immediate).run state =
        .ok (value.zeroExtend 128,(0 : Int),(0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl,ite_true,pure_bind]
  rw [show Functions.bits_of_int ((8 : Nat) : Int) 4 = (8#4) from rfl,destination_register]
  rw [run_bind,run_bind,X86Move.read_register64 state destination _ value known]
  rfl

theorem rex_w : ∀ operation : Shift, ∀ destination : Fin 16,
    Functions.logbitp_bits 3 (rex true (extension operation) destination) = true := by
  intro operation
  cases operation <;> decide

theorem selection (operation : Shift) (state : State) (value : Word)
    (count : BitVec 6) (flags : BitVec 32) (destination : Fin 16) :
    (if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 0
      then Functions.rol_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 1
      then Functions.ror_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 2
      then Functions.rcl_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 3
      then Functions.rcr_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 4
      then Functions.sal_shl_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 5
      then Functions.shr_spec 8 value count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 7
      then Functions.sar_spec 8 value count flags else pure (0#64,0#32,0#32)).run state =
      (specification operation value count flags).run state := by
  cases operation <;> fin_cases destination <;> rfl

theorem handler (operation : Shift) (state : State) (destination : Fin 16)
    (start immediateAddress next : BitVec 48) (prefixes : BitVec 52)
    (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32) (count : BitVec 8)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : immediateAddress.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (countPresent : state.mem.get? (immediateAddress.signExtend 52).toNat = some count) :
    ∃ output mask,
      (Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror .Mode_64bit start immediateAddress prefixes
        (rex true (extension operation) destination) (0xc1#8) (modRM (extension operation) destination) (0#8)).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (evaluate operation value (count.setWidth 6))) next) := by
  obtain ⟨output,mask,calculated⟩ := spec_executes operation state value (count.setWidth 6) flags
  refine ⟨output,mask,?_⟩
  unfold Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror
  dsimp only
  simp only [show ((0xc1#8) == (0xc0#8)) = false from rfl,
    show ((0xc1#8) == (0xd0#8)) = false from rfl,
    show ((0xc1#8) == (0xd2#8)) = false from rfl,
    show ((0xc1#8) == (0xc1#8)) = true from rfl,Bool.false_or,Bool.not_false,ite_true]
  rw [X86Move.operand_size64,run_bind,run_pure]
  dsimp only
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,run_bind,
    operand_register state (extension operation) destination value prefixes immediateAddress (1#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 3 = (0#3) from rfl,
    show Sail.BitVec.zeroExtend (0#3) 48 = (0#48) from rfl,run_bind,X86Move.add_pointer_zero]
  dsimp only
  simp only [show Functions.eq_bits_nat (0xc1#8) 208 = false from rfl,
    show Functions.eq_bits_nat (0xc1#8) 209 = false from rfl,
    show Functions.eq_bits_nat (0xc1#8) 210 = false from rfl,
    show Functions.eq_bits_nat (0xc1#8) 211 = false from rfl,
    show Functions.eq_bits_nat (0xc1#8) 192 = false from rfl,
    show Functions.eq_bits_nat (0xc1#8) 193 = true from rfl,
    Bool.false_eq_true,ite_false,ite_true]
  have address8 : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressSize]
  rw [address8]
  simp only [pure_bind,Sail.BitVec.signExtend,show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind,X86SubImmediate.read_immediate state immediateAddress pointer attributes count
    segments application rip countPresent]
  dsimp only
  simp only [rex_w,Bool.and_true,ite_true,count_mask64]
  simp only [run_bind,
    X86PrefixRead.add_pointer_checked state immediateAddress (1#48) next (by simpa using advance)]
  simp only [run_pure]
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  have lowValue : Sail.BitVec.truncate (value.zeroExtend 128) 64 = value :=
    X86Move.widen_truncate value
  simp only [lowValue,Functions.Mk_rflagsbits]
  rw [run_bind,selection,calculated]
  dsimp only
  change (do
    Functions.write_user_rflags output mask
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false
      ((evaluate operation value (count.setWidth 6)).zeroExtend 128) 3 (0#64) prefixes
      (rex true (extension operation) destination)
      (Functions._get_modr_m_r_m (modRM (extension operation) destination)) (3#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,write_flags state flags output mask flagsKnown quiet]
  dsimp only
  have write := X86MovePrefix.write_operand_register64
    (X86Flags.putFlags state (merged flags output mask)) (extension operation) destination
    (evaluate operation value (count.setWidth 6)) prefixes (updated_quiet _ _ quiet)
  simp only [Sail.BitVec.zeroExtend] at write
  rw [run_bind,write]
  apply X86Move.write_pointer64
  rw [diagnostic_put,updated_quiet _ _ quiet]

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_sal_sar_shl_shr_rcl_rcr_rol_ror := Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror }

theorem dispatch_original [OtherOpcodeHandlers] (operation : Shift) (destination : Fin 16)
    (mode : proc_mode) (start next : BitVec 48) (rexByte sib : BitVec 8) :
    Functions.one_byte_opcode_execute mode start next (X86LegacyFetch.packet (0xc1#8))
      rexByte (0xc1#8) (modRM (extension operation) destination) sib =
      OtherOpcodeHandlers.x86_sal_sar_shl_shr_rcl_rcr_rol_ror mode start next
        (X86LegacyFetch.packet (0xc1#8)) rexByte (0xc1#8) (modRM (extension operation) destination) sib := by
  unfold Functions.one_byte_opcode_execute
  rw [Functions.ext_one_byte_opcode_execute,if_neg (by decide)]
  repeat' tisa_shift_strict rw [if_neg (by decide)]
  rw [if_pos (by decide)]
  have group : Functions._get_modr_m_reg (modRM (extension operation) destination) =
      BitVec.ofNat 3 (extension operation).val := by
    cases operation <;> fin_cases destination <;> rfl
  rw [group]
  cases operation <;> rfl

theorem dispatch_linked (other : OtherOpcodeHandlers) (operation : Shift) (destination : Fin 16)
    (mode : proc_mode) (start next : BitVec 48) (rexByte sib : BitVec 8) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute mode start next (X86LegacyFetch.packet (0xc1#8))
      rexByte (0xc1#8) (modRM (extension operation) destination) sib =
      Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror mode start next
        (X86LegacyFetch.packet (0xc1#8)) rexByte (0xc1#8) (modRM (extension operation) destination) sib := by
  let : OtherOpcodeHandlers := linkedHandlers other
  exact dispatch_original operation destination mode start next rexByte sib

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (state : State) (destination : Fin 16)
    (origin : X86LegacyFetch.Window state (0xc1#8) true (extension operation) destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32) (count : BitVec 8)
    (advance : origin.next.toInt + 1 = next.toInt)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (countPresent : state.mem.get? (origin.next.signExtend 52).toNat = some count) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output mask,
      (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (evaluate operation value (count.setWidth 6))) next) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0xc1#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib : ∀ address16 : Bool,
      Functions.x86_decode_sib_p (modRM (extension operation) destination) address16 = false := by
    cases operation <;> fin_cases destination <;> decide
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0xc1#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes (extension operation) destination
    (modRM (extension operation) destination) noSib origin.step1 origin.step2 origin.step3
    origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode
    origin.application origin.rip origin.prefixByte origin.opcodeByte origin.modrmByte]
  rw [dispatch_linked other]
  apply handler operation state destination origin.address origin.next next (X86LegacyFetch.packet (0xc1#8))
    origin.attributes (origin.address.signExtend 64) value flags count (X86LegacyFetch.packet_segment _)
    (X86LegacyFetch.packet_address _) advance _ origin.segments origin.application origin.rip known
    flagsKnown quiet countPresent
  apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
  have := origin.step2
  have := origin.step3
  omega

theorem result_frame (state : State) (destination : Fin 16) (value : Word)
    (flags output mask : BitVec 32) (next : BitVec 48) :
    RegisterFrame {key destination,.rflags,.rip} state
      (X86Move.putPointer (put (X86Flags.putFlags state (merged flags output mask)) destination value) next) := by
  simpa [Finset.insert_comm] using
    ((flags_frame state (merged flags output mask)).trans (put_frame _ destination value)).trans
      (pointer_frame _ next)

theorem source_value (operation : Shift) (value : Word) (destination : Fin 12)
    (count : BitVec 8) (admitted : count.toNat < 64) :
    P1Scalar.evaluate (.shift operation .u64 destination destination count.toNat) [value] =
      some (evaluate operation value (count.setWidth 6)) := by
  cases operation <;>
    simp [P1Scalar.evaluate,P1Scalar.shiftWord,P1Scalar.narrow,evaluate,
      Shift.evaluate,admitted,BitVec.toNat_setWidth,Nat.mod_eq_of_lt admitted]

theorem source_rejects64 (operation : Shift) (value : Word) (destination : Fin 12) :
    P1Scalar.evaluate (.shift operation .u64 destination destination 64) [value] = none := by rfl

theorem native_masks64 (operation : Shift) (value : Word) :
    evaluate operation value ((64#8).setWidth 6) = value := by
  cases operation <;> simp [evaluate]

#print axioms left_bits
#print axioms xor_bit_executes
#print axioms parity_executes
#print axioms signed_value
#print axioms left_value
#print axioms right_value
#print axioms handler
#print axioms fetched
#print axioms result_frame
#print axioms source_value
#print axioms source_rejects64
#print axioms native_masks64
end Mettapedia.Machines.TIsa.X86Shift
