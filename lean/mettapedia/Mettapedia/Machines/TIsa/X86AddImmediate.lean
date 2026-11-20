import Mettapedia.Machines.TIsa.X86Comparison
import Mettapedia.Machines.TIsa.X86RegisterIncrement
import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86DwordLoad
import Mathlib.Tactic.NormNum

/-!
# Fetched unsigned-overflow check for a positive disp32 addition

The original 81 /0 register ADD form reads the four-byte immediate 16,
performs modular 64-bit addition, writes defined arithmetic flags and advances
RIP. Carry holds exactly when the unbounded unsigned sum reaches 2^64.
The complete seven-byte fetch covers every destination register and changes
only that register, flags and RIP. Bounds-span and consumer composition are
separate obligations. Nonoverflow and wraparound flag controls are included.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86AddImmediate
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem power64 : (2 ^i (64 : Int)) = (18446744073709551616 : Int) := by decide +kernel

theorem raw_sum (left right : Word) :
    Functions.bits_of_int (Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right) 65 =
      BitVec.ofNat 65 (left.toNat + right.toNat) := by
  rw [X86Alu.bits_of_int_eq]
  have same : Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right = ((left.toNat + right.toNat : Nat) : Int) := by
    simp [Sail.BitVec.toNatInt]
  rw [same,BitVec.ofInt_natCast]

theorem raw_sum_nat (left right : Word) :
    (Functions.bits_of_int (Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right) 65).toNat =
      left.toNat + right.toNat := by
  rw [raw_sum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
  have := left.isLt
  have := right.isLt
  omega

theorem carry_word (state : State) (raw : BitVec 65) :
    (Functions.cf_spec64 raw).run state =
      .ok (Functions.bool_to_bits (2 ^ 64 ≤ raw.toNat)) state := by
  unfold Functions.cf_spec64 Functions.unsigned_byte_p_int
  simp only [show ((64 : Int) ≥b 0) = true from rfl,run_bind,run_assert,run_pure,ite_true]
  apply congrArg (fun flag : Bool => (EStateM.Result.ok (Functions.bool_to_bits flag) state :
    EStateM.Result (Sail.Error exception) State (BitVec 1)))
  norm_num [Sail.BitVec.toNatInt,power64]
  simp only [← decide_not, Nat.not_le]

theorem carry_raw (state : State) (left right : Word) :
    (Functions.cf_spec64 (Functions.bits_of_int (Sail.BitVec.toNatInt left + Sail.BitVec.toNatInt right) 65)).run state =
      .ok (Functions.bool_to_bits (2 ^ 64 ≤ left.toNat + right.toNat)) state := by
  rw [carry_word,raw_sum_nat]

theorem add_carry (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_cf value.2.1) <$>
      Functions.gpr_add_spec_8 left right flags).run state =
        .ok (Functions.bool_to_bits (2 ^ 64 ≤ left.toNat + right.toNat)) state := by
  unfold Functions.gpr_add_spec_8
  simp only [map_eq_pure_bind,run_bind,carry_raw]
  unfold Functions.pf_spec64 Functions.of_spec64 Functions.signed_byte_p_int Functions.logbitp_int
  simp only [run_bind,run_pure,run_assert,
    show ((0 : Int) ≥b 0) = true from rfl,
    show ((64 : Int) ≥b 0) = true from rfl,ite_true]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_cf,
    Functions._update_rflagsbits_cf,Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb,BitVec.extractLsb,Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem operand (state : State) (destination : Fin 16) (value : Word)
    (prefixes : BitVec 52) (pointer : BitVec 48) (immediateBytes : BitVec 3)
    (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer (rex true 0 destination)
      (Functions._get_modr_m_r_m (modRM 0 destination)) (3#2) (0#8) immediateBytes).run state =
        .ok (Sail.BitVec.zeroExtend value 128,(0 : Int),(0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl,ite_true,pure_bind]
  rw [show Functions.bits_of_int ((8 : Nat) : Int) 4 = (8#4) from rfl,destination_register]
  rw [run_bind,run_bind,X86Move.read_register64 state destination _ value known]
  rfl

theorem handler_add16 (state : State) (destination : Fin 16) (start immediate next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : immediate.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediate.toInt index).signExtend 52).toNat =
        some ((16#32).extractLsb' (8 * index) 8)) :
    ∃ output, (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start immediate
      prefixes (rex true 0 destination) (0x81#8) (modRM 0 destination) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (value + 16)) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (2 ^ 64 ≤ value.toNat + 16) := by
  obtain ⟨output,calculated⟩ := X86Alu.add_executes_defined state value (16#64) flags
  have carry := add_carry state value (16#64) flags
  simp only [map_eq_pure_bind,run_bind,calculated,run_pure] at carry
  have cf := (EStateM.Result.ok.inj carry).1
  refine ⟨output,?_,by simpa only [show (16#64).toNat = 16 from rfl] using
    (X86Comparison.merged_carry flags output).trans cf⟩
  have size := X86Move.operand_size64 (0 : Fin 16) destination prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x81#8) == (0x80#8)) = false from rfl,
    show ((0x81#8) == (0x82#8)) = false from rfl,
    show ((0x81#8) == (0xf6#8)) = false from rfl,
    show ((0x81#8) == (0x83#8)) = false from rfl,Bool.false_or]
  rw [size,run_bind,run_pure]
  dsimp only
  have immediateSize : Functions.select_operand_size .Mode_64bit false (rex true 0 destination) true prefixes
      false false false = (pure 4 : SailM Int) := by
    simp [Functions.select_operand_size,Functions.in_64bit_mode,operandOverride]
  rw [immediateSize]
  simp only [pure_bind,show Functions.check_range 1 4 4 = (pure 4 : SailM Int) from rfl]
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,show Functions.bits_of_int 4 3 = (4#3) from rfl,
    run_bind,operand state destination value prefixes immediate (4#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl,run_bind,X86Move.add_pointer_zero]
  dsimp only
  have addressWidth : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressSize]
  rw [addressWidth]
  simp only [pure_bind,bind_assoc,show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,Sail.BitVec.signExtend]
  have upper : immediate.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := next)
    omega
  rw [run_bind,X86FrameStore.read_dword state immediate pointer attributes (16#32)
    upper segments application rip bytes]
  dsimp only
  rw [show Functions.ash_left_int 4 3 = 32 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate ((16#32).zeroExtend 128) 32) = 16 from rfl,
    run_bind,show (Functions.binary_logext 32 16).run state = .ok (16 : Int) state from rfl]
  dsimp only
  rw [show Functions.ash_left_int 8 3 = 64 from rfl,
    show Functions.loghead_int 64 16 = 16 from rfl,
    show Functions.bits_of_int 4 48 = (4#48) from rfl,run_bind,
    X86PrefixRead.add_pointer_checked state immediate (4#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate]
  change (do
    let (result,resultFlags,undefined) ← Functions.gpr_add_spec_8 value (16#64) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (Sail.BitVec.zeroExtend result 128) 3
      (0#64) prefixes (rex true 0 destination)
      (Functions._get_modr_m_r_m (modRM 0 destination)) (3#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,calculated]
  dsimp only
  rw [run_bind,X86MovePrefix.write_operand_register64 state 0 destination (value + (16#64)) prefixes quiet]
  dsimp only
  rw [run_bind,X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide),diagnostic_put]
  exact quiet

theorem dispatch_add16 (other : OtherOpcodeHandlers) (destination : Fin 16) (start immediate : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediate (X86LegacyFetch.packet (0x81#8))
      (rex true 0 destination) (0x81#8) (modRM 0 destination) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start immediate
        (X86LegacyFetch.packet (0x81#8)) (rex true 0 destination) (0x81#8) (modRM 0 destination) (0#8) := by
  fin_cases destination <;> rfl

theorem fetched_add16 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (site : X86LegacyFetch.Window state (0x81#8) true 0 destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32)
    (advance : site.next.toInt + 4 = next.toInt)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (bytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address site.next.toInt index).signExtend 52).toNat =
        some ((16#32).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (value + 16)) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (2 ^ 64 ≤ value.toNat + 16) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (0x81#8)
    ((X86LegacyFetch.checkOpcode_iff _).mp (by decide)) true state 0 destination site,dispatch_add16]
  apply handler_add16 state destination site.address site.next next (X86LegacyFetch.packet (0x81#8))
    site.attributes (site.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _)
    (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _) advance _ site.segments site.application
    site.rip known flagsKnown quiet bytes
  apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
  have := site.step2
  have := site.step3
  omega

def code (destination : Fin 16) : List Nat :=
  [(rex true 0 destination).toNat,0x81,(modRM 0 destination).toNat,16,0,0,0]

structure Inputs (state : State) (destination : Fin 16) extends X86LegacyFetch.Basis state where
  value : Word
  flags : BitVec 32
  known : lookup state destination = some value
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  upper : address.toInt + 7 < (2 ^ 47 : Int)
  loaded : X86Execution.codeLoaded state address.toInt (code destination)

theorem executes_add16 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (input : Inputs state destination) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      RegisterFrame (X86RegisterIncrement.writes destination) state after ∧
      lookup after destination = some (input.value + 16) ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((X86Execution.address input.address.toInt 7).signExtend 64) ∧
      Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (2 ^ 64 ≤ input.value.toNat + 16) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  let site := X86Execution.windowAt state state input.toBasis (RegisterFrame.refl X86Execution.dataRegisters state)
    input.upper 0 (by decide) (by simpa [X86Execution.address] using input.rip) (code destination) input.loaded
    0 destination (0x81#8) (by rfl) (by rfl) (by rfl)
  let next := X86Execution.address input.address.toInt 7
  have at3 : site.next.toInt = input.address.toInt + 3 :=
    X86Execution.address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 3 (by decide)
  have at7 : next.toInt = input.address.toInt + 7 :=
    X86Execution.address_toInt _ (by simpa using BitVec.le_toInt input.address) input.upper 7 (by decide)
  have bytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address site.next.toInt index).signExtend 52).toNat =
        some ((16#32).extractLsb' (8 * index) 8) := by
    intro index within
    rw [at3]
    have shift : X86Execution.address (input.address.toInt + 3) index =
        X86Execution.address input.address.toInt (3 + index) := by
      simp [X86Execution.address,Int.add_assoc]
    rw [shift]
    exact input.loaded (3 + index) _ (by interval_cases index <;> rfl)
  obtain ⟨output,run,carry⟩ := fetched_add16 other vector state destination site next input.value input.flags
    (by omega) input.known input.flagsKnown input.quiet bytes
  let flags := X86Flags.mergeFlags input.flags output
  let after := X86Move.putPointer (X86Flags.putFlags (put state destination (input.value + 16)) flags) next
  refine ⟨after,flags,X86FuelPrefix.fetches_one state after run,
    X86RegisterIncrement.result_frame _ _ _ _ _,?_,?_,?_,carry⟩
  · rw [X86Move.lookup_putPointer,X86Flags.putFlags_gpr,lookup_put_same]
  · rw [(pointer_frame _ next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags,Std.ExtDHashMap.get?_insert_self]
  · simp only [after,next,X86Move.putPointer,Std.ExtDHashMap.get?_insert_self]

example : code 14 = [0x49,0x81,0xc6,16,0,0,0] := by decide

theorem carry_clear (state : State) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_cf value.2.1) <$>
      Functions.gpr_add_spec_8 (32#64) (16#64) flags).run state = .ok (0#1) state := by
  simpa [Functions.bool_to_bits] using add_carry state (32#64) (16#64) flags

theorem carry_set (state : State) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_cf value.2.1) <$>
      Functions.gpr_add_spec_8 (0xfffffffffffffff8#64) (16#64) flags).run state = .ok (1#1) state := by
  simpa [Functions.bool_to_bits] using add_carry state (0xfffffffffffffff8#64) (16#64) flags

#print axioms add_carry
#print axioms executes_add16
#print axioms carry_clear
#print axioms carry_set

end Mettapedia.Machines.TIsa.X86AddImmediate
