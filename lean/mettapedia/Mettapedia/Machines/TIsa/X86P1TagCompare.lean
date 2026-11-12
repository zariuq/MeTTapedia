import Mettapedia.Machines.TIsa.X86SubImmediate
import Mettapedia.Machines.TIsa.X86DwordLoad

/-!
# Fetched 32-bit tag comparison in the actual p1 consumer

The original immediate CMP handler compares R10D with tag 6661, retaining
32-bit modular subtraction, defined flags, the instruction bytes and RIP.
Its zero flag is equivalent to equality of the loaded U32 value and the tag.
The instruction preserves all general registers and memory. Byte-result
materialization and complete consumer execution require their own joins.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1TagCompare

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
local instance : MemoryPrimitives := X86Memory.ordinary

theorem sub32_result (left right : BitVec 32) :
    Sail.BitVec.truncate (Functions.bits_of_int (left.toInt - right.toInt) 33) 32 = left - right := by
  rw [X86Alu.bits_of_int_eq]
  change (BitVec.ofInt 33 _).setWidth 32 = _
  rw [X86Alu.setWidth_ofInt 32 33 _ (by decide)]
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
  simp only [BitVec.ofInt_toInt, BitVec.sub_eq_add_neg]

theorem sub32_executes (state : State) (left right : BitVec 32) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_sub_spec_4 left right flags).run state = .ok (left - right, output, 0#32) state := by
  unfold Functions.gpr_sub_spec_4 Functions.pf_spec32 Functions.of_spec32
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl,
    show ((32 : Int) ≥b 0) = true from rfl, ite_true]
  rw [sub32_result]
  exact ⟨_, rfl⟩

theorem sub32_zero (state : State) (left right : BitVec 32) (flags : BitVec 32) :
    ((fun value : BitVec 32 × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_zf value.2.1) <$>
      Functions.gpr_sub_spec_4 left right flags).run state =
        .ok (Functions.zf_spec (left - right).toNat) state := by
  unfold Functions.gpr_sub_spec_4 Functions.pf_spec32 Functions.of_spec32
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl,
    show ((32 : Int) ≥b 0) = true from rfl, ite_true]
  simp only [sub32_result, Sail.BitVec.toNatInt]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_zf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']
  rfl

theorem read_register32 (state : State) (index : Fin 16) (value : Word) (rex : BitVec 8)
    (known : lookup state index = some value) :
    (Functions.rgfi_size (4#4) (BitVec.ofNat 4 index.val) rex).run state =
      .ok ((low32 value).zeroExtend 64) state := by
  unfold Functions.rgfi_size
  simp only [show Functions.eq_bits_nat (4#4) 1 = false from rfl,
    show Functions.eq_bits_nat (4#4) 2 = false from rfl,
    show Functions.eq_bits_nat (4#4) 4 = true from rfl, Bool.false_eq_true, ite_false, ite_true]
  unfold Functions.rr32
  have indexNat : Sail.BitVec.toNatInt (BitVec.ofNat 4 index.val) = index.val := by
    simp [Sail.BitVec.toNatInt]
  rw [indexNat]
  simp only [run_bind, rgfi_exact state index value known, run_pure]
  rfl

theorem operand_register32 (state : State) (value : BitVec 32) (prefixes : BitVec 52)
    (pointer : BitVec 48) (immediateBytes : BitVec 3)
    (known : lookup state 10 = some (value.zeroExtend 64)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 4 true false 3
      prefixes pointer (0x41#8) (2#3) (3#2) (0#8) immediateBytes).run state =
      .ok (value.zeroExtend 128, (0 : Int), (0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int ((4 : Nat) : Int) 4 = (4#4) from rfl,
    show Functions.reg_index (2#3) (0x41#8) (0#2) = (10#4) from rfl]
  have read := read_register32 state 10 (value.zeroExtend 64) (0x41#8) known
  change (Functions.rgfi_size (4#4) (10#4) (0x41#8)).run state = _ at read
  rw [run_bind, run_bind, read]
  have low : low32 (value.zeroExtend 64) = value := low32_extend32 false value
  rw [low]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (value.zeroExtend 64) 128 = value.zeroExtend 128 from by
    change (value.setWidth 64).setWidth 128 = value.setWidth 128
    exact BitVec.setWidth_setWidth (by decide)]
  rfl

theorem read_immediate32 (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (value : BitVec 32)
    (upper : address.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address address.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.rme_size .Mode_64bit 8 4 (address.signExtend 64) none 1 ":X" false false).run state =
      .ok (value.zeroExtend 128) state := by
  unfold Functions.rme_size
  rw [run_bind, X86ReadWords.code_dword_uses_rb state address attributes segments,
    X86ReadWords.rb_dword_exact state address pointer value ":X" upper application rip present]
  rfl

theorem select_cmp32 (value : BitVec 32) (flags : BitVec 32) :
    Functions.gpr_arith_logic_spec 4 8 (value.zeroExtend 64) (6661#64) flags =
      (do let (result, output, undefined) ← Functions.gpr_sub_spec_4 value (6661#32) flags
          pure (result.zeroExtend 64, output, undefined) : SailM (Word × BitVec 32 × BitVec 32)) := by
  unfold Functions.gpr_arith_logic_spec Functions.gpr_arith_logic_spec_4
  rw [X86DwordLoad.cut32]
  rfl

theorem handler_cmp32 (state : State) (start immediateAddress next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer : Word)
    (value : BitVec 32) (flags : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : immediateAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (upper : immediateAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state 10 = some (value.zeroExtend 64))
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (immediatePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediateAddress.toInt index).signExtend 52).toNat =
        some ((6661#32).extractLsb' (8 * index) 8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediateAddress
        prefixes (0x41#8) (0x81#8) (0xfa#8) (0#8)).run state =
      .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_zf (X86Flags.mergeFlags flags output) =
        Functions.zf_spec (value - (6661#32)).toNat := by
  obtain ⟨output, arithmetic⟩ := sub32_executes state value (6661#32) flags
  have zero := sub32_zero state value (6661#32) flags
  simp only [map_eq_pure_bind, run_bind, arithmetic, run_pure] at zero
  have zeroValue := (EStateM.Result.ok.inj zero).1
  refine ⟨output, ?_, (X86Comparison.merged_zero flags output).trans zeroValue⟩
  have size := X86DwordLoad.operand_size32 (7 : Fin 16) 10 prefixes operandOverride
  change Functions.select_operand_size .Mode_64bit false (0x41#8) false prefixes
    false false false = (pure 4 : SailM Int) at size
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x81#8) == (0x80#8)) = false from rfl,
    show ((0x81#8) == (0x82#8)) = false from rfl,
    show ((0x81#8) == (0xf6#8)) = false from rfl,
    show ((0x81#8) == (0x83#8)) = false from rfl, Bool.false_or]
  rw [size, run_bind, run_pure]
  dsimp only
  have immediateSize : Functions.select_operand_size .Mode_64bit false (0x41#8) true prefixes
      false false false = (pure 4 : SailM Int) := by
    simp [Functions.select_operand_size, Functions.in_64bit_mode, operandOverride]
  rw [immediateSize]
  simp only [pure_bind, show Functions.check_range 1 4 4 = (pure 4 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_mod (0xfa#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xfa#8) = (2#3) from rfl,
    X86MovePrefix.segment64 prefixes (2#3) (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (4 : Int) = 4 from rfl,
    show Functions.bits_of_int 4 3 = (4#3) from rfl,
    run_bind, operand_register32 state value prefixes immediateAddress (4#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl, run_bind, X86Move.add_pointer_zero]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [addressSize]
  simp only [pure_bind, bind_assoc, show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, read_immediate32 state immediateAddress pointer attributes (6661#32)
    upper segments application rip immediatePresent]
  dsimp only
  rw [show Functions.ash_left_int 4 3 = 32 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate ((6661#32).zeroExtend 128) 32) = 6661 from rfl,
    run_bind, show (Functions.binary_logext 32 6661).run state = .ok (6661 : Int) state from rfl]
  dsimp only
  rw [show Functions.loghead_int 32 6661 = 6661 from rfl,
    show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state immediateAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49, length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86DwordLoad.cut128]
  rw [show Functions.bits_of_int 6661 64 = (6661#64) from rfl, select_cmp32]
  simp only [bind_assoc, pure_bind,
    show ((8 : Nat) == 8) = true from rfl, Bool.true_or, ite_true]
  rw [run_bind, arithmetic]
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags state flags output flagsKnown quiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact quiet

set_option maxRecDepth 4096 in
theorem dispatch_cmp32 (other : OtherOpcodeHandlers) (start immediateAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediateAddress (X86LegacyFetch.packet (0x81#8))
      (0x41#8) (0x81#8) (0xfa#8) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediateAddress
        (X86LegacyFetch.packet (0x81#8)) (0x41#8) (0x81#8) (0xfa#8) (0#8) := by rfl

theorem fetched_cmp32 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (value : BitVec 32) (flags : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (known : lookup state 10 = some (value.zeroExtend 64))
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x41#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0xfa#8))
    (immediateBytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some ((6661#32).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) finish) ∧
      Functions._get_rflagsbits_zf (X86Flags.mergeFlags flags output) =
        Functions.zf_spec (value - (6661#32)).toNat := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x81#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p (0xfa#8) address16 = false := by decide
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x81#8) shape false state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 7 10 (0xfa#8) noSib origin.step1 origin.step2
    origin.step3 origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode
    origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [show rex false (7 : Fin 16) 10 = (0x41#8) from by decide, dispatch_cmp32 other]
  apply handler_cmp32 state origin.address origin.next finish (X86LegacyFetch.packet (0x81#8)) origin.attributes
    (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    (X86DwordLoad.packet_operand _) advance
  · apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact known
  · exact flagsKnown
  · exact quiet
  · exact immediateBytes

theorem equal_sense (value : BitVec 32) (flags : BitVec 32)
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec (value - (6661#32)).toNat) :
    X86BranchCondition.value .zero flags = decide (value = (6661#32)) := by
  have zeroEq : (value - (6661#32)).toNat = 0 ↔ value = (6661#32) := by
    constructor
    · intro zero
      apply BitVec.eq_of_toNat_eq
      have := value.isLt
      have := BitVec.toNat_sub value (6661#32)
      omega
    · intro same
      subst value
      decide
  simp only [X86BranchCondition.value, zero, X86BranchCondition.zero_sense, zeroEq]

theorem result_frame (state : State) (flags output : BitVec 32) (finish : BitVec 48) :
    X86Execution.RegisterFrame {.rflags,.rip} state
      (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) finish) :=
  X86Comparison.status_frame state (X86Flags.mergeFlags flags output) finish

end Mettapedia.Machines.TIsa.X86P1TagCompare
