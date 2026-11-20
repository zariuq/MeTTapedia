import Mettapedia.Machines.TIsa.X86AddImmediate
import Mettapedia.Machines.TIsa.X86BranchCondition

/-!
# Original fetched full-word comparison against zero

The seven-byte CMP R10,imm32(0) form retains the 64-bit operand read,
signed immediate decoding, arithmetic flags and RIP advancement. Its zero
flag tests all 64 bits. Operand preservation and Boolean materialization
are composed by the consumer-side span proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86QwordZero
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

theorem operand64 (state : State) (value : Word) (prefixes : BitVec 52)
    (pointer : BitVec 48) (immediateBytes : BitVec 3) (known : lookup state 10 = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer (0x49#8) (2#3) (3#2) (0#8) immediateBytes).run state =
        .ok (Sail.BitVec.zeroExtend value 128,(0 : Int),(0#64)) state := by
  exact X86AddImmediate.operand state 10 value prefixes pointer immediateBytes known

theorem handler (state : State) (start immediateAddress next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : immediateAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (upper : immediateAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state 10 = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (immediatePresent : ∀ index < 4,
      state.mem.get? ((address immediateAddress.toInt index).signExtend 52).toNat =
        some ((0#32).extractLsb' (8 * index) 8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediateAddress
        prefixes (0x49#8) (0x81#8) (0xfa#8) (0#8)).run state =
      .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_zf (X86Flags.mergeFlags flags output) = Functions.zf_spec value.toNat := by
  obtain ⟨output,arithmetic⟩ := X86Alu.sub_executes_defined state value (0#64) flags
  have zero := X86Comparison.sub_zero state value (0#64) flags
  simp only [map_eq_pure_bind,run_bind,arithmetic,run_pure] at zero
  have zeroValue := (EStateM.Result.ok.inj zero).1
  refine ⟨output,?_,by simpa only [BitVec.sub_zero] using (X86Comparison.merged_zero flags output).trans zeroValue⟩
  have size : Functions.select_operand_size .Mode_64bit false (0x49#8) false prefixes
      false false false = (pure 8 : SailM Int) := X86Move.operand_size64 (7 : Fin 16) 10 prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x81#8) == (0x80#8)) = false from rfl,
    show ((0x81#8) == (0x82#8)) = false from rfl,
    show ((0x81#8) == (0xf6#8)) = false from rfl,
    show ((0x81#8) == (0x83#8)) = false from rfl,Bool.false_or]
  rw [size,run_bind,run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit false (0x49#8) true prefixes
      false false false = (pure 4 : SailM Int) from rfl]
  simp only [pure_bind,show Functions.check_range 1 4 4 = (pure 4 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_mod (0xfa#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xfa#8) = (2#3) from rfl,
    X86MovePrefix.segment64 prefixes (2#3) (0#8) segmentOverride addressOverride,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,show Functions.bits_of_int 4 3 = (4#3) from rfl,
    run_bind,operand64 state value prefixes immediateAddress (4#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl,run_bind,X86Move.add_pointer_zero]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressOverride]
  rw [addressSize]
  simp only [pure_bind,bind_assoc,show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,Sail.BitVec.signExtend]
  rw [run_bind,X86FrameStore.read_dword state immediateAddress pointer attributes (0#32)
    upper segments application rip immediatePresent]
  dsimp only
  rw [show Functions.ash_left_int 4 3 = 32 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate ((0#32).zeroExtend 128) 32) = 0 from rfl,
    run_bind,show (Functions.binary_logext 32 0).run state = .ok (0 : Int) state from rfl]
  dsimp only
  rw [show Functions.ash_left_int 8 3 = 64 from rfl,
    show Functions.loghead_int 64 0 = 0 from rfl,
    show Functions.bits_of_int 4 48 = (4#48) from rfl,run_bind,
    X86PrefixRead.add_pointer_checked state immediateAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate,show Functions.bits_of_int 0 64 = (0#64) from rfl,
    show Functions.gpr_arith_logic_spec 8 8 value (0#64) flags = Functions.gpr_sub_spec_8 value (0#64) flags from rfl]
  simp only [show ((8 : Nat) == 8) = true from rfl,Bool.true_or,ite_true]
  rw [run_bind,arithmetic]
  dsimp only
  rw [run_bind,X86Flags.write_defined_flags state flags output flagsKnown quiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact quiet

theorem dispatch (other : OtherOpcodeHandlers) (start immediateAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediateAddress (X86LegacyFetch.packet (0x81#8))
      (0x49#8) (0x81#8) (0xfa#8) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediateAddress
        (X86LegacyFetch.packet (0x81#8)) (0x49#8) (0x81#8) (0xfa#8) (0#8) := by rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (known : lookup state 10 = some value) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x49#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0xfa#8))
    (immediateBytes : ∀ index < 4,
      state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
        some ((0#32).extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) finish) ∧
      Functions._get_rflagsbits_zf (X86Flags.mergeFlags flags output) = Functions.zf_spec value.toNat := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x81#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p (0xfa#8) address16 = false := by decide
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x81#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 7 10 (0xfa#8) noSib origin.step1 origin.step2
    origin.step3 origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode
    origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [show rex true (7 : Fin 16) 10 = (0x49#8) from by decide,dispatch other]
  apply handler state origin.address origin.next finish (X86LegacyFetch.packet (0x81#8)) origin.attributes
    (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advance
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

theorem equal_sense (value : Word) (flags : BitVec 32)
    (zero : Functions._get_rflagsbits_zf flags = Functions.zf_spec value.toNat) :
    X86BranchCondition.value .zero flags = decide (value = 0) := by
  have zeroEq : value.toNat = 0 ↔ value = 0 := by
    constructor
    · exact fun zero => BitVec.eq_of_toNat_eq zero
    · rintro rfl
      rfl
  simp only [X86BranchCondition.value,zero,X86BranchCondition.zero_sense,zeroEq]

#print axioms handler
#print axioms fetched

end Mettapedia.Machines.TIsa.X86QwordZero
