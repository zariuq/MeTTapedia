import Mettapedia.Machines.TIsa.X86WriteWords
import Mettapedia.Machines.TIsa.X86FrameLoad

/-!
# Fetched frame-word increment in the original Sail model

The no-SIB RDI + disp32 immediate ADD form is used by the native fuel
counter. The original handler performs displacement and operand reads,
sign extension of the immediate byte, modular ADD, bytewise memory writes,
flag updates and RIP advancement. The complete eight-byte fetch is linked
through the original opcode dispatcher.

The result frame changes only the data bytes, arithmetic flags and RIP.
Native buffer placement, the preceding budget checks, complete fuel-prefix
execution and whole-emitter refinement remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/ImmediateFunctions.lean.inc"
  sha256 "108927ecbf4e48e5f9e9be8f1410e6088bb434c053df5ab558fecfd752e45adf"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86FrameIncrement
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

example (state : State) :
    (Functions.binary_logext 8 1).run state = .ok (1 : Int) state := by rfl

theorem effective_disp32_immediate_size (overrideAddress : Bool)
    (displacementAddress : BitVec 48) (rex : BitVec 8) (immediateBytes : BitVec 3) :
    Functions.x86_effective_addr_32_64 .Mode_64bit overrideAddress displacementAddress rex
      (7#3) (2#2) (0#8) immediateBytes =
    Functions.x86_effective_addr_32_64 .Mode_64bit overrideAddress displacementAddress rex
      (7#3) (2#2) (0#8) (0#3) := by
  unfold Functions.x86_effective_addr_32_64
  simp only [show Functions.eq_bits_nat (2#2) 0 = false from rfl,
    show Functions.eq_bits_nat (2#2) 1 = false from rfl,
    show Functions.eq_bits_nat (2#2) 2 = true from rfl,
    show Functions.eq_bits_nat (7#3) 4 = false from rfl,
    Bool.false_eq_true, ite_false, ite_true]

theorem effective_frame_immediate_size (prefixes : BitVec 52)
    (displacementAddress : BitVec 48) (rex : BitVec 8) (immediateBytes : BitVec 3) :
    Functions.x86_effective_addr .Mode_64bit prefixes displacementAddress rex
      (7#3) (2#2) (0#8) immediateBytes =
    Functions.x86_effective_addr .Mode_64bit prefixes displacementAddress rex
      (7#3) (2#2) (0#8) (0#3) := by
  unfold Functions.x86_effective_addr
  dsimp only
  rw [effective_disp32_immediate_size]

theorem frame_operand_immediate_size (prefixes : BitVec 52)
    (displacementAddress : BitVec 48) (destination : Fin 16) (immediateBytes : BitVec 3) :
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes displacementAddress (X86FrameLoad.frameRex destination) (7#3) (2#2) (0#8) immediateBytes =
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes displacementAddress (X86FrameLoad.frameRex destination) (7#3) (2#2) (0#8) (0#3) := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  dsimp only
  rw [effective_frame_immediate_size]

theorem write_frame (state : State) (dataAddress : BitVec 48) (prefixes : BitVec 52)
    (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer value : Word) (flags : BitVec 32) (rex : BitVec 8)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (aligned : dataAddress &&& (7#48) = (0#48)) :
    (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (value.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes rex (7#3) (2#2) (0#8)).run state =
      .ok () (X86WriteWords.storeBytes 8 state dataAddress value) := by
  unfold Functions.x86_operand_to_reg_mem
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false,
    bind_assoc, pure_bind, Bool.true_and]
  rw [run_bind, X86FrameLoad.alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [size]
  simp only [pure_bind, Functions.select_base_register]
  unfold Functions.wme_size
  change (Functions.store_bytes_to_ea .Mode_64bit 8 8 (dataAddress.signExtend 64) none 3
    (Sail.BitVec.truncate (Sail.BitVec.zeroExtend value 128) 64)
    (X86FrameLoad.alignmentEnabled controls flags visible) false).run state = _
  rw [X86Move.widen_truncate]
  exact X86WriteWords.store_word_exact state dataAddress none attributes pointer value
    (X86FrameLoad.alignmentEnabled controls flags visible) false upper segments application rip (Or.inr aligned)

theorem read_immediate_one (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (1#8)) :
    (Functions.rme_size .Mode_64bit 8 1 (address.signExtend 64) none 1 ":X" false false).run state =
      .ok (1#128) state := by
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    pure (Sail.BitVec.zeroExtend byte 128) : SailM (BitVec 128)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes (1#8)
    segments application rip present]
  rfl

theorem handler_increment (state : State)
    (start displacementAddress immediateAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer frame value : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advanceDisplacement : displacementAddress.toInt + 4 = immediateAddress.toInt)
    (advanceImmediate : immediateAddress.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8))
    (immediatePresent : state.mem.get? (immediateAddress.signExtend 52).toNat = some (1#8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start displacementAddress
        prefixes (0x48#8) (0x83#8) (0x87#8) (0#8)).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (X86WriteWords.storeBytes 8 state dataAddress (value + (1#64)))
          (X86Flags.mergeFlags flags output)) next) := by
  obtain ⟨output, arithmetic⟩ := X86Alu.add_executes_defined state value (1#64) flags
  refine ⟨output, ?_⟩
  have size : Functions.select_operand_size .Mode_64bit false (0x48#8) false prefixes
      false false false = (pure 8 : SailM Int) :=
    X86Move.operand_size64 (0 : Fin 16) 7 prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x83#8) == (0x80#8)) = false from rfl,
    show ((0x83#8) == (0x82#8)) = false from rfl,
    show ((0x83#8) == (0xf6#8)) = false from rfl,
    show ((0x83#8) == (0x83#8)) = true from rfl,
    Bool.false_or, Bool.true_or]
  rw [size, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit true (0x48#8) true prefixes
      false false false = (pure 1 : SailM Int) from rfl]
  simp only [pure_bind, show Functions.check_range 1 4 1 = (pure 1 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_mod (0x87#8) = (2#2) from rfl,
    show Functions._get_modr_m_r_m (0x87#8) = (7#3) from rfl,
    X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  have rexZero : X86FrameLoad.frameRex (0 : Fin 16) = (0x48#8) := by decide
  rw [← rexZero]
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    show Functions.bits_of_int 1 3 = (1#3) from rfl,
    frame_operand_immediate_size prefixes displacementAddress (0 : Fin 16) (1#3), run_bind,
    X86FrameLoad.operand_frame state (0 : Fin 16) displacementAddress dataAddress prefixes
      attributes visible controls pointer frame value flags displacement addressOverride codeUpper
      dataUpper segments application rip frameKnown controlKnown flagsKnown visibleKnown effective
      aligned codePresent dataPresent]
  dsimp only
  rw [rexZero]
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) immediateAddress
    (by simpa using advanceDisplacement)]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [addressSize]
  simp only [pure_bind, bind_assoc, show Int.toNat (1 : Int) = 1 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, read_immediate_one state immediateAddress pointer attributes segments application rip immediatePresent]
  dsimp only
  rw [show Functions.ash_left_int 1 3 = 8 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate (1#128) 32) = 1 from rfl,
    run_bind, show (Functions.binary_logext 8 1).run state = .ok (1 : Int) state from rfl]
  dsimp only
  rw [show Functions.bits_of_int 1 48 = (1#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state immediateAddress (1#48) next
    (by simpa using advanceImmediate)]
  dsimp only
  rw [X86Move.truncate_pointer49, length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate]
  change (do
    let (result, resultFlags, undefined) ← Functions.gpr_add_spec_8 value (1#64) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (result.zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (0x48#8) (7#3) (2#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, arithmetic]
  dsimp only
  rw [run_bind, write_frame state dataAddress prefixes attributes visible controls pointer (value + (1#64))
    flags (0x48#8) addressOverride dataUpper segments application rip controlKnown flagsKnown visibleKnown aligned]
  dsimp only
  have unchanged := (X86WriteWords.storeBytes_frame 8 state dataAddress (value + (1#64))).registers_equal
  rw [run_bind, X86Flags.write_defined_flags _ flags output
    (by rw [unchanged]; exact flagsKnown) (by rw [unchanged]; exact quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  simp only [X86Flags.putFlags_other _ _ .log_register_writes (by decide), unchanged]
  exact quiet

@[instance_reducible] def linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with
    x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i := Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i }

theorem dispatch_increment (other : OtherOpcodeHandlers) (start displacementAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start displacementAddress
      (X86LegacyFetch.packet (0x83#8)) (0x48#8) (0x83#8) (0x87#8) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 0 .Mode_64bit start displacementAddress
        (X86LegacyFetch.packet (0x83#8)) (0x48#8) (0x83#8) (0x87#8) (0#8) := by
  rfl

theorem fetched_increment (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (immediateAddress finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advanceDisplacement : origin.next.toInt + 4 = immediateAddress.toInt)
    (advanceImmediate : immediateAddress.toInt + 1 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x48#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x83#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0x87#8))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8))
    (immediatePresent : state.mem.get? (immediateAddress.signExtend 52).toNat = some (1#8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (X86WriteWords.storeBytes 8 state dataAddress (value + (1#64)))
          (X86Flags.mergeFlags flags output)) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x83#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib (address16 : Bool) : Functions.x86_decode_sib_p (0x87#8) address16 = false := by
    simp [Functions.x86_decode_sib_p, show Functions._get_modr_m_r_m (0x87#8) = (7#3) from rfl,
      show Functions._get_modr_m_mod (0x87#8) = (2#2) from rfl]
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x83#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 0 7 (0x87#8) noSib
    origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs origin.segments
    origin.longMode origin.codeMode origin.application origin.rip
    (by simpa only [show X86RegisterEncoding.rex true 0 7 = (0x48#8) from by decide] using prefixByte)
    opcodeByte modrmByte]
  rw [show X86RegisterEncoding.rex true 0 7 = (0x48#8) from by decide,
    dispatch_increment other]
  apply handler_increment state origin.address origin.next immediateAddress finish dataAddress
    (X86LegacyFetch.packet (0x83#8)) origin.attributes visible controls (origin.address.signExtend 64)
    frame value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advanceDisplacement advanceImmediate
  · apply X86FrameLoad.length_from_distance _ _ 8 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := immediateAddress)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact frameKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent
  · exact dataPresent
  · exact immediatePresent

theorem result_frame (state : State) (base : BitVec 48) (value : Word)
    (flags : BitVec 32) (finish : BitVec 48) :
    X86StateFrame.Frame {.rflags, .rip} (X86WriteWords.written base (List.range 8)) state
      (X86Move.putPointer (X86Flags.putFlags (X86WriteWords.storeBytes 8 state base value) flags) finish) := by
  have memory := X86WriteWords.storeBytes_frame 8 state base value
  have flagsFrame := X86Execution.flags_frame (X86WriteWords.storeBytes 8 state base value) flags
  have pointerFrame := X86Execution.pointer_frame
    (X86Flags.putFlags (X86WriteWords.storeBytes 8 state base value) flags) finish
  simpa using memory.trans (X86StateFrame.registerOnly (flagsFrame.trans pointerFrame))

namespace Controls

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)

private def mapped (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rdi (0x1f58#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x48#8)
  let memory := memory.insert 4097 (0x83#8)
  let memory := memory.insert 4098 (0x87#8)
  let memory := memory.insert 4099 (0xa8#8)
  let memory := memory.insert 4100 (0#8)
  let memory := memory.insert 4101 (0#8)
  let memory := memory.insert 4102 (0#8)
  let memory := memory.insert 4103 (1#8)
  let memory := memory.insert 8200 (42#8)
  let memory := (List.range 8).foldl (fun current index => current.insert (8192 + index)
    (value.extractLsb' (8 * index) 8)) memory
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (value : Word) : X86LegacyFetch.Basis (mapped value) where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [mapped, Std.ExtDHashMap.get?_insert]
  fault := by simp [mapped, Std.ExtDHashMap.get?_insert]
  msrs := by simp [mapped, Std.ExtDHashMap.get?_insert]
  segments := by simp [mapped, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [mapped, Std.ExtDHashMap.get?_insert]
  rip := by simp [mapped, Std.ExtDHashMap.get?_insert]

theorem increment_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (mapped value) =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (X86WriteWords.storeBytes 8 (mapped value) (0x2000#48) (value + (1#64)))
          (X86Flags.mergeFlags (0#32) output)) (0x1008#48)) := by
  apply fetched_increment other vector (mapped value) (origin value) (0x1007#48) (0x1008#48)
    (0x2000#48) visible controls (0x1f58#64) value (0#32) (0xa8#32)
    (by change (0x1003#48).toInt + 4 = (0x1007#48).toInt; decide) (by decide) (by decide)
    (by simp [mapped, lookup, key, cast_eq, Std.ExtDHashMap.get?_insert]; rfl)
    (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped]) (by decide) (by decide)
    (by simp [origin, mapped, List.range_succ, Std.ExtHashMap.getElem_insert])
    (by simp [origin, mapped, List.range_succ, Std.ExtHashMap.getElem_insert])
    (by simp [origin, mapped, List.range_succ, Std.ExtHashMap.getElem_insert])
  · intro index within
    interval_cases index <;> simp [origin, mapped, List.range_succ, X86Execution.address,
      Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [mapped, List.range_succ, X86Execution.address,
      Std.ExtHashMap.getElem_insert]
  · simp [mapped, List.range_succ, Std.ExtHashMap.getElem_insert]

theorem increment_wraps (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run (mapped (0xffffffffffffffff#64)) =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (X86WriteWords.storeBytes 8 (mapped (0xffffffffffffffff#64)) (0x2000#48) (0#64))
          (X86Flags.mergeFlags (0#32) output)) (0x1008#48)) := by
  simpa only [show (0xffffffffffffffff#64) + (1#64) = (0#64) from rfl] using
    increment_executes other vector (0xffffffffffffffff#64)

theorem wrong_answer_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (5#64)) = .ok () after ∧
      after.mem.get? 8192 = some (5#8) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, executed⟩ := increment_executes other vector (5#64)
  rintro ⟨after, wrongRun, wrongValue⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans wrongRun)).2
  rw [← same] at wrongValue
  change (X86WriteWords.storeBytes 8 (mapped (5#64)) (0x2000#48) (6#64)).mem.get? 8192 = some (5#8) at wrongValue
  have stored := X86WriteWords.store_word_byte (mapped (5#64)) (0x2000#48) (6#64) (by decide) 0 (by decide)
  change (X86WriteWords.storeBytes 8 (mapped (5#64)) (0x2000#48) (6#64)).mem.get? 8192 = some (6#8) at stored
  rw [stored] at wrongValue
  exact (by decide : some (6#8) ≠ some (5#8)) wrongValue

theorem exact_frame (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped value) = .ok () after ∧
      X86StateFrame.Frame {.rflags, .rip} (X86WriteWords.written (0x2000#48) (List.range 8))
        (mapped value) after := by
  obtain ⟨output, executed⟩ := increment_executes other vector value
  exact ⟨_, executed, result_frame (mapped value) (0x2000#48) (value + (1#64)) _ (0x1008#48)⟩

theorem suffix_preserved (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped value) = .ok () after ∧
      after.mem.get? 8200 = some (42#8) := by
  obtain ⟨after, executed, frame⟩ := exact_frame other vector value
  refine ⟨after, executed, ?_⟩
  rw [frame.memory 8200 (by decide)]
  simp [mapped, List.range_succ, Std.ExtHashMap.getElem_insert]

theorem omitted_write_footprint_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (5#64)) = .ok () after ∧
      X86StateFrame.Frame ∅ ∅ (mapped (5#64)) after := by
  rintro ⟨after, executed, frame⟩
  apply wrong_answer_refused other vector
  refine ⟨after, executed, ?_⟩
  rw [frame.memory 8192 (by simp)]
  simp [mapped, List.range_succ, Std.ExtHashMap.getElem_insert]

end Controls
end Mettapedia.Machines.TIsa.X86FrameIncrement

#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.handler_increment
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.fetched_increment
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.result_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.increment_executes
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.increment_wraps
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.wrong_answer_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.exact_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.suffix_preserved
#print axioms Mettapedia.Machines.TIsa.X86FrameIncrement.Controls.omitted_write_footprint_refused
