import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86PrefixRead
import Mettapedia.Machines.TIsa.X86StateFrame

/-! Arithmetic on declared frame words in the x86 instruction semantics. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86Funding.GenericMemory
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

theorem subtract_to_handler (destination : Fin 16) (state : State) (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer frame left right : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (leftKnown : lookup state destination = some left)
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
        some (right.extractLsb' (8 * index) 8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e 4 .Mode_64bit start displacementAddress
        prefixes (X86FrameLoad.frameRex destination) (0x2b#8) (X86FrameLoad.frameModRM destination) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state destination (left - right)) (X86Flags.mergeFlags flags output)) next) := by
  obtain ⟨output, calculated⟩ := X86Alu.sub_executes_defined state left right flags
  have calculated' : (Functions.gpr_arith_logic_spec 8 4 left right flags).run state =
      .ok (left - right, output, 0#32) state := calculated
  refine ⟨output, ?_⟩
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x2b#8)) 1) = false from rfl,
    X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [X86FrameLoad.frame_destination, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    run_bind, X86Move.read_register64 state destination _ left leftKnown]
  dsimp only
  rw [X86FrameLoad.frame_mod, X86FrameLoad.frame_rm,
    X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    X86FrameLoad.operand_frame state destination displacementAddress dataAddress prefixes attributes visible controls
      pointer frame right flags displacement addressOverride codeUpper dataUpper segments application rip
      frameKnown controlKnown flagsKnown visibleKnown effective aligned codePresent dataPresent]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, run_bind, calculated']
  dsimp only
  rw [show ((4 : Nat) == 8) = false from rfl, if_neg (by decide : ¬false = true)]
  rw [run_bind, X86FrameLoad.write_destination state destination (left - right) quiet]
  have currentFlags : (put state destination (left - right)).regs.get? .rflags = some flags :=
    (put_flags state destination (left - right)).trans flagsKnown
  have currentQuiet : (put state destination (left - right)).regs.get? .log_register_writes = some false := by
    simpa only [diagnostic_put] using quiet
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags _ flags output currentFlags currentQuiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact currentQuiet

abbrev subtract_handler := subtract_to_handler 14

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { X86Arithmetic.linkedHandlers other with
    x86_add_adc_sub_sbb_or_and_xor_cmp_g_e := Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e }

theorem fetched_subtract_to (destination : Fin 16) (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame left right : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (leftKnown : lookup state destination = some left)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat =
      some (X86FrameLoad.frameRex destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x2b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat =
      some (X86FrameLoad.frameModRM destination))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (right.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (put state destination (left - right)) (X86Flags.mergeFlags flags output)) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x2b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x2b#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes destination 7 (X86FrameLoad.frameModRM destination)
    (X86FrameLoad.frame_no_sib destination) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change ∃ output,
    (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e 4 .Mode_64bit origin.address origin.next
      (X86LegacyFetch.packet (0x2b#8)) (X86FrameLoad.frameRex destination) (0x2b#8)
      (X86FrameLoad.frameModRM destination) (0#8)).run state = _
  apply subtract_to_handler destination state origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x2b#8)) origin.attributes visible controls
    (origin.address.signExtend 64) frame left right flags displacement
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) advance
  · apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact frameKnown
  · exact leftKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent
  · exact dataPresent

abbrev fetched_subtract := fetched_subtract_to 14

theorem subtract_to_frame (destination : Fin 16) (state : State) (value : Word) (flags : BitVec 32) (finish : BitVec 48) :
    X86StateFrame.Frame {key destination, .rflags, .rip} ∅ state
      (X86Move.putPointer (X86Flags.putFlags (put state destination value) flags) finish) := by
  apply X86StateFrame.registerOnly
  simpa using ((X86Execution.put_frame state destination value).trans
    (X86Execution.flags_frame _ flags)).trans (X86Execution.pointer_frame _ finish)

abbrev subtract_frame := subtract_to_frame 14

theorem add_handler (state : State) (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6)
    (controls : Vector (BitVec 64) 17) (pointer frame left right : Word)
    (flags : BitVec 32) (displacement : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : displacementAddress.toInt + 4 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (sourceKnown : lookup state 15 = some right)
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
        some (left.extractLsb' (8 * index) 8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 0 .Mode_64bit start displacementAddress
        prefixes (X86FrameLoad.frameRex 15) (0x01#8) (X86FrameLoad.frameModRM 15) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (X86WriteWords.storeBytes 8 state dataAddress (left + right))
            (X86Flags.mergeFlags flags output)) next) := by
  obtain ⟨output, calculated⟩ := X86Alu.add_executes_defined state left right flags
  have calculated' : (Functions.gpr_arith_logic_spec 8 0 left right flags).run state =
      .ok (left + right, output, 0#32) state := calculated
  refine ⟨output, ?_⟩
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x01#8)) 1) = false from rfl,
    X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [X86FrameLoad.frame_destination, show Functions.bits_of_int 8 4 = (8#4) from rfl,
    run_bind, X86Move.read_register64 state 15 _ right sourceKnown]
  dsimp only
  rw [X86FrameLoad.frame_mod, X86FrameLoad.frame_rm,
    X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    X86FrameLoad.operand_frame state 15 displacementAddress dataAddress prefixes attributes visible controls
      pointer frame left flags displacement addressOverride codeUpper dataUpper segments application rip
      frameKnown controlKnown flagsKnown visibleKnown effective aligned codePresent dataPresent]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, run_bind, calculated']
  dsimp only
  simp only [show ((0 : Nat) == 8 || (0 : Nat) == 7) = false from rfl,
    Bool.false_eq_true, ite_false]
  change (do
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false ((left + right).zeroExtend 128) 3
      (dataAddress.signExtend 64) prefixes (X86FrameLoad.frameRex 15) (7#3) (2#2) (0#8)
    Functions.write_user_rflags output (0#32)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, X86FrameIncrement.write_frame state dataAddress prefixes attributes visible controls
    pointer (left + right) flags (X86FrameLoad.frameRex 15) addressOverride dataUpper segments application
    rip controlKnown flagsKnown visibleKnown aligned]
  dsimp only
  have unchanged := (X86WriteWords.storeBytes_frame 8 state dataAddress (left + right)).registers_equal
  rw [run_bind, X86Flags.write_defined_flags _ flags output
    (by rw [unchanged]; exact flagsKnown) (by rw [unchanged]; exact quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  simp only [X86Flags.putFlags_other _ _ .log_register_writes (by decide), unchanged]
  exact quiet

theorem add_frame (state : State) (address : BitVec 48) (value : Word)
    (flags : BitVec 32) (finish : BitVec 48) :
    X86StateFrame.Frame {.rflags, .rip} (X86WriteWords.written address (List.range 8)) state
      (X86Move.putPointer (X86Flags.putFlags (X86WriteWords.storeBytes 8 state address value) flags) finish) := by
  simpa using ((X86WriteWords.storeBytes_frame 8 state address value).trans
    (X86StateFrame.registerOnly (X86Execution.flags_frame _ flags))).trans
      (X86StateFrame.registerOnly (X86Execution.pointer_frame _ finish))

theorem fetched_add (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame left right : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (sourceKnown : lookup state 15 = some right)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat =
      some (X86FrameLoad.frameRex 15))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x01#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat =
      some (X86FrameLoad.frameModRM 15))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (left.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (X86WriteWords.storeBytes 8 state dataAddress (left + right)) (X86Flags.mergeFlags flags output)) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x01#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x01#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 15 7 (X86FrameLoad.frameModRM 15)
    (X86FrameLoad.frame_no_sib 15) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change ∃ output,
    (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 0 .Mode_64bit origin.address origin.next
      (X86LegacyFetch.packet (0x01#8)) (X86FrameLoad.frameRex 15) (0x01#8)
      (X86FrameLoad.frameModRM 15) (0#8)).run state = _
  apply add_handler state origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x01#8)) origin.attributes visible controls
    (origin.address.signExtend 64) frame left right flags displacement
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) advance
  · apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · have := BitVec.toInt_lt (x := finish)
    omega
  · exact dataUpper
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact frameKnown
  · exact sourceKnown
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent
  · exact dataPresent

end Mettapedia.Machines.TIsa.X86Funding.GenericMemory

namespace Mettapedia.Machines.TIsa.X86Funding.Placed

open _root_.X86Registers

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameStore.linkedHandlers (X86FrameLoad.linkedHandlers (GenericMemory.linkedHandlers other))

end Mettapedia.Machines.TIsa.X86Funding.Placed
