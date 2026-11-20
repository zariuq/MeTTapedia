import Mettapedia.Machines.TIsa.X86Funding
import Mettapedia.Machines.TIsa.X86CmpImmediate64

/-! # Fetched comparison of a qword with an ABI frame field -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86FrameCompare

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86Funding.GenericMemory (linkedHandlers)
local instance : MemoryPrimitives := X86Memory.ordinary

theorem handler (destination : Fin 16) (state : State) (start displacementAddress next dataAddress : BitVec 48)
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
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e 8 .Mode_64bit start displacementAddress
        prefixes (X86FrameLoad.frameRex destination) (0x3b#8) (X86FrameLoad.frameModRM destination) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) next) ∧
        X86CmpImmediate64.Flags state left right flags output := by
  obtain ⟨output, calculated⟩ := X86Alu.sub_executes_defined state left right flags
  have calculated' : (Functions.gpr_arith_logic_spec 8 8 left right flags).run state =
      .ok (left - right, output, 0#32) state := calculated
  have carry := X86Comparison.sub_carry state left right flags
  have zero := X86Comparison.sub_zero state left right flags
  simp only [map_eq_pure_bind, run_bind, calculated, run_pure] at carry zero
  refine ⟨output, ?_, ⟨calculated, (X86Comparison.merged_carry _ _).trans (EStateM.Result.ok.inj carry).1,
    (X86Comparison.merged_zero _ _).trans (EStateM.Result.ok.inj zero).1⟩⟩
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x3b#8)) 1) = false from rfl,
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
  rw [show ((8 : Nat) == 8) = true from rfl, if_pos rfl]
  rw [run_bind, X86Flags.write_defined_flags state flags output flagsKnown quiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  exact (X86Flags.putFlags_other _ _ .log_register_writes (by decide)).trans quiet

theorem fetched (destination : Fin 16) (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
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
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x3b#8))
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
        (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) finish) ∧
      X86CmpImmediate64.Flags state left right flags output := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x3b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x3b#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes destination 7 (X86FrameLoad.frameModRM destination)
    (X86FrameLoad.frame_no_sib destination) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change ∃ output,
    (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e 8 .Mode_64bit origin.address origin.next
      (X86LegacyFetch.packet (0x3b#8)) (X86FrameLoad.frameRex destination) (0x3b#8)
      (X86FrameLoad.frameModRM destination) (0#8)).run state = _ ∧ _
  apply handler destination state origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x3b#8)) origin.attributes visible controls
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

end Mettapedia.Machines.TIsa.X86FrameCompare
