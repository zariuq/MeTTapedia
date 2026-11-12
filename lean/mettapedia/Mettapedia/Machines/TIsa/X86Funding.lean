import Mettapedia.Machines.TIsa.X86Symbolic
import Mettapedia.Machines.TIsa.X86OutcomeLoad
import Mettapedia.Machines.TIsa.X86FailureHandler
import Mettapedia.Machines.TIsa.X86ReturnPath
import Mettapedia.Machines.TIsa.X86Prologue

/-!
# Native funding blocks in the original Sail semantics

`Placed` composes the actual fetched instruction contracts for arbitrary
canonical code and frame locations and explicit architectural observations.
Payment takes six instructions and writes the eight receipt bytes. Exhaustion
takes five instructions and preserves memory at the supplied branch target.
The common result realizes the portable charge for valid entry receipts.

The input includes actual code/data reads, aligned effective frame addresses,
code separation and the canonical branch-target equation. Calibration controls
supply inhabited instances. The current C capture supplies the exact byte
window at any image placement. These are block-exit contracts; failure-handler,
ABI and whole-emitter composition remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86Funding.GenericGrade
open _root_.X86Registers X86RegisterRefinement X86PrefixRead
local instance : MemoryPrimitives := X86Memory.ordinary

def packet : BitVec 52 := X86LegacyFetch.packet (0xbf#8)

theorem handler (state : State) (start immediateAddress finish : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32)
    (advance : immediateAddress.toInt + 4 = finish.toInt)
    (length : Functions.check_instruction_length start finish (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediateAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_oi .Mode_64bit start immediateAddress packet
      (0x41#8) (0xbf#8) (0#8) (0#8)).run state =
      .ok () (X86Move.putPointer (put state 15 (value.zeroExtend 64)) finish) := by
  have upper : immediateAddress.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := finish)
    omega
  unfold Functions.x86_mov_op_en_oi
  dsimp only
  rw [show (((176 : Int) ≤b Sail.BitVec.toNatInt (0xbf#8)) &&
      ((Sail.BitVec.toNatInt (0xbf#8) ≤b (183 : Int)) : Bool)) = false from rfl]
  rw [show Functions.select_operand_size .Mode_64bit false (0x41#8) false packet false false false =
      (pure 4 : SailM Int) from rfl, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_address_size .Mode_64bit (some packet) = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, X86FrameStore.read_dword state immediateAddress pointer attributes value upper
    segments application rip present]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, add_pointer_checked state immediateAddress (4#48) finish (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  change (do
    Functions.wr32 (15#4) (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32)
    Functions.write_iptr .Mode_64bit finish).run state = _
  have write := wr32_exact state (15 : Fin 16) value quiet
  change (Functions.wr32 (15#4) value).run state = .ok () (put state 15 (value.zeroExtend 64)) at write
  rw [X86OutcomeLoad.narrowed, run_bind, write]
  change (Functions.write_iptr .Mode_64bit finish).run (put state 15 (value.zeroExtend 64)) = _
  exact X86Move.write_pointer64 _ finish
    ((put_other_register state (15 : Fin 16) (value.zeroExtend 64) .log_register_writes (by decide)).trans quiet)

theorem opcode_scan (state : State) (address next : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (advance : address.toInt + 1 = next.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (prefixByte : state.mem.get? (address.signExtend 52).toNat = some (0x41#8))
    (opcodeByte : state.mem.get? (next.signExtend 52).toNat = some (0xbf#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15).run state =
      .ok (packet, (0x41#8)) state := by
  rw [rex_advances_scan state address next pointer attributes false (0 : Fin 16) (15 : Fin 16)
    (0#8) 14 advance (by decide) (by decide) segments application rip prefixByte]
  exact X86LegacyFetch.grade_opcode_scan state next pointer attributes (0x41#8) 13
    segments application rip opcodeByte

theorem fetch_to_handler [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (origin : X86LegacyFetch.Basis state)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x41#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0xbf#8)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.x86_mov_op_en_oi .Mode_64bit origin.address origin.modrmAddress
        packet (0x41#8) (0xbf#8) (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, origin.status]
  dsimp only
  rw [run_bind, readRegister_exact, origin.fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state origin.control origin.attributes origin.msrs
    origin.segments origin.longMode origin.codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state origin.address origin.rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, opcode_scan state origin.address origin.opcodeAddress (origin.address.signExtend 64)
    origin.attributes origin.step1 origin.segments origin.application origin.rip prefixByte opcodeByte]
  dsimp only
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit origin.address (2#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state origin.address (2#48) origin.modrmAddress
    (by simpa using origin.step2)]
  dsimp only
  simp only [pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48) (grade : Funding.Grade)
    (advance : origin.modrmAddress.toInt + 4 = finish.toInt)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x41#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0xbf#8))
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.modrmAddress.toInt index).signExtend 52).toNat =
        some (grade.units.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 15 grade.word) finish) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [fetch_to_handler state origin prefixByte opcodeByte]
  change (Functions.x86_mov_op_en_oi .Mode_64bit origin.address origin.modrmAddress
    packet (0x41#8) (0xbf#8) (0#8) (0#8)).run state = _
  apply handler state origin.address origin.modrmAddress finish origin.attributes (origin.address.signExtend 64)
    grade.units advance
  · apply X86FrameLoad.length_from_distance _ _ 6 (by decide)
    have := origin.step2
    omega
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact quiet
  · exact present

theorem result_frame (state : State) (grade : Funding.Grade) (finish : BitVec 48) :
    X86StateFrame.Frame {.r15, .rip} ∅ state
      (X86Move.putPointer (put state 15 grade.word) finish) := by
  apply X86StateFrame.registerOnly
  simpa [key] using (X86Execution.put_frame state 15 grade.word).trans
    (X86Execution.pointer_frame _ finish)

end Mettapedia.Machines.TIsa.X86Funding.GenericGrade

namespace Mettapedia.Machines.TIsa.X86Funding.GenericMemory
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

theorem subtract_handler (state : State) (start displacementAddress next dataAddress : BitVec 48)
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
    (leftKnown : lookup state 14 = some left)
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
        prefixes (X86FrameLoad.frameRex 14) (0x2b#8) (X86FrameLoad.frameModRM 14) (0#8)).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state 14 (left - right)) (X86Flags.mergeFlags flags output)) next) := by
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
    run_bind, X86Move.read_register64 state 14 _ left leftKnown]
  dsimp only
  rw [X86FrameLoad.frame_mod, X86FrameLoad.frame_rm,
    X86FrameLoad.segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    X86FrameLoad.operand_frame state 14 displacementAddress dataAddress prefixes attributes visible controls
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
  rw [run_bind, X86FrameLoad.write_destination state 14 (left - right) quiet]
  have currentFlags : (put state 14 (left - right)).regs.get? .rflags = some flags :=
    (put_other_register state 14 (left - right) .rflags (by decide)).trans flagsKnown
  have currentQuiet : (put state 14 (left - right)).regs.get? .log_register_writes = some false :=
    (put_other_register state 14 (left - right) .log_register_writes (by decide)).trans quiet
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags _ flags output currentFlags currentQuiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact currentQuiet


abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { X86Arithmetic.linkedHandlers other with
    x86_add_adc_sub_sbb_or_and_xor_cmp_g_e := Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e }

theorem fetched_subtract (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame left right : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (leftKnown : lookup state 14 = some left)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat =
      some (X86FrameLoad.frameRex 14))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x2b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat =
      some (X86FrameLoad.frameModRM 14))
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
        (X86Flags.putFlags (put state 14 (left - right)) (X86Flags.mergeFlags flags output)) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x2b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x2b#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 14 7 (X86FrameLoad.frameModRM 14)
    (X86FrameLoad.frame_no_sib 14) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  change ∃ output,
    (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e 4 .Mode_64bit origin.address origin.next
      (X86LegacyFetch.packet (0x2b#8)) (X86FrameLoad.frameRex 14) (0x2b#8)
      (X86FrameLoad.frameModRM 14) (0#8)).run state = _
  apply subtract_handler state origin.address origin.next finish dataAddress
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

theorem subtract_frame (state : State) (value : Word) (flags : BitVec 32) (finish : BitVec 48) :
    X86StateFrame.Frame {.r14, .rflags, .rip} ∅ state
      (X86Move.putPointer (X86Flags.putFlags (put state 14 value) flags) finish) := by
  apply X86StateFrame.registerOnly
  simpa [key] using ((X86Execution.put_frame state 14 value).trans
    (X86Execution.flags_frame _ flags)).trans (X86Execution.pointer_frame _ finish)

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
open _root_.X86Registers X86RegisterRefinement
open X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def prefixCode (grade : Funding.Grade) : List Nat :=
  ([0x41,0xbf] ++ (List.range 4).map (fun index =>
    (grade.units.extractLsb' (8 * index) 8).toNat)) ++
    [0x4c,0x8b,0xb7,0xa0,0,0,0] ++ [0x4c,0x2b,0xb7,0xa8,0,0,0]

def code (grade : Funding.Grade) : List Nat := prefixCode grade ++ [0x4d,0x39,0xfe]
def branchCode (grade : Funding.Grade) (delta : BitVec 32 := 53#32) : List Nat :=
  code grade ++ [0x0f,0x82] ++
    (List.range 4).map (fun index => (delta.extractLsb' (8 * index) 8).toNat)
def completeCode (grade : Funding.Grade) (delta : BitVec 32 := 53#32) : List Nat :=
  branchCode grade delta ++ [0x4c,0x01,0xbf,0xa8,0,0,0]

abbrev writes : Finset Register := {.rip, .rflags, .r14, .r15}

noncomputable abbrev baseHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  X86FrameStore.linkedHandlers (X86FrameLoad.linkedHandlers (GenericMemory.linkedHandlers other))

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (baseHandlers other) extra

theorem writes_data : writes ⊆ dataRegisters := by decide

def position (start : BitVec 48) (offset : Nat) : BitVec 48 := address start.toInt offset

theorem position_exact (start : BitVec 48) (upper : start.toInt + 36 < (2 ^ 47 : Int))
    (offset : Nat) (within : offset ≤ 36) :
    (position start offset).toInt = start.toInt + offset :=
  address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper offset within

theorem position_zero (start : BitVec 48) : position start 0 = start := by
  apply BitVec.eq_of_toInt_eq
  have upper : start.toInt + 0 < (2 ^ 47 : Int) := by simpa using BitVec.toInt_lt (x := start)
  simpa [position] using address_toInt start.toInt (by simpa using BitVec.le_toInt start) upper 0 (by decide)

theorem position_shift (start : BitVec 48) (upper : start.toInt + 36 < (2 ^ 47 : Int))
    (offset index : Nat) (within : offset ≤ 36) :
    address (position start offset).toInt index = position start (offset + index) := by
  rw [position_exact start upper offset within]
  simp only [position, address, Nat.cast_add, Int.add_assoc]

structure Inputs (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word) where
  upper : origin.address.toInt + 36 < (2 ^ 47 : Int)
  frame : Word
  budgetAddress : BitVec 48
  receiptAddress : BitVec 48
  budgetUpper : budgetAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  receiptUpper : receiptAddress.toInt + 8 ≤ (2 ^ 47 : Int)
  base : lookup state 7 = some frame
  budgetEffective : frame + (160#32).signExtend 64 = budgetAddress.signExtend 64
  receiptEffective : frame + (168#32).signExtend 64 = receiptAddress.signExtend 64
  budgetAligned : budgetAddress &&& (7#48) = (0#48)
  receiptAligned : receiptAddress &&& (7#48) = (0#48)
  controls : Vector (BitVec 64) 17
  visible : Vector (BitVec 16) 6
  flags : BitVec 32
  controlKnown : state.regs.get? .ctrs = some controls
  visibleKnown : state.regs.get? .seg_visibles = some visible
  flagsKnown : state.regs.get? .rflags = some flags
  quiet : state.regs.get? .log_register_writes = some false
  loaded : codeLoaded state origin.address.toInt (completeCode grade delta)
  budget : ∀ index < 8,
    state.mem.get? ((address budgetAddress.toInt index).signExtend 52).toNat =
      some (allowance.extractLsb' (8 * index) 8)
  receipt : ∀ index < 8,
    state.mem.get? ((address receiptAddress.toInt index).signExtend 52).toNat =
      some (receipt.extractLsb' (8 * index) 8)
  outsideCode : ∀ index byte, (completeCode grade delta)[index]? = some byte →
    ((address origin.address.toInt index).signExtend 52).toNat ∉
      X86WriteWords.written receiptAddress (List.range 8)

theorem loaded_word32 (state : State) (start : BitVec 48) (grade : Funding.Grade) (delta : BitVec 32)
    (upper : start.toInt + 36 < (2 ^ 47 : Int))
    (loaded : codeLoaded state start.toInt (completeCode grade delta))
    (offset : Nat) (within : offset ≤ 36) (value : BitVec 32)
    (encoded : ∀ index : Fin 4, (completeCode grade delta)[offset + index.val]? =
      some (value.extractLsb' (8 * index.val) 8).toNat) :
    ∀ index < 4,
      state.mem.get? ((address (position start offset).toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8) := by
  intro index bounded
  rw [position_shift start upper offset index within]
  simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    loaded _ _ (encoded ⟨index, bounded⟩)

theorem loaded_grade (state : State) (start : BitVec 48) (grade : Funding.Grade) (delta : BitVec 32)
    (upper : start.toInt + 36 < (2 ^ 47 : Int))
    (loaded : codeLoaded state start.toInt (completeCode grade delta)) :
    ∀ index < 4,
      state.mem.get? ((address (position start 2).toInt index).signExtend 52).toNat =
        some (grade.units.extractLsb' (8 * index) 8) := by
  intro index within
  rw [position_shift start upper 2 index (by decide)]
  have byte : (completeCode grade delta)[2 + index]? =
      some (grade.units.extractLsb' (8 * index) 8).toNat := by
    interval_cases index <;> rfl
  simpa only [position, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded _ _ byte

theorem grade_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      RegisterFrame {.r15, .rip} state after ∧
      lookup after 15 = some grade.word ∧
      after.regs.get? .rip = some ((position origin.address 6).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have rip : state.regs.get? .rip = some ((position origin.address 0).signExtend 64) := by
    simpa only [position_zero] using origin.rip
  let site := rebase state state origin (RegisterFrame.refl dataRegisters state)
    input.upper 0 (by decide) rip
  have result := GenericGrade.fetched (handlers other extra) vector state site (position origin.address 6) grade
    (by change (position origin.address 2).toInt + 4 = (position origin.address 6).toInt
        rw [position_exact _ input.upper 2 (by decide), position_exact _ input.upper 6 (by decide)]
        omega)
    input.quiet
    (by simpa only [site, rebase, position_zero] using input.loaded 0 0x41 (by rfl))
    (by exact input.loaded 1 0xbf (by rfl))
    (loaded_grade state origin.address grade delta input.upper input.loaded)
  let after := X86Move.putPointer (put state 15 grade.word) (position origin.address 6)
  refine ⟨after, result, ?_, ?_, ?_⟩
  · simpa [after, key] using (put_frame state 15 grade.word).trans
      (pointer_frame _ (position origin.address 6))
  · exact ((X86StateFrame.registerOnly (pointer_frame (put state 15 grade.word)
      (position origin.address 6))).lookup 15 (by decide)).trans (lookup_put_same state 15 grade.word)
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem load_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (rip : current.regs.get? .rip = some ((position origin.address 6).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run current = .ok () after ∧
      RegisterFrame {.r14, .rip} current after ∧ lookup after 14 = some allowance ∧
      after.regs.get? .rip = some ((position origin.address 13).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 6 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have lowerOffset : (position origin.address 9).toInt + 4 = (position origin.address 13).toInt := by
    rw [position_exact _ input.upper 9 (by decide), position_exact _ input.upper 13 (by decide)]
    omega
  have result := X86FrameLoad.fetched_frame (handlers other extra) vector current 14 site
    (position origin.address 13) input.budgetAddress input.visible input.controls input.frame allowance flags
    (160#32) lowerOffset input.budgetUpper
    (((X86StateFrame.registerOnly framed).lookup 7 (by decide)).trans input.base)
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    input.budgetEffective input.budgetAligned
    (loaded 6 0x4c (by rfl)) (loaded 7 0x8b (by rfl)) (loaded 8 0xb7 (by rfl))
    (loaded_word32 current origin.address grade delta input.upper loaded 9 (by decide) (160#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.budget index within)
  let after := X86Move.putPointer (put current 14 allowance) (position origin.address 13)
  refine ⟨after, result, ?_, ?_, ?_⟩
  · simpa [after, key] using (put_frame current 14 allowance).trans
      (pointer_frame _ (position origin.address 13))
  · exact ((X86StateFrame.registerOnly (pointer_frame (put current 14 allowance)
      (position origin.address 13))).lookup 14 (by decide)).trans (lookup_put_same current 14 allowance)
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem subtract_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (leftKnown : lookup current 14 = some allowance)
    (rip : current.regs.get? .rip = some ((position origin.address 13).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (Functions.x86_fetch_decode_execute ()).run current = .ok () after ∧
      RegisterFrame {.r14, .rflags, .rip} current after ∧
      lookup after 14 = some (allowance - receipt) ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 20).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 13 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 16).toInt + 4 = (position origin.address 20).toInt := by
    rw [position_exact _ input.upper 16 (by decide), position_exact _ input.upper 20 (by decide)]
    omega
  obtain ⟨output, result⟩ := GenericMemory.fetched_subtract (handlers other extra) vector current site
    (position origin.address 20) input.receiptAddress input.visible input.controls input.frame allowance receipt flags
    (168#32) advance input.receiptUpper
    (((X86StateFrame.registerOnly framed).lookup 7 (by decide)).trans input.base) leftKnown
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned
    (loaded 13 0x4c (by rfl)) (loaded 14 0x2b (by rfl)) (loaded 15 0xb7 (by rfl))
    (loaded_word32 current origin.address grade delta input.upper loaded 16 (by decide) (168#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.receipt index within)
  let updated := put current 14 (allowance - receipt)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags updated nextFlags) (position origin.address 20)
  have tailFrame := (flags_frame updated nextFlags).trans (pointer_frame _ (position origin.address 20))
  refine ⟨after, nextFlags, result, ?_, ?_, ?_, ?_⟩
  · exact ((put_frame current 14 (allowance - receipt)).trans tailFrame).mono (by decide)
  · exact ((X86StateFrame.registerOnly tailFrame).lookup 14 (by decide)).trans
      (lookup_put_same current 14 (allowance - receipt))
  · rw [(pointer_frame (X86Flags.putFlags updated nextFlags) (position origin.address 20)).registers
      .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem remaining_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 3).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (allowance - receipt) ∧
      lookup after 15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 20).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨firstState, first, firstFrame, gradeRead, firstRip⟩ :=
    grade_step other extra vector state origin grade delta allowance receipt input
  have firstWide : RegisterFrame writes state firstState := firstFrame.mono (by decide)
  have firstFlags := (firstFrame.registers .rflags (by decide)).trans input.flagsKnown
  obtain ⟨secondState, second, secondFrame, allowanceRead, secondRip⟩ :=
    load_step other extra vector state firstState origin grade delta allowance receipt input firstWide
      input.flags firstFlags firstRip
  have secondWide : RegisterFrame writes state secondState :=
    (firstWide.trans secondFrame).mono (by decide)
  have secondFlags := (secondFrame.registers .rflags (by decide)).trans firstFlags
  obtain ⟨thirdState, nextFlags, third, thirdFrame, remainingRead, flagsRead, thirdRip⟩ :=
    subtract_step other extra vector state secondState origin grade delta allowance receipt input secondWide
      input.flags secondFlags allowanceRead secondRip
  refine ⟨thirdState, nextFlags,
    X86FuelPrefix.fetches_cons 2 state firstState thirdState first
      (X86FuelPrefix.fetches_cons 1 firstState secondState thirdState second
        (X86FuelPrefix.fetches_one secondState thirdState third)),
    (secondWide.trans thirdFrame).mono (by decide), remainingRead, ?_, flagsRead, thirdRip⟩
  exact ((X86StateFrame.registerOnly thirdFrame).lookup 15 (by decide)).trans
    (((X86StateFrame.registerOnly secondFrame).lookup 15 (by decide)).trans gradeRead)

theorem compare_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (remainingRead : lookup current 14 = some (allowance - receipt))
    (gradeRead : lookup current 15 = some grade.word)
    (rip : current.regs.get? .rip = some ((position origin.address 20).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (Functions.x86_fetch_decode_execute ()).run current = .ok () after ∧
      RegisterFrame {.rflags, .rip} current after ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits ((allowance - receipt).toNat < grade.word.toNat) ∧
      after.regs.get? .rip = some ((position origin.address 23).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  let site := windowAt state current origin (framed.mono writes_data) input.upper 20 (by decide) rip
    (completeCode grade delta) loaded 15 14 (0x39#8) (by rfl) (by rfl) (by rfl)
  obtain ⟨output, result, carry, _⟩ := X86Comparison.fetched_compare64 (handlers other extra) vector current
    15 14 site (allowance - receipt) grade.word flags gradeRead remainingRead flagsKnown
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags current nextFlags) site.next
  refine ⟨after, nextFlags, result, X86Comparison.status_frame current nextFlags site.next, ?_, ?_, ?_⟩
  · rw [(pointer_frame (X86Flags.putFlags current nextFlags) site.next).registers .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · exact (X86Comparison.merged_carry flags output).trans carry
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    rfl

theorem compare_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (allowance - receipt) ∧
      lookup after 15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits ((allowance - receipt).toNat < grade.word.toNat) ∧
      after.regs.get? .rip = some ((position origin.address 23).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, remainingRead, gradeRead, flagsRead, middleRip⟩ :=
    remaining_prefix other extra vector state origin grade delta allowance receipt input
  obtain ⟨after, nextFlags, last, lastFrame, nextFlagsRead, carryRead, finalRip⟩ :=
    compare_step other extra vector state middle origin grade delta allowance receipt input framed
      flags flagsRead remainingRead gradeRead middleRip
  refine ⟨after, nextFlags, X86FuelPrefix.fetches_then 3 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last),
    (framed.trans lastFrame).mono (by decide), ?_, ?_, nextFlagsRead, carryRead, finalRip⟩
  · exact ((X86StateFrame.registerOnly lastFrame).lookup 14 (by decide)).trans remainingRead
  · exact ((X86StateFrame.registerOnly lastFrame).lookup 15 (by decide)).trans gradeRead

theorem branch_executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      RegisterFrame writes state after ∧ lookup after 14 = some (allowance - receipt) ∧
      lookup after 15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some
        (if (allowance - receipt).toNat < grade.word.toNat then target.signExtend 64
          else (position origin.address 29).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, first, framed, remainingRead, gradeRead, flagsRead, carryRead, middleRip⟩ :=
    compare_executes other extra vector state origin grade delta allowance receipt input
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have step1 : (position origin.address 23).toInt + 1 = (position origin.address 24).toInt := by
    rw [position_exact _ input.upper 23 (by decide), position_exact _ input.upper 24 (by decide)]
    omega
  have step2 : (position origin.address 24).toInt + 1 = (position origin.address 25).toInt := by
    rw [position_exact _ input.upper 24 (by decide), position_exact _ input.upper 25 (by decide)]
    omega
  have advance : (position origin.address 25).toInt + 4 = (position origin.address 29).toInt := by
    rw [position_exact _ input.upper 25 (by decide), position_exact _ input.upper 29 (by decide)]
    omega
  have last := X86EscapeFetch.fetched_branch (baseHandlers other) extra vector .below middle
    (position origin.address 23) (position origin.address 24) (position origin.address 25)
    (position origin.address 29) target origin.control origin.attributes flags delta step1 step2 advance jump
    ((framed.registers .ms_reg (by decide)).trans origin.status)
    ((framed.registers .fault_reg (by decide)).trans origin.fault)
    ((framed.registers .msrs (by decide)).trans origin.msrs)
    ((framed.registers .seg_hidden_attrs (by decide)).trans origin.segments)
    origin.longMode origin.codeMode
    ((framed.registers .app_view (by decide)).trans origin.application) middleRip flagsRead
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    (loaded 23 0x0f (by rfl)) (loaded 24 0x82 (by rfl))
    (loaded_word32 middle origin.address grade delta input.upper loaded 25 (by decide) delta
      (by intro index; fin_cases index <;> rfl))
  have sense : X86BranchCondition.value .below flags =
      decide ((allowance - receipt).toNat < grade.word.toNat) := by
    simp only [X86BranchCondition.value, carryRead]
    generalize allowance - receipt = remainingWord
    generalize grade.word = gradeWord
    by_cases below : remainingWord.toNat < gradeWord.toNat <;> simp [Functions.bool_to_bits, below]
  rw [sense] at last
  let destination := if decide ((allowance - receipt).toNat < grade.word.toNat) then target
    else position origin.address 29
  let after := X86Move.putPointer middle destination
  have lastFrame := pointer_frame middle destination
  refine ⟨after, flags, X86FuelPrefix.fetches_then 4 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last),
    (framed.trans lastFrame).mono (by decide), ?_, ?_, ?_, ?_⟩
  · exact ((X86StateFrame.registerOnly lastFrame).lookup 14 (by decide)).trans remainingRead
  · exact ((X86StateFrame.registerOnly lastFrame).lookup 15 (by decide)).trans gradeRead
  · exact (lastFrame.registers .rflags (by decide)).trans flagsRead
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    dsimp only [destination]
    generalize allowance - receipt = remainingWord
    generalize grade.word = gradeWord
    by_cases below : remainingWord.toNat < gradeWord.toNat <;> simp [below]

theorem payment_step (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state current : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt)
    (framed : RegisterFrame writes state current) (flags : BitVec 32)
    (flagsKnown : current.regs.get? .rflags = some flags)
    (gradeRead : lookup current 15 = some grade.word)
    (rip : current.regs.get? .rip = some ((position origin.address 29).signExtend 64)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (Functions.x86_fetch_decode_execute ()).run current = .ok () after ∧
      X86StateFrame.Frame {.rflags, .rip}
        (X86WriteWords.written input.receiptAddress (List.range 8)) current after ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some ((receipt + grade.word).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 36).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let site := rebase state current origin (framed.mono writes_data) input.upper 29 (by decide) rip
  have loaded := framed.code_preserved origin.address.toInt _ input.loaded
  have advance : (position origin.address 32).toInt + 4 = (position origin.address 36).toInt := by
    rw [position_exact _ input.upper 32 (by decide), position_exact _ input.upper 36 (by decide)]
    omega
  obtain ⟨output, result⟩ := GenericMemory.fetched_add (handlers other extra) vector current site
    (position origin.address 36) input.receiptAddress input.visible input.controls input.frame receipt grade.word flags
    (168#32) advance input.receiptUpper
    (((X86StateFrame.registerOnly framed).lookup 7 (by decide)).trans input.base) gradeRead
    ((framed.registers .ctrs (by decide)).trans input.controlKnown) flagsKnown
    ((framed.registers .seg_visibles (by decide)).trans input.visibleKnown)
    ((framed.registers .log_register_writes (by decide)).trans input.quiet)
    input.receiptEffective input.receiptAligned
    (loaded 29 0x4c (by rfl)) (loaded 30 0x01 (by rfl)) (loaded 31 0xbf (by rfl))
    (loaded_word32 current origin.address grade delta input.upper loaded 32 (by decide) (168#32)
      (by intro index; fin_cases index <;> rfl))
    (by intro index within; rw [framed.memory]; exact input.receipt index within)
  let stored := X86WriteWords.storeBytes 8 current input.receiptAddress (receipt + grade.word)
  let nextFlags := X86Flags.mergeFlags flags output
  let after := X86Move.putPointer (X86Flags.putFlags stored nextFlags) (position origin.address 36)
  have tailFrame := (flags_frame stored nextFlags).trans (pointer_frame _ (position origin.address 36))
  refine ⟨after, nextFlags, result,
    GenericMemory.add_frame current input.receiptAddress (receipt + grade.word) nextFlags _, ?_, ?_, ?_⟩
  · intro index within
    rw [tailFrame.memory]
    exact X86WriteWords.store_word_byte current input.receiptAddress (receipt + grade.word)
      input.receiptUpper index within
  · rw [(pointer_frame (X86Flags.putFlags stored nextFlags) (position origin.address 36)).registers
      .rflags (by decide)]
    simp only [X86Flags.putFlags, Std.ExtDHashMap.get?_insert_self]
  · simp only [after, X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]

theorem paid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt)
    (fits : receipt.toNat + grade.units.toNat ≤ allowance.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame writes (X86WriteWords.written input.receiptAddress (List.range 8)) state after ∧
      codeLoaded after origin.address.toInt (completeCode grade delta) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some ((receipt + grade.word).extractLsb' (8 * index) 8)) ∧
      lookup after 14 = some (allowance - receipt) ∧ lookup after 15 = some grade.word ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((position origin.address 36).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have valid : receipt.toNat ≤ allowance.toNat := by omega
  have enough : grade.word.toNat ≤ (allowance - receipt).toNat :=
    (Funding.available_sub_iff allowance receipt grade valid).mp
      ((Funding.available_iff allowance receipt grade).mpr fits)
  obtain ⟨middle, flags, first, framed, remainingRead, gradeRead, flagsRead, middleRip⟩ :=
    branch_executes other extra vector state origin grade delta allowance receipt input target jump
  rw [if_neg (by omega)] at middleRip
  obtain ⟨after, nextFlags, last, lastFrame, receiptRead, nextFlagsRead, finalRip⟩ :=
    payment_step other extra vector state middle origin grade delta allowance receipt input framed
      flags flagsRead gradeRead middleRip
  have wholeFrame : X86StateFrame.Frame writes
      (X86WriteWords.written input.receiptAddress (List.range 8)) state after :=
    ((X86StateFrame.registerOnly framed).trans lastFrame).mono (by decide) (by simp)
  refine ⟨after, nextFlags, X86FuelPrefix.fetches_then 5 1 state middle after first
    (X86FuelPrefix.fetches_one middle after last), wholeFrame,
    wholeFrame.codeLoaded origin.address.toInt _ input.loaded input.outsideCode,
    receiptRead, ?_, ?_, nextFlagsRead, finalRip⟩
  · exact (lastFrame.lookup 14 (by decide)).trans remainingRead
  · exact (lastFrame.lookup 15 (by decide)).trans gradeRead

theorem exhausted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt)
    (valid : receipt.toNat ≤ allowance.toNat)
    (short : allowance.toNat < receipt.toNat + grade.units.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      RegisterFrame writes state after ∧ codeLoaded after origin.address.toInt (completeCode grade delta) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some (receipt.extractLsb' (8 * index) 8)) ∧
      lookup after 14 = some (allowance - receipt) ∧ lookup after 15 = some grade.word ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .rip = some (target.signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have lacks : (allowance - receipt).toNat < grade.word.toNat := by
    by_contra enough
    have available := (Funding.available_sub_iff allowance receipt grade valid).mpr (by omega)
    have fits := (Funding.available_iff allowance receipt grade).mp available
    omega
  obtain ⟨after, nextFlags, run, framed, remainingRead, gradeRead, flagsRead, finalRip⟩ :=
    branch_executes other extra vector state origin grade delta allowance receipt input target jump
  rw [if_pos lacks] at finalRip
  refine ⟨after, nextFlags, run, framed,
    framed.code_preserved origin.address.toInt _ input.loaded, ?_,
    remainingRead, gradeRead, flagsRead, finalRip⟩
  intro index within
  rw [framed.memory]
  exact input.receipt index within

theorem realizes_charge (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt)
    (valid : receipt.toNat ≤ allowance.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, lookup after 14 = some (allowance - receipt) ∧
      lookup after 15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      codeLoaded after origin.address.toInt (completeCode grade delta) ∧
      match Funding.charge allowance receipt grade with
      | .invalidReceipt => False
      | .exhausted => (X86FuelPrefix.fetches 5).run state = .ok () after ∧
          RegisterFrame writes state after ∧
          (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
            some (receipt.extractLsb' (8 * index) 8)) ∧
          after.regs.get? .rip = some (target.signExtend 64)
      | .paid following => (X86FuelPrefix.fetches 6).run state = .ok () after ∧
          X86StateFrame.Frame writes (X86WriteWords.written input.receiptAddress (List.range 8)) state after ∧
          (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
            some (following.extractLsb' (8 * index) 8)) ∧
          after.regs.get? .rip = some ((position origin.address 36).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  cases payment : Funding.charge allowance receipt grade with
  | invalidReceipt =>
      have invalid := (Funding.invalid_iff allowance receipt grade).mp payment
      omega
  | exhausted =>
      obtain ⟨_, short⟩ := (Funding.exhausted_iff allowance receipt grade).mp payment
      obtain ⟨after, nextFlags, executed, framed, codeRead, bytes, remainingRead, gradeRead, flagsRead, finalRip⟩ :=
        exhausted other extra vector state origin grade delta allowance receipt input target jump valid short
      exact ⟨after, nextFlags, remainingRead, gradeRead, flagsRead, codeRead, executed, framed, bytes, finalRip⟩
  | paid following =>
      obtain ⟨fits, rfl⟩ := (Funding.paid_iff allowance receipt following grade).mp payment
      obtain ⟨after, nextFlags, executed, framed, codeRead, bytes, remainingRead, gradeRead, flagsRead, finalRip⟩ :=
        paid other extra vector state origin grade delta allowance receipt input target jump fits
      exact ⟨after, nextFlags, remainingRead, gradeRead, flagsRead, codeRead, executed, framed, bytes, finalRip⟩

end Mettapedia.Machines.TIsa.X86Funding.Placed

namespace Mettapedia.Machines.TIsa.X86Funding.Controls
open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1
local instance : MemoryPrimitives := X86Memory.ordinary

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)

open Placed (prefixCode code branchCode completeCode)

structure Inputs (state : State) (allowance receiptWord : Word) (flags : BitVec 32)
    (image : List Nat) : Prop where
  status : state.regs.get? .ms_reg = some false
  fault : state.regs.get? .fault_reg = some false
  mode : state.regs.get? .msrs = some control
  segments : state.regs.get? .seg_hidden_attrs = some attributes
  application : state.regs.get? .app_view = some true
  quiet : state.regs.get? .log_register_writes = some false
  controlKnown : state.regs.get? .ctrs = some controls
  flagsKnown : state.regs.get? .rflags = some flags
  visibleKnown : state.regs.get? .seg_visibles = some visible
  rip : state.regs.get? .rip = some (4096#64)
  base : state.regs.get? .rdi = some (1048576#64)
  loaded : ∀ index : Fin image.length,
    state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 image[index.val])
  budget : ∀ index : Fin 8,
    state.mem.get? (1048736 + index.val) = some (allowance.extractLsb' (8 * index.val) 8)
  receipt : ∀ index : Fin 8,
    state.mem.get? (1048744 + index.val) = some (receiptWord.extractLsb' (8 * index.val) 8)

private noncomputable abbrev scalarHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { X86FrameStore.linkedHandlers (X86FuelPrefix.baseHandlers other) with
    x86_add_adc_sub_sbb_or_and_xor_cmp_g_e := Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e }

private noncomputable abbrev handlers (other : OtherOpcodeHandlers)
    (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86EscapeFetch.linked (scalarHandlers other) extra

theorem compare (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade)
    (allowance receiptWord : Word) (flags : BitVec 32)
    (input : Inputs state allowance receiptWord flags (code grade)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits ((allowance - receiptWord).toNat < grade.word.toNat) ∧
      after.regs.get? .rip = some (4119#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases input with ⟨status, fault, mode, segments, application, quiet, controlKnown,
    flagsKnown, visibleKnown, rip, base, loaded, budget, receipt⟩
  have prefixLoaded : ∀ index : Fin (prefixCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (prefixCode grade)[index.val]) := by
    intro index
    have within : index.val < (code grade).length := by
      simp only [code, List.length_append]
      omega
    have known := loaded ⟨index.val, within⟩
    simpa only [code, List.getElem_append_left index.isLt] using known
  obtain ⟨middle, middleFlags, first, framed, remainingRead, gradeRead, flagsRead, middleRip⟩ :=
    X86Symbolic.Controls.fund_remaining (handlers other extra)
      vector state grade allowance receiptWord flags status fault mode segments application quiet
      controlKnown flagsKnown visibleKnown rip base prefixLoaded budget receipt
  tisa_sail_bytes [loaded]
  have last : ∃ after nextFlags,
      (Functions.x86_fetch_decode_execute ()).run middle = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags} ∅ middle after ∧
      after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits ((allowance - receiptWord).toNat < grade.word.toNat) ∧
      after.regs.get? .rip = some (4119#64) := by
    tisa_sail_inherit [framed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    tisa_sail_step
    · tisa_sail_frame
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
    · apply BitVec.eq_of_getLsbD_eq
      intro index within
      have zero : index = 0 := by omega
      subst index
      generalize allowance - receiptWord = remainingWord
      generalize grade.word = gradeWord
      simp [Functions._get_rflagsbits_cf,
        Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
        Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
        Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
        Functions.regval_from_reg,
        Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb,
        BitVec.extractLsb, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        Sail.BitVec.toNatInt]
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
  obtain ⟨after, nextFlags, finalStep, finalFrame, finalFlags, carryValue, finalRip⟩ := last
  refine ⟨after, nextFlags,
    X86FuelPrefix.fetches_then 3 1 state middle after first
      (X86FuelPrefix.fetches_one middle after finalStep),
    ?_, ?_, ?_, finalFlags, carryValue, finalRip⟩
  · apply (framed.trans finalFrame).mono
    · intro register member
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
    · simp
  · exact (finalFrame.registers .r14 (by decide)).trans remainingRead
  · exact (finalFrame.registers .r15 (by decide)).trans gradeRead


def branchTarget (delta : BitVec 32) : BitVec 48 := BitVec.ofInt 48 (4125 + delta.toInt)

theorem branchTarget_exact (delta : BitVec 32) :
    (branchTarget delta).toInt = 4125 + delta.toInt := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · have lower := BitVec.le_toInt delta
    omega
  · have upper := BitVec.toInt_lt (x := delta)
    omega

theorem branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade) {delta : BitVec 32}
    (allowance receiptWord : Word) (flags : BitVec 32)
    (input : Inputs state allowance receiptWord flags (branchCode grade delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      Functions._get_rflagsbits_cf nextFlags =
        Functions.bool_to_bits ((allowance - receiptWord).toNat < grade.word.toNat) ∧
      after.regs.get? .rip = some
        (if (allowance - receiptWord).toNat < grade.word.toNat then
          (branchTarget delta).signExtend 64 else (4125#64)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases input with ⟨status, fault, mode, segments, application, quiet, controlKnown,
    flagsKnown, visibleKnown, rip, base, loaded, budget, receipt⟩
  have prefixLoaded : ∀ index : Fin (code grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (code grade)[index.val]) := by
    intro index
    have within : index.val < (branchCode grade delta).length := by
      simp only [branchCode, List.length_append]
      omega
    have known := loaded ⟨index.val, within⟩
    simpa only [branchCode, List.getElem_append_left
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega : index.val <
        (code grade ++ [0x0f,0x82]).length), List.getElem_append_left index.isLt] using known
  have encodedDelta : ∀ index : Fin 4, state.mem.get? (4121 + index.val) =
      some (delta.extractLsb' (8 * index.val) 8) := by
    intro index
    have within : 25 + index.val < (branchCode grade delta).length := by
      have length : (branchCode grade delta).length = 29 := rfl
      rw [length]
      omega
    have known := loaded ⟨25 + index.val, within⟩
    fin_cases index <;>
      simpa only [branchCode, code, prefixCode, List.range_succ, List.range_zero, List.map_append,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceAdd, Nat.reduceMul,
        BitVec.ofNat_toNat, BitVec.setWidth_eq] using known
  obtain ⟨middle, nextFlags, first, framed, remainingRead, gradeRead, flagsRead, carryRead, middleRip⟩ :=
    compare other extra vector state grade allowance receiptWord flags
      ⟨status, fault, mode, segments, application, quiet, controlKnown, flagsKnown,
        visibleKnown, rip, base, prefixLoaded, budget, receipt⟩
  tisa_sail_bytes [loaded]
  tisa_sail_inherit [framed]
  have deltaBytes : ∀ index : Fin 4, middle.mem.get? (4121 + index.val) =
      some (delta.extractLsb' (8 * index.val) 8) := by
    intro index
    rw [framed.memory _ (by simp)]
    exact encodedDelta index
  have last := X86EscapeFetch.fetched_branch (scalarHandlers other) extra vector .below middle
    (4119#48) (4120#48) (4121#48) (4125#48) (branchTarget delta) _ _ nextFlags delta
    (by decide) (by decide) (by decide) (branchTarget_exact delta)
    (by assumption) (by assumption) (by assumption) (by assumption) (by rfl) (by rfl)
    (by assumption) middleRip flagsRead (by assumption)
    (by assumption) (by assumption)
    (by
      intro index within
      interval_cases index
      · exact deltaBytes (0 : Fin 4)
      · exact deltaBytes (1 : Fin 4)
      · exact deltaBytes (2 : Fin 4)
      · exact deltaBytes (3 : Fin 4))
  have sense : X86BranchCondition.value .below nextFlags =
      decide ((allowance - receiptWord).toNat < grade.word.toNat) := by
    simp only [X86BranchCondition.value, carryRead]
    generalize allowance - receiptWord = remainingWord
    generalize grade.word = gradeWord
    by_cases below : remainingWord.toNat < gradeWord.toNat <;>
      simp [Functions.bool_to_bits, below]
  rw [sense] at last
  let destination : BitVec 48 :=
    if decide ((allowance - receiptWord).toNat < grade.word.toNat) then branchTarget delta else 4125#48
  have lastFrame := X86StateFrame.registerOnly (X86Execution.pointer_frame middle destination)
  refine ⟨X86Move.putPointer middle destination, nextFlags,
    X86FuelPrefix.fetches_then 4 1 state middle _ first
      (X86FuelPrefix.fetches_one middle _ last), ?_, ?_, ?_, ?_, carryRead, ?_⟩
  · apply (framed.trans lastFrame).mono
    · intro register member
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
    · simp
  · exact (lastFrame.registers .r14 (by decide)).trans remainingRead
  · exact (lastFrame.registers .r15 (by decide)).trans gradeRead
  · exact (lastFrame.registers .rflags (by decide)).trans flagsRead
  · simp only [X86Move.putPointer, Std.ExtDHashMap.get?_insert_self]
    change some (destination.signExtend 64) = some _
    simp only [Option.some.injEq]
    dsimp only [destination]
    generalize allowance - receiptWord = remainingWord
    generalize grade.word = gradeWord
    by_cases below : remainingWord.toNat < gradeWord.toNat <;> simp [below]



theorem forward_target : branchTarget (53#32) = (4178#48) := by decide
theorem backward_target : branchTarget (BitVec.ofInt 32 (-45)) = (4080#48) := by decide
theorem maximal_forward_target : (branchTarget (0x7fffffff#32)).toInt = 2147487772 := by decide
theorem minimal_backward_target : (branchTarget (0x80000000#32)).toInt = -2147479523 := by decide

private def receiptBytes : Finset Nat :=
  {1048744,1048745,1048746,1048747,1048748,1048749,1048750,1048751}

theorem paid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade)
    (allowance receiptWord following : Word) (flags : BitVec 32) {delta : BitVec 32}
    (payment : Funding.charge allowance receiptWord grade = .paid following)
    (input : Inputs state allowance receiptWord flags (completeCode grade delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14, .r15} receiptBytes state after ∧
      (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
        some (following.extractLsb' (8 * index.val) 8)) ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some (4132#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases input with ⟨status, fault, mode, segments, application, quiet, controlKnown,
    flagsKnown, visibleKnown, rip, base, loaded, budget, receipt⟩
  obtain ⟨fits, rfl⟩ := (Funding.paid_iff allowance receiptWord following grade).mp payment
  have valid : receiptWord.toNat ≤ allowance.toNat := by omega
  have enough : grade.word.toNat ≤ (allowance - receiptWord).toNat :=
    (Funding.available_sub_iff allowance receiptWord grade valid).mp
      ((Funding.available_iff allowance receiptWord grade).mpr fits)
  have branchLoaded : ∀ index : Fin (branchCode grade delta).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (branchCode grade delta)[index.val]) := by
    intro index
    have within : index.val < (completeCode grade delta).length := by
      simp only [completeCode, List.length_append]
      omega
    have known := loaded ⟨index.val, within⟩
    simpa only [completeCode, List.getElem_append_left index.isLt] using known
  obtain ⟨middle, middleFlags, first, framed, remainingRead, gradeRead, flagsRead, _, middleRip⟩ :=
    branch other extra vector state grade allowance receiptWord flags
      ⟨status, fault, mode, segments, application, quiet, controlKnown, flagsKnown,
        visibleKnown, rip, base, branchLoaded, budget, receipt⟩
  rw [if_neg (by omega)] at middleRip
  tisa_sail_bytes [loaded, receipt]
  have last : ∃ after nextFlags,
      (Functions.x86_fetch_decode_execute ()).run middle = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags} receiptBytes middle after ∧
      (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
        some ((receiptWord + grade.word).extractLsb' (8 * index.val) 8)) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .rip = some (4132#64) := by
    tisa_sail_inherit [framed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    tisa_sail_step
    · unfold receiptBytes
      tisa_sail_frame
    · have sumSlice (offset : Nat) (bounded : offset + 8 ≤ 64) :
          (Functions.bits_of_int
            (Sail.BitVec.toNatInt (X86ReadWords.assembled receiptWord) +
              Sail.BitVec.toNatInt grade.word) 65).extractLsb' offset 8 =
            (receiptWord + grade.word).extractLsb' offset 8 := by
        rw [X86ReadWords.assembled_exact]
        calc
          _ = (Sail.BitVec.truncate (Functions.bits_of_int
              (Sail.BitVec.toNatInt receiptWord + Sail.BitVec.toNatInt grade.word) 65) 64).extractLsb'
                offset 8 := (BitVec.extractLsb'_setWidth_of_le bounded).symm
          _ = _ := congrArg (fun value : Word => value.extractLsb' offset 8)
            (X86Alu.add_result receiptWord grade.word)
      have sumSliceNarrow (offset : Nat) :
          (Sail.BitVec.truncate (Functions.bits_of_int
            (Sail.BitVec.toNatInt (X86ReadWords.assembled receiptWord) +
              Sail.BitVec.toNatInt grade.word) 65) 64).extractLsb' offset 8 =
            (receiptWord + grade.word).extractLsb' offset 8 := by
        rw [X86ReadWords.assembled_exact]
        exact congrArg (fun value : Word => value.extractLsb' offset 8)
          (X86Alu.add_result receiptWord grade.word)
      intro index
      fin_cases index <;>
        simp [↓X86Symbolic.reduceClosedNat, Std.ExtHashMap.getElem_insert,
          Functions.regval_from_reg, Sail.BitVec.truncate, Sail.BitVec.zeroExtend,
          Sail.BitVec.extractLsb]
      all_goals first
        | apply sumSlice <;> decide
        | exact sumSliceNarrow _
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
  obtain ⟨after, nextFlags, finalStep, finalFrame, finalReceipt, finalFlags, finalRip⟩ := last
  refine ⟨after, nextFlags,
    X86FuelPrefix.fetches_then 5 1 state middle after first
      (X86FuelPrefix.fetches_one middle after finalStep),
    ?_, finalReceipt, ?_, ?_, finalFlags, finalRip⟩
  · apply (framed.trans finalFrame).mono
    · intro register member
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
    · simp
  · exact (finalFrame.registers .r14 (by decide)).trans remainingRead
  · exact (finalFrame.registers .r15 (by decide)).trans gradeRead

theorem exhausted (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade)
    (allowance receiptWord : Word) (flags : BitVec 32) {delta : BitVec 32}
    (payment : Funding.charge allowance receiptWord grade = .exhausted)
    (input : Inputs state allowance receiptWord flags (completeCode grade delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
      (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
        some (receiptWord.extractLsb' (8 * index.val) 8)) ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((branchTarget delta).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases input with ⟨status, fault, mode, segments, application, quiet, controlKnown,
    flagsKnown, visibleKnown, rip, base, loaded, budget, receipt⟩
  obtain ⟨valid, unpaid⟩ := (Funding.exhausted_iff allowance receiptWord grade).mp payment
  have below : (allowance - receiptWord).toNat < grade.word.toNat := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using valid), grade.word_toNat]
    omega
  have branchLoaded : ∀ index : Fin (branchCode grade delta).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (branchCode grade delta)[index.val]) := by
    intro index
    have within : index.val < (completeCode grade delta).length := by
      simp only [completeCode, List.length_append]
      omega
    have known := loaded ⟨index.val, within⟩
    simpa only [completeCode, List.getElem_append_left index.isLt] using known
  obtain ⟨after, nextFlags, executed, framed, remainingRead, gradeRead, flagsRead, _, finalRip⟩ :=
    branch other extra vector state grade allowance receiptWord flags
      ⟨status, fault, mode, segments, application, quiet, controlKnown, flagsKnown,
        visibleKnown, rip, base, branchLoaded, budget, receipt⟩
  refine ⟨after, nextFlags, executed, framed, ?_, remainingRead, gradeRead, flagsRead, ?_⟩
  · intro index
    rw [framed.memory _ (by simp)]
    exact receipt index
  · simpa only [if_pos below] using finalRip

theorem realizes_charge (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade)
    (allowance receiptWord : Word) (flags : BitVec 32) {delta : BitVec 32}
    (valid : receiptWord.toNat ≤ allowance.toNat)
    (input : Inputs state allowance receiptWord flags (completeCode grade delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      match Funding.charge allowance receiptWord grade with
      | .invalidReceipt => False
      | .exhausted => (X86FuelPrefix.fetches 5).run state = .ok () after ∧
          X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
          (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
            some (receiptWord.extractLsb' (8 * index.val) 8)) ∧
          after.regs.get? .rip = some ((branchTarget delta).signExtend 64)
      | .paid following => (X86FuelPrefix.fetches 6).run state = .ok () after ∧
          X86StateFrame.Frame {.rip, .rflags, .r14, .r15} receiptBytes state after ∧
          (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
            some (following.extractLsb' (8 * index.val) 8)) ∧
          after.regs.get? .rip = some (4132#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases input with ⟨status, fault, mode, segments, application, quiet, controlKnown,
    flagsKnown, visibleKnown, rip, base, loaded, budget, receipt⟩
  cases payment : Funding.charge allowance receiptWord grade with
  | invalidReceipt =>
      have invalid := (Funding.invalid_iff allowance receiptWord grade).mp payment
      omega
  | exhausted =>
      obtain ⟨after, nextFlags, executed, framed, bytes, remainingRead, gradeRead, flagsRead, finalRip⟩ :=
        exhausted other extra vector state grade allowance receiptWord flags payment
          ⟨status, fault, mode, segments, application, quiet, controlKnown, flagsKnown,
            visibleKnown, rip, base, loaded, budget, receipt⟩
      exact ⟨after, nextFlags, remainingRead, gradeRead, flagsRead, executed, framed, bytes, finalRip⟩
  | paid following =>
      obtain ⟨after, nextFlags, executed, framed, bytes, remainingRead, gradeRead, flagsRead, finalRip⟩ :=
        paid other extra vector state grade allowance receiptWord following flags payment
          ⟨status, fault, mode, segments, application, quiet, controlKnown, flagsKnown,
            visibleKnown, rip, base, loaded, budget, receipt⟩
      exact ⟨after, nextFlags, remainingRead, gradeRead, flagsRead, executed, framed, bytes, finalRip⟩

private def three : Funding.Grade := ⟨3#32, by decide⟩

theorem paid_wrong_target (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (grade : Funding.Grade)
    (allowance receiptWord following : Word) (flags : BitVec 32) {delta : BitVec 32}
    (payment : Funding.charge allowance receiptWord grade = .paid following)
    (input : Inputs state allowance receiptWord flags (completeCode grade delta)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      after.regs.get? .rip = some (4178#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨computed, _, executed, _, _, _, _, _, properRip⟩ :=
    paid other extra vector state grade allowance receiptWord following flags payment input
  rintro ⟨after, forged, wrong⟩
  have same := X86FuelPrefix.fetches_deterministic 6 state computed after executed forged
  rw [same, wrong] at properRip
  exact (by decide : (4178#64) ≠ (4132#64)) (Option.some.inj properRip)

theorem exhausted_no_early_payment (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (flags : BitVec 32)
    (input : Inputs state (9#64) (7#64) flags (completeCode three)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      after.mem.get? 1048744 = some (10#8) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have refused : Funding.charge (9#64) (7#64) three = .exhausted := by decide
  obtain ⟨computed, _, executed, _, bytes, _, _, _, _⟩ :=
    exhausted other extra vector state three (9#64) (7#64) flags refused input
  rintro ⟨after, forged, wrong⟩
  have same := X86FuelPrefix.fetches_deterministic 5 state computed after executed forged
  have low := bytes (0 : Fin 8)
  change computed.mem.get? 1048744 = some (7#8) at low
  rw [same, wrong] at low
  exact (by decide : (10#8) ≠ (7#8)) (Option.some.inj low)

private def sampleState (allowance : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (2#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .rip (4096#64)
  let registers := registers.insert .rdi (1048576#64)
  let memory := (List.range (completeCode three).length).foldl
    (fun memory index => memory.insert (4096 + index) (BitVec.ofNat 8 (completeCode three)[index]!))
    (∅ : Std.ExtHashMap Nat (BitVec 8))
  let memory := (List.range 8).foldl
    (fun memory index => memory.insert (1048736 + index) (allowance.extractLsb' (8 * index) 8)) memory
  let memory := (List.range 8).foldl
    (fun memory index => memory.insert (1048744 + index) ((7#64).extractLsb' (8 * index) 8)) memory
  ⟨registers, (), memory, (), 0, #[]⟩

theorem sample_input (allowance : Word) :
    Inputs (sampleState allowance) allowance (7#64) (2#32) (completeCode three) := by
  constructor
  case loaded =>
    intro index
    fin_cases index <;>
      simp [sampleState, completeCode, branchCode, code, prefixCode, three,
        List.range_succ, Std.ExtHashMap.getElem_insert]
  case budget =>
    intro index
    fin_cases index <;>
      simp [sampleState, completeCode, branchCode, code, prefixCode, three,
        List.range_succ, Std.ExtHashMap.getElem_insert]
  case receipt =>
    intro index
    fin_cases index <;>
      simp [sampleState, completeCode, branchCode, code, prefixCode, three,
        List.range_succ, Std.ExtHashMap.getElem_insert]
  all_goals simp [sampleState, Std.ExtDHashMap.get?_insert]

theorem sample_paid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run (sampleState (10#64)) = .ok () after ∧
      after.mem.get? 1048744 = some (10#8) ∧ after.regs.get? .rip = some (4132#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have payment : Funding.charge (10#64) (7#64) three = .paid (10#64) := by decide
  obtain ⟨after, _, executed, _, bytes, _, _, _, finalRip⟩ :=
    paid other extra vector (sampleState (10#64)) three (10#64) (7#64) (10#64) (2#32)
      payment (sample_input (10#64))
  exact ⟨after, executed, bytes (0 : Fin 8), finalRip⟩

theorem sample_exhaustion_refuses_payment (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 5).run (sampleState (9#64)) = .ok () after ∧
      after.mem.get? 1048744 = some (10#8) :=
  exhausted_no_early_payment other extra vector (sampleState (9#64)) (2#32) (sample_input (9#64))

end Mettapedia.Machines.TIsa.X86Funding.Controls
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.compare
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.branch
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.paid
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.exhausted
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.realizes_charge
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.paid_wrong_target
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.exhausted_no_early_payment
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_input
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_paid
#print axioms Mettapedia.Machines.TIsa.X86Funding.Controls.sample_exhaustion_refuses_payment

namespace Mettapedia.Machines.TIsa.X86Funding.Capture

open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable def captured : List Nat × List NativeImage.TemplateSample :=
  tisa_template_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/FundHelper.json"

noncomputable def block : List Nat :=
  ((captured.2[0]?).map NativeImage.TemplateSample.bytes).getD []

noncomputable def image : List Nat :=
  ((captured.2[1]?).map NativeImage.TemplateSample.bytes).getD []

def sampleCheck (sample : NativeImage.TemplateSample) : Bool :=
  sample.inputs == [3, 9, 91] && sample.bytes == Placed.completeCode Controls.three &&
    sample.spans == [⟨0, 36, "FUND"⟩] && sample.scratchMask == 12288

theorem register_map_exact : captured.1 = (Registers.canonical .x86_64).registers := by
  kernel_reflexivity

theorem inventory_exact : captured.2.map NativeImage.TemplateSample.inputs =
    [[3, 9, 91], [192, 160, 168, 144, 152]] := by kernel_reflexivity

theorem captured_block_checked : (captured.2.take 1).all sampleCheck = true := by
  kernel_reflexivity

theorem block_exact : block = Placed.completeCode Controls.three := by kernel_reflexivity
theorem block_length : block.length = 36 := by kernel_reflexivity
theorem image_length : image.length = 120 := by kernel_reflexivity
theorem image_slice : (image.drop 9).take 36 = block := by kernel_reflexivity

theorem image_byte (index : Fin block.length) :
    image[index.val + 9]? = some block[index.val] := by
  revert index
  decide

theorem changed_branch_refused :
    sampleCheck ⟨[3, 9, 91], (Placed.completeCode Controls.three).set 24 131,
      [⟨0, 36, "FUND"⟩], 12288⟩ = false := by decide

theorem window_from_image (state : State) (loaded : X86Execution.codeLoaded state 4087 image) :
    ∀ index : Fin block.length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 block[index.val]) := by
  intro index
  have known := loaded (index.val + 9) block[index.val] (image_byte index)
  fin_cases index <;> exact known

theorem realizes_charge (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (allowance receiptWord : Word) (flags : BitVec 32)
    (valid : receiptWord.toNat ≤ allowance.toNat)
    (input : Controls.Inputs state allowance receiptWord flags block) :
    letI : OtherOpcodeHandlers := Controls.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some Controls.three.word ∧ after.regs.get? .rflags = some nextFlags ∧
      match Funding.charge allowance receiptWord Controls.three with
      | .invalidReceipt => False
      | .exhausted => (X86FuelPrefix.fetches 5).run state = .ok () after ∧
          X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
          (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
            some (receiptWord.extractLsb' (8 * index.val) 8)) ∧
          after.regs.get? .rip = some (4178#64)
      | .paid following => (X86FuelPrefix.fetches 6).run state = .ok () after ∧
          X86StateFrame.Frame {.rip, .rflags, .r14, .r15} Controls.receiptBytes state after ∧
          (∀ index : Fin 8, after.mem.get? (1048744 + index.val) =
            some (following.extractLsb' (8 * index.val) 8)) ∧
          after.regs.get? .rip = some (4132#64) := by
  apply Controls.realizes_charge other extra vector state Controls.three allowance receiptWord flags (delta := 53#32) valid
  simpa only [block_exact] using input

end Mettapedia.Machines.TIsa.X86Funding.Capture

#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.captured_block_checked
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.changed_branch_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.window_from_image
#print axioms Mettapedia.Machines.TIsa.X86Funding.Capture.realizes_charge

namespace Mettapedia.Machines.TIsa.X86Funding.Placed

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def calibrationBasis (state : State) (grade : Funding.Grade) (delta : BitVec 32)
    (allowance receipt : Word) (flags : BitVec 32)
    (input : Controls.Inputs state allowance receipt flags (completeCode grade delta)) :
    X86LegacyFetch.Basis state where
  address := 4096#48
  opcodeAddress := 4097#48
  modrmAddress := 4098#48
  next := 4099#48
  control := Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
  attributes := Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := input.status
  fault := input.fault
  msrs := input.mode
  segments := input.segments
  longMode := by decide
  codeMode := by decide
  application := input.application
  rip := input.rip

def calibrationInput (state : State) (grade : Funding.Grade) (delta : BitVec 32)
    (allowance receipt : Word) (flags : BitVec 32)
    (input : Controls.Inputs state allowance receipt flags (completeCode grade delta)) :
    Inputs state (calibrationBasis state grade delta allowance receipt flags input)
      grade delta allowance receipt where
  upper := by change (4096#48).toInt + 36 < (2 ^ 47 : Int); decide
  frame := 1048576#64
  budgetAddress := 1048736#48
  receiptAddress := 1048744#48
  budgetUpper := by decide
  receiptUpper := by decide
  base := by change (state.regs.get? .rdi).map (fun value : Word => value) = _; rw [input.base]; rfl
  budgetEffective := by decide
  receiptEffective := by decide
  budgetAligned := by decide
  receiptAligned := by decide
  controls := Vector.replicate 17 (0#64)
  visible := Vector.replicate 6 (0#16)
  flags := flags
  controlKnown := input.controlKnown
  visibleKnown := input.visibleKnown
  flagsKnown := input.flagsKnown
  quiet := input.quiet
  loaded := by
    intro index byte present
    obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
    have length : (completeCode grade delta).length = 36 := by rfl
    have bound : index < 36 := by omega
    have known := input.loaded ⟨index, within⟩
    rw [same] at known
    have place : ((address (4096#48).toInt index).signExtend 52).toNat = 4096 + index := by
      interval_cases index <;> rfl
    change state.mem.get? ((address (4096#48).toInt index).signExtend 52).toNat = _
    rw [place]
    exact known
  budget := by
    intro index within
    have known := input.budget ⟨index, within⟩
    interval_cases index <;> exact known
  receipt := by
    intro index within
    have known := input.receipt ⟨index, within⟩
    interval_cases index <;> exact known
  outsideCode := by
    intro index byte present
    have within : index < 36 := by
      have bound := (List.getElem?_eq_some_iff.mp present).choose
      have length : (completeCode grade delta).length = 36 := by rfl
      omega
    change ((address (4096#48).toInt index).signExtend 52).toNat ∉
      X86WriteWords.written (1048744#48) (List.range 8)
    interval_cases index <;> decide

namespace Controls

private def three : Funding.Grade := ⟨3#32, by decide⟩

theorem inputs_inhabited (allowance : Word) :
    ∃ state, ∃ origin : X86LegacyFetch.Basis state,
      Nonempty (Inputs state origin three (53#32) allowance (7#64)) := by
  have original : ∃ state, X86Funding.Controls.Inputs state allowance (7#64) (2#32)
      (completeCode three (53#32)) := ⟨_, X86Funding.Controls.sample_input allowance⟩
  obtain ⟨state, input⟩ := original
  exact ⟨state, calibrationBasis state three (53#32) allowance (7#64) (2#32) input,
    ⟨calibrationInput state three (53#32) allowance (7#64) (2#32) input⟩⟩

theorem paid_wrong_target (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt)
    (fits : receipt.toNat + grade.units.toNat ≤ allowance.toNat)
    (badPointer : Word) (wrong : badPointer ≠ (position origin.address 36).signExtend 64) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      after.regs.get? .rip = some badPointer := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, _, executed, _, _, _, _, _, _, finalRip⟩ :=
    paid other extra vector state origin grade delta allowance receipt input target jump fits
  rintro ⟨after, otherRun, badRip⟩
  have same := X86FuelPrefix.fetches_deterministic 6 state actual after executed otherRun
  rw [← same] at badRip
  exact wrong (Option.some.inj (finalRip.symm.trans badRip)).symm

theorem exhausted_wrong_byte (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (grade : Funding.Grade) (delta : BitVec 32) (allowance receipt : Word)
    (input : Inputs state origin grade delta allowance receipt) (target : BitVec 48)
    (jump : target.toInt = (position origin.address 29).toInt + delta.toInt)
    (valid : receipt.toNat ≤ allowance.toNat)
    (short : allowance.toNat < receipt.toNat + grade.units.toNat)
    (address : Nat) (byte : BitVec 8) (wrong : state.mem.get? address ≠ some byte) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 5).run state = .ok () after ∧
      after.mem.get? address = some byte := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, _, executed, framed, _, _, _, _, _, _⟩ :=
    exhausted other extra vector state origin grade delta allowance receipt input target jump valid short
  rintro ⟨after, otherRun, badByte⟩
  have same := X86FuelPrefix.fetches_deterministic 5 state actual after executed otherRun
  rw [← same, framed.memory] at badByte
  exact wrong badByte

end Controls

theorem captured_block_exact : X86Funding.Capture.block = completeCode ⟨3#32, by decide⟩ (53#32) := by
  kernel_reflexivity

theorem captured_window (state : State) (base : Int)
    (loaded : codeLoaded state base X86Funding.Capture.image) :
    codeLoaded state (base + 9) (completeCode ⟨3#32, by decide⟩ (53#32)) := by
  rw [← captured_block_exact]
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := X86Funding.Capture.image_byte ⟨index, within⟩
  rw [same] at imageByte
  have known := loaded (index + 9) byte imageByte
  have position : address (base + 9) index = address base (index + 9) := by
    unfold address
    congr 1
    push_cast
    omega
  rw [position]
  exact known

end Mettapedia.Machines.TIsa.X86Funding.Placed

#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.fetched_subtract
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.subtract_frame
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.add_handler
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.add_frame
#print axioms Mettapedia.Machines.TIsa.X86Funding.GenericMemory.fetched_add
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.position_exact
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.loaded_grade
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.grade_step
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.load_step
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.subtract_step
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.remaining_prefix
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.compare_step
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.compare_executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.branch_executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.payment_step
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.paid
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.exhausted
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.realizes_charge
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.calibrationInput
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.inputs_inhabited
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.paid_wrong_target
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.Controls.exhausted_wrong_byte
#print axioms Mettapedia.Machines.TIsa.X86Funding.Placed.captured_window

namespace Mettapedia.Machines.TIsa.X86Funding.Exhaustion
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev pathExpected : List Nat := X86FailureHandler.RegisterPath.expected (4#32)

theorem captured_slice : (Capture.image.drop 91).take 19 = pathExpected := by kernel_reflexivity

theorem captured_byte (index : Fin pathExpected.length) :
    Capture.image[index.val + 91]? = some pathExpected[index.val] := by
  revert index
  decide

theorem captured_window (state : State) (base : Int) (loaded : codeLoaded state base Capture.image) :
    codeLoaded state (base + 91) pathExpected := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := captured_byte ⟨index, within⟩
  rw [same] at imageByte
  have known := loaded (index + 91) byte imageByte
  have place : address (base + 91) index = address base (index + 91) := by
    unfold address
    congr 1
    push_cast
    omega
  rw [place]
  exact known

private def grade : Funding.Grade := ⟨3#32, by decide⟩

def writes {state : State} (facts : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written facts.statusAddress (List.range 8) ∪
    X86WriteWords.written facts.resultAddress (List.range 8)

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (allowance receipt : Word) (input : Placed.Inputs state origin grade (53#32) allowance receipt)
    (facts : X86FailureHandler.FrameFacts state) (base : Int)
    (start : origin.address.toInt = base + 9)
    (upper : base + 120 < (2 ^ 47 : Int))
    (loaded : codeLoaded state base Capture.image)
    (outsideImage : ∀ index byte, Capture.image[index]? = some byte →
      ((address base index).signExtend 52).toNat ∉ writes facts)
    (receiptOutside : ∀ index < 8,
      X86WriteWords.physicalAddress input.receiptAddress index ∉ writes facts)
    (valid : receipt.toNat ≤ allowance.toNat)
    (short : allowance.toNat < receipt.toNat + 3) :
    letI : OtherOpcodeHandlers := Placed.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 8).run state = .ok () after ∧
      X86StateFrame.Frame {.rax, .r14, .r15, .rflags, .rip} (writes facts) state after ∧
      codeLoaded after base Capture.image ∧ lookup after 0 = some (4#64) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress index) =
        some ((4#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress index) =
        some ((4#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some (receipt.extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((address base 110).signExtend 64) := by
  let : OtherOpcodeHandlers := Placed.handlers other extra
  let : VectorOpcodeHandlers := vector
  have regionUpper : origin.address.toInt + 111 < (2 ^ 47 : Int) := by omega
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let target := address origin.address.toInt 82
  have targetInt : target.toInt = origin.address.toInt + 82 :=
    address_toInt _ lower regionUpper 82 (by decide)
  have jump : target.toInt = (Placed.position origin.address 29).toInt + (53#32).toInt := by
    rw [targetInt, Placed.position_exact _ input.upper 29 (by decide)]
    change origin.address.toInt + 82 = origin.address.toInt + 29 + 53
    omega
  obtain ⟨middle, flags, first, framed, _, _, _, _, flagsRead, middleRip⟩ :=
    Placed.exhausted other extra vector state origin grade (53#32) allowance receipt input target jump
      valid (by simpa only [grade, BitVec.toNat_ofNat] using short)
  let site := rebase state middle origin (framed.mono Placed.writes_data)
    regionUpper 82 (by decide) middleRip
  have siteInt : site.address.toInt = base + 91 := by
    change target.toInt = base + 91
    rw [targetInt, start]
    omega
  have addressHere (index : Nat) : address site.address.toInt index = address base (index + 91) := by
    rw [siteInt]
    unfold address
    congr 1
    push_cast
    omega
  let changed : X86FailureHandler.FrameFacts middle := {
    frame := facts.frame
    statusAddress := facts.statusAddress
    resultAddress := facts.resultAddress
    statusUpper := facts.statusUpper
    resultUpper := facts.resultUpper
    statusEffective := facts.statusEffective
    resultEffective := facts.resultEffective
    statusAligned := facts.statusAligned
    resultAligned := facts.resultAligned
    visible := facts.visible
    controls := facts.controls
    flags := flags
    frameKnown := ((X86StateFrame.registerOnly framed).lookup 7 (by decide)).trans facts.frameKnown
    controlsKnown := (framed.registers .ctrs (by decide)).trans facts.controlsKnown
    visibleKnown := (framed.registers .seg_visibles (by decide)).trans facts.visibleKnown
    flagsKnown := flagsRead
    quiet := (framed.registers .log_register_writes (by decide)).trans facts.quiet
    statusOutside := facts.statusOutside }
  have currentCode := framed.code_preserved base _ loaded
  let prepared : X86FailureHandler.RegisterPath.Inputs middle (4#32) := {
    toBasis := site
    toFrameFacts := changed
    upper := by rw [siteInt]; omega
    loaded := by change codeLoaded middle site.address.toInt pathExpected; rw [siteInt]; exact captured_window _ _ currentCode
    codeOutside := by
      intro index byte present
      obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
      have imageByte := captured_byte ⟨index, within⟩
      rw [same] at imageByte
      change ((address site.address.toInt index).signExtend 52).toNat ∉ writes facts
      rw [addressHere]
      exact outsideImage _ _ imageByte }
  let after := X86FailureHandler.RegisterPath.finished middle prepared
  have last := X86FailureHandler.RegisterPath.executes (Placed.handlers other extra) vector middle (4#32) prepared
  have correct := X86FailureHandler.RegisterPath.finished_result middle (4#32) prepared
  have wholeFrame : X86StateFrame.Frame {.rax, .r14, .r15, .rflags, .rip} (writes facts) state after :=
    ((X86StateFrame.registerOnly framed).trans correct.frame).mono (by decide) (by simp [X86FailureHandler.RegisterPath.writes, writes, prepared, changed])
  refine ⟨after, flags, X86FuelPrefix.fetches_then 5 3 state middle after first last, wholeFrame,
    wholeFrame.codeLoaded base _ loaded outsideImage, correct.rax, correct.status, correct.result,
    ?_, correct.flags, ?_⟩
  · intro index within
    rw [correct.frame.memory _ (receiptOutside index within), framed.memory]
    exact input.receipt index within
  · have pointer := correct.pointer
    change after.regs.get? .rip = some ((address site.address.toInt 19).signExtend 64) at pointer
    rw [addressHere 19] at pointer
    exact pointer

namespace Controls

private def overlay (memory : Std.ExtHashMap Nat (BitVec 8)) (base count : Nat) (value : Nat → BitVec 8) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (List.range count).foldl (fun memory index => memory.insert (base + index) (value index)) memory

private theorem overlay_inside (memory : Std.ExtHashMap Nat (BitVec 8)) (base count : Nat)
    (value : Nat → BitVec 8) (index : Nat) (within : index < count) :
    (overlay memory base count value).get? (base + index) = some (value index) := by
  induction count with
  | zero => omega
  | succ count induction =>
      simp only [overlay, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases last : index = count
      · subst index
        simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert_self]
      · have earlier : index < count := by omega
        have apart : base + index ≠ base + count := by omega
        simpa only [overlay, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
          beq_iff_eq, if_neg apart, if_neg (Ne.symm apart)] using induction earlier

private theorem overlay_outside (memory : Std.ExtHashMap Nat (BitVec 8)) (base count : Nat)
    (value : Nat → BitVec 8) (key : Nat) (outside : key < base ∨ base + count ≤ key) :
    (overlay memory base count value).get? key = memory.get? key := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [overlay, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have apart : key ≠ base + count := by omega
      simpa only [overlay, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
        beq_iff_eq, if_neg apart, if_neg (Ne.symm apart)] using induction (by omega)

private noncomputable def sampleState : State :=
  let regs := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let regs := regs.insert .fault_reg false
  let regs := regs.insert .msrs (Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64)))
  let regs := regs.insert .seg_hidden_attrs (Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16)))
  let regs := regs.insert .app_view true
  let regs := regs.insert .log_register_writes false
  let regs := regs.insert .ctrs (Vector.replicate 17 (0#64))
  let regs := regs.insert .seg_visibles (Vector.replicate 6 (0#16))
  let regs := regs.insert .rflags (2#32)
  let regs := regs.insert .rip (4096#64)
  let regs := regs.insert .rdi (1048576#64)
  let mem := overlay ∅ 4087 Capture.image.length (fun index => BitVec.ofNat 8 Capture.image[index]!)
  let mem := overlay mem 1048736 8 (fun index => (9#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048744 8 (fun index => (7#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048720 8 (fun index => (99#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048728 8 (fun index => (77#64).extractLsb' (8 * index) 8)
  ⟨regs, (), mem, (), 0, #[]⟩

theorem sample_code : ∀ index : Fin Capture.image.length,
    sampleState.mem.get? (4087 + index.val) = some (BitVec.ofNat 8 Capture.image[index.val]) := by
  intro index
  have bound : index.val < 120 := by simpa only [Capture.image_length] using index.isLt
  simp only [sampleState]
  rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
    overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
    overlay_inside _ _ _ _ _ index.isLt]
  rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem index.isLt)]

theorem sample_controls : X86Funding.Controls.Inputs sampleState (9#64) (7#64) (2#32)
    (Placed.completeCode grade (53#32)) := by
  constructor
  case loaded =>
    intro index
    have full : codeLoaded sampleState 4087 Capture.image := by
      intro offset byte present
      obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
      have bounded : offset < 120 := by simpa only [Capture.image_length] using within
      have place : ((address 4087 offset).signExtend 52).toNat = 4087 + offset := by
        interval_cases offset <;> rfl
      rw [place]
      simpa only [same] using sample_code ⟨offset, within⟩
    have body := Placed.captured_window sampleState 4087 full index.val _ (List.getElem?_eq_getElem index.isLt)
    have within : index.val < 36 := by exact index.isLt
    have place (offset : Nat) (bounded : offset < 36) :
        ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
      interval_cases offset <;> rfl
    change sampleState.mem.get? ((address 4096 index.val).signExtend 52).toNat = _ at body
    rw [place index.val within] at body
    exact body
  case budget =>
    intro index
    simp only [sampleState]
    rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
      overlay_outside _ _ _ _ _ (by omega), overlay_inside _ _ _ _ _ index.isLt]
  case receipt =>
    intro index
    simp only [sampleState]
    rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
      overlay_inside _ _ _ _ _ index.isLt]
  all_goals simp [sampleState, Std.ExtDHashMap.get?_insert]
  all_goals rfl

private noncomputable def sampleOrigin : X86LegacyFetch.Basis sampleState :=
  Placed.calibrationBasis sampleState grade (53#32) (9#64) (7#64) (2#32) sample_controls

private noncomputable def sampleFund : Placed.Inputs sampleState sampleOrigin grade (53#32) (9#64) (7#64) :=
  Placed.calibrationInput sampleState grade (53#32) (9#64) (7#64) (2#32) sample_controls

private def sampleFacts : X86FailureHandler.FrameFacts sampleState where
  frame := 1048576#64
  statusAddress := 1048720#48
  resultAddress := 1048728#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := Vector.replicate 6 (0#16)
  controls := Vector.replicate 17 (0#64)
  flags := 2#32
  frameKnown := by
    change (sampleState.regs.get? .rdi).map (fun value : Word => value) = _
    rw [sample_controls.base]
    rfl
  controlsKnown := sample_controls.controlKnown
  visibleKnown := sample_controls.visibleKnown
  flagsKnown := sample_controls.flagsKnown
  quiet := sample_controls.quiet
  statusOutside := by intro index within; interval_cases index <;> decide

theorem sample_image : codeLoaded sampleState 4087 Capture.image := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have bounded : index < 120 := by simpa only [Capture.image_length] using within
  have place : ((address 4087 index).signExtend 52).toNat = 4087 + index := by
    interval_cases index <;> rfl
  rw [place]
  simpa only [same] using sample_code ⟨index, within⟩

theorem sample_reaches_epilogue (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := Placed.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 8).run sampleState = .ok () after ∧
      after.regs.get? .rip = some (4197#64) ∧
      after.mem.get? 1048720 = some (4#8) ∧ after.mem.get? 1048728 = some (4#8) ∧
      after.mem.get? 1048744 = some (7#8) := by
  let : OtherOpcodeHandlers := Placed.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, _, run, _, _, _, statusBytes, resultBytes, receiptBytes, _, pointer⟩ :=
    Exhaustion.executes other extra vector sampleState sampleOrigin (9#64) (7#64) sampleFund sampleFacts 4087
      (by rfl) (by decide) sample_image
      (by
        intro index byte present
        have within : index < 120 := by
          have bound := (List.getElem?_eq_some_iff.mp present).choose
          simpa only [Capture.image_length] using bound
        change ((address 4087 index).signExtend 52).toNat ∉
          X86WriteWords.written (1048720#48) (List.range 8) ∪
            X86WriteWords.written (1048728#48) (List.range 8)
        interval_cases index <;> decide)
      (by
        intro index within
        change X86WriteWords.physicalAddress (1048744#48) index ∉
          X86WriteWords.written (1048720#48) (List.range 8) ∪
            X86WriteWords.written (1048728#48) (List.range 8)
        interval_cases index <;> decide)
      (by decide) (by decide)
  exact ⟨after, run, pointer, statusBytes 0 (by decide), resultBytes 0 (by decide), receiptBytes 0 (by decide)⟩

theorem stale_result_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := Placed.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 8).run sampleState = .ok () after ∧
      after.mem.get? 1048728 = some (77#8) := by
  let : OtherOpcodeHandlers := Placed.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, run, _, _, returned, _⟩ := sample_reaches_epilogue other extra vector
  rintro ⟨after, otherRun, stale⟩
  have same := X86FuelPrefix.fetches_deterministic 8 sampleState actual after run otherRun
  rw [← same] at stale
  exact (by decide : some (4#8) ≠ some (77#8)) (returned.symm.trans stale)

theorem early_receipt_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := Placed.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 8).run sampleState = .ok () after ∧
      after.mem.get? 1048744 = some (10#8) := by
  let : OtherOpcodeHandlers := Placed.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, run, _, _, _, receipt⟩ := sample_reaches_epilogue other extra vector
  rintro ⟨after, otherRun, early⟩
  have same := X86FuelPrefix.fetches_deterministic 8 sampleState actual after run otherRun
  rw [← same] at early
  exact (by decide : some (7#8) ≠ some (10#8)) (receipt.symm.trans early)

end Controls

end Mettapedia.Machines.TIsa.X86Funding.Exhaustion

#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.captured_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_code
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_controls
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.sample_reaches_epilogue
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.stale_result_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Exhaustion.Controls.early_receipt_refused

namespace Mettapedia.Machines.TIsa.X86Funding.Return
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev pathExpected : List Nat := X86ReturnPath.expected 6 (39#32)

theorem captured_slice : (Capture.image.drop 45).take 26 = pathExpected := by kernel_reflexivity

theorem captured_byte (index : Fin pathExpected.length) :
    Capture.image[index.val + 45]? = some pathExpected[index.val] := by
  revert index
  decide

theorem captured_window (state : State) (base : Int) (loaded : codeLoaded state base Capture.image) :
    codeLoaded state (base + 45) pathExpected := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := captured_byte ⟨index, within⟩
  rw [same] at imageByte
  have known := loaded (index + 45) byte imageByte
  have place : address (base + 45) index = address base (index + 45) := by
    unfold address
    congr 1
    push_cast
    omega
  rw [place]
  exact known

private def grade : Funding.Grade := ⟨3#32, by decide⟩

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  Placed.handlers (X86ReturnPath.linkedHandlers other) extra

def writes {state : State} (facts : X86FailureHandler.FrameFacts state) : Finset Nat :=
  X86WriteWords.written facts.statusAddress (List.range 8) ∪
    X86WriteWords.written facts.resultAddress (List.range 8)

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (allowance receipt value : Word) (input : Placed.Inputs state origin grade (53#32) allowance receipt)
    (facts : X86FailureHandler.FrameFacts state) (base : Int)
    (start : origin.address.toInt = base + 9) (upper : base + 120 < (2 ^ 47 : Int))
    (loaded : codeLoaded state base Capture.image) (sourceKnown : lookup state 6 = some value)
    (outsideFund : ∀ index byte, Capture.image[index]? = some byte →
      ((address base index).signExtend 52).toNat ∉ X86WriteWords.written input.receiptAddress (List.range 8))
    (outsideReturn : ∀ index byte, Capture.image[index]? = some byte →
      ((address base index).signExtend 52).toNat ∉ writes facts)
    (receiptOutside : ∀ index < 8,
      X86WriteWords.physicalAddress input.receiptAddress index ∉ writes facts)
    (fits : receipt.toNat + 3 ≤ allowance.toNat) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 10).run state = .ok () after ∧
      X86StateFrame.Frame {.rax, .r14, .r15, .rflags, .rip}
        (X86WriteWords.written input.receiptAddress (List.range 8) ∪ writes facts) state after ∧
      codeLoaded after base Capture.image ∧ lookup after 0 = some value ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.statusAddress index) =
        some ((1#64).extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress facts.resultAddress index) =
        some (value.extractLsb' (8 * index) 8)) ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress input.receiptAddress index) =
        some ((receipt + grade.word).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((address base 110).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have regionUpper : origin.address.toInt + 111 < (2 ^ 47 : Int) := by omega
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  let failed := address origin.address.toInt 82
  have failedInt : failed.toInt = origin.address.toInt + 82 := address_toInt _ lower regionUpper 82 (by decide)
  have jumpFund : failed.toInt = (Placed.position origin.address 29).toInt + (53#32).toInt := by
    rw [failedInt, Placed.position_exact _ input.upper 29 (by decide)]
    change origin.address.toInt + 82 = origin.address.toInt + 29 + 53
    omega
  obtain ⟨middle, flags, first, framed, _, receiptRead, _, _, flagsRead, middleRip⟩ :=
    Placed.paid (X86ReturnPath.linkedHandlers other) extra vector state origin grade (53#32) allowance receipt
      input failed jumpFund (by simpa only [grade, BitVec.toNat_ofNat] using fits)
  let site := X86StateFrame.rebase state middle origin framed Placed.writes_data
    regionUpper 36 (by decide) middleRip
  have siteInt : site.address.toInt = base + 45 := by
    change (address origin.address.toInt 36).toInt = base + 45
    rw [address_toInt _ lower regionUpper 36 (by decide), start]
    omega
  let epilogue := address origin.address.toInt 101
  have epilogueInt : epilogue.toInt = origin.address.toInt + 101 :=
    address_toInt _ lower regionUpper 101 (by decide)
  have epilogueEq : epilogue = address base 110 := by
    unfold epilogue address
    rw [start]
    congr 1
    omega
  have addressHere (index : Nat) : address site.address.toInt index = address base (index + 45) := by
    rw [siteInt]
    unfold address
    congr 1
    push_cast
    omega
  let changed : X86FailureHandler.FrameFacts middle := {
    frame := facts.frame
    statusAddress := facts.statusAddress
    resultAddress := facts.resultAddress
    statusUpper := facts.statusUpper
    resultUpper := facts.resultUpper
    statusEffective := facts.statusEffective
    resultEffective := facts.resultEffective
    statusAligned := facts.statusAligned
    resultAligned := facts.resultAligned
    visible := facts.visible
    controls := facts.controls
    flags := flags
    frameKnown := (framed.lookup 7 (by decide)).trans facts.frameKnown
    controlsKnown := (framed.registers .ctrs (by decide)).trans facts.controlsKnown
    visibleKnown := (framed.registers .seg_visibles (by decide)).trans facts.visibleKnown
    flagsKnown := flagsRead
    quiet := (framed.registers .log_register_writes (by decide)).trans facts.quiet
    statusOutside := facts.statusOutside }
  have currentCode := framed.codeLoaded base _ loaded outsideFund
  let prepared : X86ReturnPath.Inputs middle 6 value := {
    toBasis := site
    toFrameFacts := changed
    sourceKnown := (framed.lookup 6 (by decide)).trans sourceKnown
    displacement := 39#32
    epilogue := epilogue
    upper := by rw [siteInt]; omega
    jump := by rw [epilogueInt, siteInt, start]; change base + 9 + 101 = base + 45 + 26 + 39; omega
    loaded := by change codeLoaded middle site.address.toInt pathExpected; rw [siteInt]; exact captured_window _ _ currentCode
    codeOutside := by
      intro index byte present
      obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
      have imageByte := captured_byte ⟨index, within⟩
      rw [same] at imageByte
      change ((address site.address.toInt index).signExtend 52).toNat ∉ writes facts
      rw [addressHere]
      exact outsideReturn _ _ imageByte }
  let after := X86ReturnPath.finished middle prepared
  have last := X86ReturnPath.executes (handlers other extra) vector middle 6 value prepared
  have correct := X86ReturnPath.finished_result middle 6 value prepared
  have wholeFrame : X86StateFrame.Frame {.rax, .r14, .r15, .rflags, .rip}
      (X86WriteWords.written input.receiptAddress (List.range 8) ∪ writes facts) state after :=
    (framed.trans correct.frame).mono (by decide) (by simp [X86ReturnPath.writes, writes, prepared, changed])
  have outsideAll (index byte : Nat) (present : Capture.image[index]? = some byte) :
      ((address base index).signExtend 52).toNat ∉
        X86WriteWords.written input.receiptAddress (List.range 8) ∪ writes facts := by
    intro member
    rcases Finset.mem_union.mp member with member | member
    · exact outsideFund index byte present member
    · exact outsideReturn index byte present member
  refine ⟨after, flags, X86FuelPrefix.fetches_then 6 4 state middle after first last, wholeFrame,
    wholeFrame.codeLoaded base _ loaded outsideAll, correct.rax, correct.status, correct.result,
    ?_, correct.flags, ?_⟩
  · intro index within
    rw [correct.frame.memory _ (receiptOutside index within)]
    exact receiptRead index within
  · exact correct.pointer.trans (congrArg (fun pointer => some (pointer.signExtend 64)) epilogueEq)

namespace Controls

open Exhaustion.Controls (overlay overlay_inside overlay_outside)

private noncomputable def sampleState : State :=
  let regs := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let regs := regs.insert .fault_reg false
  let regs := regs.insert .msrs (Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64)))
  let regs := regs.insert .seg_hidden_attrs (Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16)))
  let regs := regs.insert .app_view true
  let regs := regs.insert .log_register_writes false
  let regs := regs.insert .ctrs (Vector.replicate 17 (0#64))
  let regs := regs.insert .seg_visibles (Vector.replicate 6 (0#16))
  let regs := regs.insert .rflags (2#32)
  let regs := regs.insert .rip (4096#64)
  let regs := regs.insert .rdi (1048576#64)
  let regs := regs.insert .rsi (0xfedcba9876543210#64)
  let mem := overlay ∅ 4087 Capture.image.length (fun index => BitVec.ofNat 8 Capture.image[index]!)
  let mem := overlay mem 1048736 8 (fun index => (10#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048744 8 (fun index => (7#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048720 8 (fun index => (99#64).extractLsb' (8 * index) 8)
  let mem := overlay mem 1048728 8 (fun index => (77#64).extractLsb' (8 * index) 8)
  ⟨regs, (), mem, (), 0, #[]⟩

theorem sample_code : ∀ index : Fin Capture.image.length,
    sampleState.mem.get? (4087 + index.val) = some (BitVec.ofNat 8 Capture.image[index.val]) := by
  intro index
  have bound : index.val < 120 := by simpa only [Capture.image_length] using index.isLt
  simp only [sampleState]
  rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
    overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
    overlay_inside _ _ _ _ _ index.isLt]
  rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem index.isLt)]

theorem sample_controls : X86Funding.Controls.Inputs sampleState (10#64) (7#64) (2#32)
    (Placed.completeCode grade (53#32)) := by
  constructor
  case loaded =>
    intro index
    have full : codeLoaded sampleState 4087 Capture.image := by
      intro offset byte present
      obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
      have bounded : offset < 120 := by simpa only [Capture.image_length] using within
      have place : ((address 4087 offset).signExtend 52).toNat = 4087 + offset := by
        interval_cases offset <;> rfl
      rw [place]
      simpa only [same] using sample_code ⟨offset, within⟩
    have body := Placed.captured_window sampleState 4087 full index.val _ (List.getElem?_eq_getElem index.isLt)
    have within : index.val < 36 := by exact index.isLt
    have place (offset : Nat) (bounded : offset < 36) :
        ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
      interval_cases offset <;> rfl
    change sampleState.mem.get? ((address 4096 index.val).signExtend 52).toNat = _ at body
    rw [place index.val within] at body
    exact body
  case budget =>
    intro index
    simp only [sampleState]
    rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
      overlay_outside _ _ _ _ _ (by omega), overlay_inside _ _ _ _ _ index.isLt]
  case receipt =>
    intro index
    simp only [sampleState]
    rw [overlay_outside _ _ _ _ _ (by omega), overlay_outside _ _ _ _ _ (by omega),
      overlay_inside _ _ _ _ _ index.isLt]
  all_goals simp [sampleState, Std.ExtDHashMap.get?_insert]
  all_goals rfl

private noncomputable def sampleOrigin : X86LegacyFetch.Basis sampleState :=
  Placed.calibrationBasis sampleState grade (53#32) (10#64) (7#64) (2#32) sample_controls

private noncomputable def sampleFund : Placed.Inputs sampleState sampleOrigin grade (53#32) (10#64) (7#64) :=
  Placed.calibrationInput sampleState grade (53#32) (10#64) (7#64) (2#32) sample_controls

private def sampleFacts : X86FailureHandler.FrameFacts sampleState where
  frame := 1048576#64
  statusAddress := 1048720#48
  resultAddress := 1048728#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  visible := Vector.replicate 6 (0#16)
  controls := Vector.replicate 17 (0#64)
  flags := 2#32
  frameKnown := by
    change (sampleState.regs.get? .rdi).map (fun value : Word => value) = _
    rw [sample_controls.base]
    rfl
  controlsKnown := sample_controls.controlKnown
  visibleKnown := sample_controls.visibleKnown
  flagsKnown := sample_controls.flagsKnown
  quiet := sample_controls.quiet
  statusOutside := by intro index within; interval_cases index <;> decide

theorem sample_image : codeLoaded sampleState 4087 Capture.image := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have bounded : index < 120 := by simpa only [Capture.image_length] using within
  have place : ((address 4087 index).signExtend 52).toNat = 4087 + index := by
    interval_cases index <;> rfl
  rw [place]
  simpa only [same] using sample_code ⟨index, within⟩


theorem sample_reaches_epilogue (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 10).run sampleState = .ok () after ∧
      after.regs.get? .rip = some (4197#64) ∧ lookup after 0 = some (0xfedcba9876543210#64) ∧
      after.mem.get? 1048720 = some (1#8) ∧ after.mem.get? 1048728 = some (0x10#8) ∧
      after.mem.get? 1048744 = some (10#8) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have sourceKnown : lookup sampleState 6 = some (0xfedcba9876543210#64) := by
    change (sampleState.regs.get? .rsi).map (fun value : Word => value) = _
    simp [sampleState]
  obtain ⟨after, _, run, _, _, rax, statusBytes, resultBytes, receiptBytes, _, pointer⟩ :=
    Return.executes other extra vector sampleState sampleOrigin (10#64) (7#64) (0xfedcba9876543210#64)
      sampleFund sampleFacts 4087 (by rfl) (by decide) sample_image sourceKnown
      (by
        intro index byte present
        have within : index < 120 := by
          have bound := (List.getElem?_eq_some_iff.mp present).choose
          simpa only [Capture.image_length] using bound
        change ((address 4087 index).signExtend 52).toNat ∉ X86WriteWords.written (1048744#48) (List.range 8)
        interval_cases index <;> decide)
      (by
        intro index byte present
        have within : index < 120 := by
          have bound := (List.getElem?_eq_some_iff.mp present).choose
          simpa only [Capture.image_length] using bound
        change ((address 4087 index).signExtend 52).toNat ∉
          X86WriteWords.written (1048720#48) (List.range 8) ∪ X86WriteWords.written (1048728#48) (List.range 8)
        interval_cases index <;> decide)
      (by
        intro index within
        change X86WriteWords.physicalAddress (1048744#48) index ∉
          X86WriteWords.written (1048720#48) (List.range 8) ∪ X86WriteWords.written (1048728#48) (List.range 8)
        interval_cases index <;> decide)
      (by decide)
  exact ⟨after, run, pointer, rax, statusBytes 0 (by decide), resultBytes 0 (by decide), receiptBytes 0 (by decide)⟩

theorem truncated_result_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 10).run sampleState = .ok () after ∧
      lookup after 0 = some (0x76543210#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, run, _, rax, _, _, _⟩ := sample_reaches_epilogue other extra vector
  rintro ⟨after, otherRun, truncated⟩
  have same := X86FuelPrefix.fetches_deterministic 10 sampleState actual after run otherRun
  rw [← same] at truncated
  exact (by decide : some (0xfedcba9876543210#64) ≠ some (0x76543210#64)) (rax.symm.trans truncated)

theorem unpaid_receipt_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (X86FuelPrefix.fetches 10).run sampleState = .ok () after ∧
      after.mem.get? 1048744 = some (7#8) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual, run, _, _, _, _, receipt⟩ := sample_reaches_epilogue other extra vector
  rintro ⟨after, otherRun, unpaid⟩
  have same := X86FuelPrefix.fetches_deterministic 10 sampleState actual after run otherRun
  rw [← same] at unpaid
  exact (by decide : some (10#8) ≠ some (7#8)) (receipt.symm.trans unpaid)

end Controls

end Mettapedia.Machines.TIsa.X86Funding.Return

#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.captured_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.executes
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.sample_reaches_epilogue
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.truncated_result_refused
#print axioms Mettapedia.Machines.TIsa.X86Funding.Return.Controls.unpaid_receipt_refused

namespace Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding
open _root_.X86Registers X86RegisterRefinement X86Execution

theorem prologue_slice : Capture.image.take 9 = X86Prologue.expected := by kernel_reflexivity
theorem epilogue_slice : (Capture.image.drop 110).take 10 = X86Epilogue.expected := by kernel_reflexivity

theorem prologue_byte (index : Fin X86Prologue.expected.length) :
    Capture.image[index.val]? = some X86Prologue.expected[index.val] := by
  revert index
  decide

theorem epilogue_byte (index : Fin X86Epilogue.expected.length) :
    Capture.image[index.val + 110]? = some X86Epilogue.expected[index.val] := by
  revert index
  decide

theorem prologue_window (state : State) (base : Int)
    (loaded : codeLoaded state base Capture.image) :
    codeLoaded state base X86Prologue.expected := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := prologue_byte ⟨index, within⟩
  rw [same] at imageByte
  exact loaded index byte imageByte

theorem epilogue_window (state : State) (base : Int)
    (loaded : codeLoaded state base Capture.image) :
    codeLoaded state (base + 110) X86Epilogue.expected := by
  intro index byte present
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp present
  have imageByte := epilogue_byte ⟨index, within⟩
  rw [same] at imageByte
  have known := loaded (index + 110) byte imageByte
  have place : address (base + 110) index = address base (index + 110) := by
    unfold address
    congr 1
    push_cast
    omega
  rw [place]
  exact known

end Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding

#print axioms Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding.prologue_window
#print axioms Mettapedia.Machines.TIsa.X86Funding.WrapperEncoding.epilogue_window
