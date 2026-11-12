import Mettapedia.Machines.TIsa.X86ReadWords

/-!
# Fetched 64-bit frame loads in the original Sail model

The imported MOV memory-to-register handler is linked explicitly into the
original dispatcher. Its no-SIB disp32 frame form reads RDI, computes the
effective address, performs the original alignment and memory operations,
writes the decoded destination and advances RIP by the decoded length.

The full seven-byte fetch theorem derives intermediate decoder inputs from
architectural state and loaded bytes. No handler execution is assumed.
Native helper-output identity, frame-pointer layout linkage, compiler-buffer
behavior, fuel-prefix and ABI composition are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

section
variable [X86Registers.MemoryPrimitives]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/LoadFunctions.lean.inc"
  sha256 "e767b5e35baf99ff4ea89973834a791cf5e075300b8c98c6b145d7a7a895e234"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end

namespace Mettapedia.Machines.TIsa.X86FrameLoad

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
open Sail.ConcurrencyInterfaceV1

abbrev frameRex (destination : Fin 16) : BitVec 8 := rex true destination 7
def frameModRM (destination : Fin 16) : BitVec 8 := BitVec.ofNat 8 (128 + (destination.val % 8) * 8 + 7)

theorem frame_base : ∀ destination : Fin 16,
    Functions.reg_index (7#3) (frameRex destination) (0#2) = (7#4) := by decide
theorem frame_mod : ∀ destination : Fin 16, Functions._get_modr_m_mod (frameModRM destination) = (2#2) := by decide
theorem frame_rm : ∀ destination : Fin 16, Functions._get_modr_m_r_m (frameModRM destination) = (7#3) := by decide
theorem frame_destination : ∀ destination : Fin 16,
    Functions.reg_index (Functions._get_modr_m_reg (frameModRM destination)) (frameRex destination) (2#2) =
      BitVec.ofNat 4 destination.val := by decide

local instance : MemoryPrimitives := X86Memory.ordinary

theorem effective_disp32 (state : State) (destination : Fin 16) (displacementAddress : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer frame : Word) (displacement : BitVec 32)
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr_32_64 .Mode_64bit false displacementAddress (frameRex destination)
      (7#3) (2#2) (0#8) (0#3)).run state =
      .ok (frame + displacement.signExtend 64, (4 : Int)) state := by
  unfold Functions.x86_effective_addr_32_64
  simp only [show Functions.eq_bits_nat (2#2) 0 = false from rfl,
    show Functions.eq_bits_nat (2#2) 1 = false from rfl,
    show Functions.eq_bits_nat (2#2) 2 = true from rfl,
    show Functions.eq_bits_nat (7#3) 4 = false from rfl,
    Bool.false_eq_true, ite_false, ite_true]
  rw [show Functions.select_address_size .Mode_64bit none = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, bind_assoc, Sail.BitVec.signExtend,
    show Int.toNat (8 : Int) = 8 from rfl]
  rw [run_bind, X86ReadWords.signed_displacement_exact state displacementAddress attributes pointer displacement
    upper segments application rip present]
  dsimp only
  simp only [Functions.in_64bit_mode, ite_true]
  rw [frame_base]
  change (do
    let value ← Functions.rgfi 7
    pure (Functions.bits_of_int (value.toInt + (displacement.signExtend 64).toInt) 64, (4 : Int))).run state = _
  have readFrame : (Functions.rgfi 7).run state = .ok frame state := by
    convert rgfi_exact state 7 frame frameKnown using 1
    rfl
  rw [run_bind, readFrame]
  dsimp only
  rw [X86Alu.bits_of_int_eq, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  rfl

theorem effective_frame (state : State) (destination : Fin 16) (displacementAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer frame : Word) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (upper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_effective_addr .Mode_64bit prefixes displacementAddress (frameRex destination)
      (7#3) (2#2) (0#8) (0#3)).run state =
      .ok (frame + displacement.signExtend 64, (4 : Int)) state := by
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  unfold Functions.x86_effective_addr
  rw [size]
  simp only [pure_bind, addressOverride]
  exact effective_disp32 state destination displacementAddress attributes pointer frame displacement
    upper segments application rip frameKnown present

def alignmentEnabled (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) : Bool :=
  (Functions._get_cr0bits_am (Functions.Mk_cr0bits (Sail.BitVec.truncate controls[0]! 32)) == (1#1)) &&
    ((Sail.BitVec.zeroExtend (Functions._get_rflagsbits_ac flags) 2 == (1#2)) &&
      (Functions._get_segment_selectorbits_rpl (Functions.Mk_segment_selectorbits visible[1]!) == (3#2)))

theorem alignment_exact (state : State) (controls : Vector (BitVec 64) 17)
    (flags : BitVec 32) (visible : Vector (BitVec 16) 6)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible) :
    (Functions.alignment_checking_enabled_p ()).run state =
      .ok (alignmentEnabled controls flags visible) state := by
  unfold Functions.alignment_checking_enabled_p
  simp only [bind_assoc, pure_bind]
  rw [run_bind, readRegister_exact, controlKnown]
  dsimp only
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [run_bind, readRegister_exact, visibleKnown]
  rfl

theorem operand_frame (state : State) (destination : Fin 16) (displacementAddress dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer frame value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (codeUpper : displacementAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address displacementAddress.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes displacementAddress (frameRex destination) (7#3) (2#2) (0#8) (0#3)).run state =
      .ok (Sail.BitVec.zeroExtend value 128, (4 : Int), dataAddress.signExtend 64) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((2#2) == (3#2)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, effective_frame state destination displacementAddress prefixes attributes pointer frame displacement
    addressOverride codeUpper segments application rip frameKnown codePresent]
  dsimp only
  rw [effective]
  simp only [bind_assoc, pure_bind, Bool.true_and]
  rw [run_bind, alignment_exact state controls flags visible controlKnown flagsKnown visibleKnown]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [size]
  simp only [pure_bind, Functions.select_base_register, show Int.toNat (8 : Int) = 8 from rfl]
  unfold Functions.rme_size
  rw [run_bind, run_bind, X86ReadWords.load_word_exact state dataAddress none attributes pointer value ":R"
    (alignmentEnabled controls flags visible) false dataUpper segments application rip (Or.inr aligned) dataPresent]
  rfl

theorem segment_frame (prefixes : BitVec 52)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8)) :
    Functions.select_segment_register .Mode_64bit prefixes (2#2) (7#3) (0#8) = (pure 3 : SailM Nat) := by
  simp [Functions.select_segment_register, Functions.select_address_size, Functions.in_64bit_mode,
    segmentOverride, addressOverride, Functions.eq_bits_nat, Sail.BitVec.toNatInt]

theorem write_destination (state : State) (destination : Fin 16) (value : Word)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi_size (8#4) (BitVec.ofNat 4 destination.val) value (frameRex destination)).run state =
      .ok () (put state destination value) := by
  have bound : destination.val < 2 ^ 4 := destination.isLt
  simpa [Functions.write_rgfi_size, Functions.eq_bits_nat, Functions.wr64, Sail.BitVec.toNatInt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] using write_rgfi_exact state destination value quiet

theorem handler_frame (state : State) (destination : Fin 16) (start displacementAddress next dataAddress : BitVec 48)
    (prefixes : BitVec 52) (attributes visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (pointer frame value : Word) (flags : BitVec 32) (displacement : BitVec 32)
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
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress prefixes (frameRex destination) (0x8b#8)
      (frameModRM destination) (0#8)).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  have size : Functions.select_operand_size .Mode_64bit false (frameRex destination) false prefixes
      false false false = (pure 8 : SailM Int) :=
    X86Move.operand_size64 destination 7 prefixes
  unfold Functions.x86_mov_op_en_rm
  dsimp only
  rw [show ((0x8b#8) == (0x8a#8)) = false from rfl,
    size, run_bind, run_pure]
  dsimp only
  rw [frame_mod, frame_rm, segment_frame prefixes segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    operand_frame state destination displacementAddress dataAddress prefixes attributes visible controls pointer
      frame value flags displacement addressOverride codeUpper dataUpper segments application rip frameKnown
      controlKnown flagsKnown visibleKnown effective aligned codePresent dataPresent]
  dsimp only
  rw [show Sail.BitVec.zeroExtend (Functions.bits_of_int 4 3) 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state displacementAddress (4#48) next (by simpa using advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [show Functions.bits_of_int 8 4 = (8#4) from rfl, frame_destination, X86Move.widen_truncate]
  rw [run_bind, write_destination state destination value quiet]
  change (Functions.write_iptr .Mode_64bit next).run (put state destination value) = _
  exact X86Move.write_pointer64 _ next (by simpa only [diagnostic_put] using quiet)

theorem length_from_distance (start next : BitVec 48) (distance : Nat) (short : distance ≤ 15)
    (apart : next.toInt = start.toInt + distance) :
    Functions.check_instruction_length start next (0#3) = none := by
  have startBits := X86Move.bits_of_int48 start
  have nextBits := X86Move.bits_of_int48 next
  have endBits : (Functions.bits_of_int next.toInt 49).toInt = next.toInt := by
    rw [X86Move.bits_of_int49, BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 49)]
  have small : (Functions.bits_of_int (distance : Int) 50).toInt = distance := by
    rw [X86Alu.bits_of_int_eq]
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  have difference : next.toInt - start.toInt = distance := by omega
  have zero : Functions.bits_of_int 0 3 = (0#3) := rfl
  simpa [Functions.check_instruction_length, Sail.BitVec.toNatInt, startBits, nextBits, endBits,
    zero, difference, small] using (by omega : (distance : Int) ≤ 15)

theorem frame_no_sib (destination : Fin 16) (address16 : Bool) :
    Functions.x86_decode_sib_p (frameModRM destination) address16 = false := by
  simp [Functions.x86_decode_sib_p, frame_rm]

abbrev linkedHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_mov_op_en_rm := Functions.x86_mov_op_en_rm }

theorem dispatch_frame (other : OtherOpcodeHandlers) (destination : Fin 16)
    (start displacementAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start displacementAddress
      (X86LegacyFetch.packet (0x8b#8)) (frameRex destination) (0x8b#8) (frameModRM destination) (0#8) =
      Functions.x86_mov_op_en_rm .Mode_64bit start displacementAddress
        (X86LegacyFetch.packet (0x8b#8)) (frameRex destination) (0x8b#8) (frameModRM destination) (0#8) := by
  rfl

theorem fetched_frame (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (destination : Fin 16) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame value : Word) (flags : BitVec 32) (displacement : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + displacement.signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (frameRex destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (frameModRM destination))
    (codePresent : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8))
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) finish) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x8b#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x8b#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes destination 7 (frameModRM destination)
    (frame_no_sib destination) origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs
    origin.segments origin.longMode origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [dispatch_frame other destination]
  apply handler_frame state destination origin.address origin.next finish dataAddress
    (X86LegacyFetch.packet (0x8b#8)) origin.attributes visible controls (origin.address.signExtend 64)
    frame value flags displacement (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) advance
  · apply length_from_distance _ _ 7 (by decide)
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
  · exact controlKnown
  · exact flagsKnown
  · exact visibleKnown
  · exact quiet
  · exact effective
  · exact aligned
  · exact codePresent
  · exact dataPresent

end Mettapedia.Machines.TIsa.X86FrameLoad

#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.effective_disp32
#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.operand_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.handler_frame
#print axioms Mettapedia.Machines.TIsa.X86FrameLoad.fetched_frame
