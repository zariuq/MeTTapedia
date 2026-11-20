import Mettapedia.Machines.TIsa.X86SubImmediate

/-!
# Fetched R15 subtraction by a nonnegative signed-byte immediate

This original 83 /5 form covers immediates zero through 127. It retains the
operand read, immediate-byte fetch, sign-extension semantics, modular result,
defined arithmetic flags and RIP update. Carry records unsigned borrow.
The register frame changes only R15, flags and RIP. Negative immediates and
complete bounds-span composition are outside this contract.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86SubByteImmediate
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def byte (immediate : Fin 128) : BitVec 8 := BitVec.ofNat 8 immediate.val
def word (immediate : Fin 128) : Word := BitVec.ofNat 64 immediate.val

theorem immediate_value : ∀ immediate : Fin 128,
    Sail.BitVec.toNatInt (Sail.BitVec.truncate ((byte immediate).zeroExtend 128) 32) =
      (immediate.val : Int) := by decide

theorem positive_logext (immediate : Fin 128) :
    Functions.binary_logext 8 (immediate.val : Int) = (pure (immediate.val : Int) : SailM Int) := by
  fin_cases immediate <;> rfl

theorem normalized : ∀ immediate : Fin 128,
    Functions.bits_of_int (Functions.loghead_int 64 (immediate.val : Int)) 64 = word immediate := by decide

theorem word_nat : ∀ immediate : Fin 128, (word immediate).toNat = immediate.val := by decide

theorem handler (state : State) (immediate : Fin 128) (start immediateAddress next : BitVec 48)
    (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segmentOverride : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : immediateAddress.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state 15 = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (immediatePresent : state.mem.get? (immediateAddress.signExtend 52).toNat = some (byte immediate)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 4 .Mode_64bit start immediateAddress
        prefixes (0x49#8) (0x83#8) (0xef#8) (0#8)).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (put state 15 (value - word immediate)) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (value.toNat < immediate.val) := by
  obtain ⟨output,arithmetic⟩ := X86Alu.sub_executes_defined state value (word immediate) flags
  have carry := X86Comparison.sub_carry state value (word immediate) flags
  simp only [map_eq_pure_bind,run_bind,arithmetic,run_pure] at carry
  have carryValue := (EStateM.Result.ok.inj carry).1
  refine ⟨output,?_,?_⟩
  swap
  · exact (X86Comparison.merged_carry flags output).trans (by simpa only [word_nat] using carryValue)
  have size : Functions.select_operand_size .Mode_64bit false (0x49#8) false prefixes
      false false false = (pure 8 : SailM Int) := X86Move.operand_size64 (5 : Fin 16) 15 prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x83#8) == (0x80#8)) = false from rfl,
    show ((0x83#8) == (0x82#8)) = false from rfl,
    show ((0x83#8) == (0xf6#8)) = false from rfl,
    show ((0x83#8) == (0x83#8)) = true from rfl,Bool.false_or,Bool.true_or]
  rw [size,run_bind,run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit true (0x49#8) true prefixes
      false false false = (pure 1 : SailM Int) from rfl]
  simp only [pure_bind,show Functions.check_range 1 4 1 = (pure 1 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_mod (0xef#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xef#8) = (7#3) from rfl,
    X86MovePrefix.segment64 prefixes (7#3) (0#8) segmentOverride addressOverride,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,show Functions.bits_of_int 1 3 = (1#3) from rfl,
    X86SubImmediate.register_operand_immediate_size prefixes immediateAddress (1#3),run_bind]
  have operand := X86Arithmetic.operand_register64 state (5 : Fin 16) 15 value prefixes immediateAddress known
  change (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
    prefixes immediateAddress (0x49#8) (7#3) (3#2) (0#8) (0#3)).run state =
      .ok (Sail.BitVec.zeroExtend value 128,(0 : Int),(0#64)) state at operand
  rw [operand]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl,run_bind,X86Move.add_pointer_zero]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size,Functions.in_64bit_mode,addressOverride]
  rw [addressSize]
  simp only [pure_bind,bind_assoc,show Int.toNat (1 : Int) = 1 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl,Sail.BitVec.signExtend]
  rw [run_bind,X86SubImmediate.read_immediate state immediateAddress pointer attributes (byte immediate)
    segments application rip immediatePresent]
  dsimp only
  rw [show Functions.ash_left_int 1 3 = 8 from rfl,immediate_value,positive_logext,run_bind,run_pure]
  dsimp only
  rw [show Functions.bits_of_int 1 48 = (1#48) from rfl,run_bind,
    X86PrefixRead.add_pointer_checked state immediateAddress (1#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate,show Functions.ash_left_int 8 3 = 64 from rfl,normalized]
  change (do
    let (result,resultFlags,undefined) ← Functions.gpr_sub_spec_8 value (word immediate) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (result.zeroExtend 128) 3
      (0#64) prefixes (0x49#8) (7#3) (3#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,arithmetic]
  dsimp only
  have write := X86MovePrefix.write_operand_register64 state (5 : Fin 16) 15 (value - word immediate) prefixes quiet
  change (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false ((value - word immediate).zeroExtend 128) 3
    (0#64) prefixes (0x49#8) (7#3) (3#2) (0#8)).run state = .ok () (put state 15 (value - word immediate)) at write
  rw [run_bind,write]
  dsimp only
  rw [run_bind,X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide),diagnostic_put]
  exact quiet

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (immediate : Fin 128) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 1 = finish.toInt)
    (known : lookup state 15 = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x49#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x83#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0xef#8))
    (immediateByte : state.mem.get? (origin.next.signExtend 52).toNat = some (byte immediate)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state 15 (value - word immediate)) (X86Flags.mergeFlags flags output)) finish) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (value.toNat < immediate.val) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x83#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p (0xef#8) address16 = false := by decide
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x83#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 5 15 (0xef#8) noSib origin.step1 origin.step2
    origin.step3 origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode
    origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [show rex true (5 : Fin 16) 15 = (0x49#8) from by decide,X86SubImmediate.dispatch_sub4 other]
  apply handler state immediate origin.address origin.next finish (X86LegacyFetch.packet (0x83#8)) origin.attributes
    (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advance _ origin.segments origin.application origin.rip known flagsKnown quiet immediateByte
  apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
  have := origin.step2
  have := origin.step3
  omega

theorem result_frame (state : State) (immediate : Fin 128) (value : Word) (flags output : BitVec 32)
    (finish : BitVec 48) : RegisterFrame {.r15,.rflags,.rip} state
      (X86Move.putPointer (X86Flags.putFlags (put state 15 (value - word immediate))
        (X86Flags.mergeFlags flags output)) finish) := by
  simpa [key,Finset.insert_comm] using
    ((put_frame state 15 (value - word immediate)).trans
      (flags_frame _ (X86Flags.mergeFlags flags output))).trans (pointer_frame _ finish)

#print axioms handler
#print axioms fetched

end Mettapedia.Machines.TIsa.X86SubByteImmediate
