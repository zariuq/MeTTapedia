import Mettapedia.Machines.TIsa.X86Shift32
import Mettapedia.Machines.TIsa.X86BareFetch

/-!
# Original fetched dword immediate shifts

C1 /4, /5 and /7 use the original Sail handler, including the immediate
read, five-bit count mask, arithmetic flags and zero-extended register write.
The low-register form omits REX; the high-register form retains REX.B.
Signed source normalization and complete typed template joins are separate.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Shift32Instruction
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86MaskedFlags X86Shift32
open Sail.ConcurrencyInterfaceV1
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev extension := X86Shift.extension

def evaluate (operation : Shift) (value : Word) (count : BitVec 8) : Word :=
  (operation.evaluate (low32 value) ((count &&& 31).setWidth 6).toNat).zeroExtend 64

theorem encoded_result (value : BitVec 32) :
    Sail.BitVec.zeroExtend (Functions.sail_mask 64 (Functions.trunc 4 (value.zeroExtend 64))) 128 =
      value.zeroExtend 128 := by
  change (((value.setWidth 64).setWidth 32).setWidth 64).setWidth 128 = value.setWidth 128
  have cut : (value.setWidth 64).setWidth 32 = value := by
    rw [BitVec.setWidth_setWidth (by decide),BitVec.setWidth_eq]
  rw [cut,BitVec.setWidth_setWidth (by decide)]

theorem selection (operation : Shift) (state : State) (value : BitVec 32)
    (count : BitVec 6) (flags : BitVec 32) (destination : Fin 16) :
    (if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 0
      then Functions.rol_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 1
      then Functions.ror_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 2
      then Functions.rcl_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 3
      then Functions.rcr_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 4
      then Functions.sal_shl_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 5
      then Functions.shr_spec 4 (value.zeroExtend 64) count flags else
    if Functions.eq_bits_nat (Functions._get_modr_m_reg (modRM (extension operation) destination)) 7
      then Functions.sar_spec 4 (value.zeroExtend 64) count flags else pure (0#64,0#32,0#32)).run state =
      (specification operation value count flags).run state := by
  cases operation <;> fin_cases destination <;> rfl

theorem handler (operation : Shift) (state : State) (destination : Fin 16)
    (start immediateAddress next : BitVec 48) (prefixes : BitVec 52)
    (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32) (count : BitVec 8)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
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
        (rex32 destination) (0xc1#8) (modRM (extension operation) destination) (0#8)).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (evaluate operation value count)) next) := by
  obtain ⟨output,mask,calculated⟩ := spec_executes operation state (low32 value) ((count &&& 31).setWidth 6) flags
  refine ⟨output,mask,?_⟩
  unfold Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror
  dsimp only
  simp only [show ((0xc1#8) == (0xc0#8)) = false from rfl,
    show ((0xc1#8) == (0xd0#8)) = false from rfl,
    show ((0xc1#8) == (0xd2#8)) = false from rfl,
    show ((0xc1#8) == (0xc1#8)) = true from rfl,Bool.false_or,Bool.not_false,ite_true]
  rw [operand_size destination prefixes operandOverride,run_bind,run_pure]
  dsimp only
  rw [register_mode,X86MovePrefix.segment64 prefixes _ _ segment addressSize,run_bind,run_pure]
  dsimp only
  rw [show Int.toNat (4 : Int) = 4 from rfl,run_bind,
    operand_register operation state destination value prefixes immediateAddress (1#3) known]
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
  simp only [rex_w_zero,Bool.false_and,Bool.false_eq_true,ite_false,X86Shift.count_mask32]
  simp only [run_bind,
    X86PrefixRead.add_pointer_checked state immediateAddress (1#48) next (by simpa using advance)]
  simp only [run_pure]
  rw [X86Move.truncate_pointer49,length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl,Bool.false_eq_true,ite_false]
  rw [run_bind,readRegister_exact,flagsKnown]
  dsimp only
  have lowValue : Sail.BitVec.truncate ((low32 value).zeroExtend 128) 64 = (low32 value).zeroExtend 64 := by
    change ((low32 value).setWidth 128).setWidth 64 = (low32 value).setWidth 64
    exact BitVec.setWidth_setWidth (by decide)
  simp only [lowValue,Functions.Mk_rflagsbits]
  rw [run_bind,selection,calculated]
  dsimp only
  rw [encoded_result]
  change (do
    Functions.write_user_rflags output mask
    Functions.x86_operand_to_reg_mem .Mode_64bit 4 true false
      ((operation.evaluate (low32 value) ((count &&& 31).setWidth 6).toNat).zeroExtend 128) 3 (0#64) prefixes
      (rex32 destination)
      (Functions._get_modr_m_r_m (modRM (extension operation) destination)) (3#2) (0#8)
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind,write_flags state flags output mask flagsKnown quiet]
  dsimp only
  have write := write_operand operation
    (X86Flags.putFlags state (merged flags output mask)) destination
    (operation.evaluate (low32 value) ((count &&& 31).setWidth 6).toNat) prefixes
    (updated_quiet _ _ quiet)
  rw [run_bind,write]
  apply X86Move.write_pointer64
  rw [diagnostic_put,updated_quiet _ _ quiet]


theorem dispatch_original [OtherOpcodeHandlers] (operation : Shift) (destination : Fin 16)
    (mode : proc_mode) (start next : BitVec 48) (rexByte sib : BitVec 8) :
    Functions.one_byte_opcode_execute mode start next (X86PlainFetch.packet (0xc1#8) (0#4))
      rexByte (0xc1#8) (modRM (extension operation) destination) sib =
      OtherOpcodeHandlers.x86_sal_sar_shl_shr_rcl_rcr_rol_ror mode start next
        (X86PlainFetch.packet (0xc1#8) (0#4)) rexByte (0xc1#8)
        (modRM (extension operation) destination) sib := by
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
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    Functions.one_byte_opcode_execute mode start next (X86PlainFetch.packet (0xc1#8) (0#4))
      rexByte (0xc1#8) (modRM (extension operation) destination) sib =
      Functions.x86_sal_sar_shl_shr_rcl_rcr_rol_ror mode start next
        (X86PlainFetch.packet (0xc1#8) (0#4)) rexByte (0xc1#8)
        (modRM (extension operation) destination) sib := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  exact dispatch_original operation destination mode start next rexByte sib

theorem without_sib : ∀ operation : Shift, ∀ destination : Fin 16, ∀ address16 : Bool,
    Functions.x86_decode_sib_p (modRM (extension operation) destination) address16 = false := by
  intro operation
  cases operation <;> decide

theorem fetched_bare (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (state : State) (destination : Fin 16) (low : destination.val < 8)
    (origin : X86BareFetch.Window state (0xc1#8) (modRM (extension operation) destination))
    (next : BitVec 48) (value : Word) (flags : BitVec 32) (count : BitVec 8)
    (advance : origin.next.toInt + 1 = next.toInt)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (countPresent : state.mem.get? (origin.next.signExtend 52).toNat = some count) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output mask,
      (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (evaluate operation value count)) next) := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0xc1#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86BareFetch.fetch_to_dispatch (0xc1#8) shape state _ origin (without_sib operation destination)]
  rw [dispatch_linked other]
  have length : Functions.check_instruction_length origin.address next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 3 (by decide)
    have := origin.step1
    have := origin.step2
    omega
  have run := handler operation state destination origin.address origin.next next
    (X86PlainFetch.packet (0xc1#8) (0#4)) origin.attributes (origin.address.signExtend 64) value flags count
    (by decide) (X86PlainFetch.packet_address _ _) (by decide) advance length
    origin.segments origin.application origin.rip known flagsKnown quiet countPresent
  simpa only [rex32,if_pos low] using run

theorem rex32_high (operation : Shift) (destination : Fin 16) (high : 8 ≤ destination.val) :
    rex32 destination = rex false (extension operation) destination := by
  simp only [rex32,show ¬destination.val < 8 from by omega,ite_false]
  cases operation <;> rfl

theorem fetched_rex (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Shift) (state : State) (destination : Fin 16) (high : 8 ≤ destination.val)
    (origin : X86LegacyFetch.Window state (0xc1#8) false (extension operation) destination)
    (next : BitVec 48) (value : Word) (flags : BitVec 32) (count : BitVec 8)
    (advance : origin.next.toInt + 1 = next.toInt)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (countPresent : state.mem.get? (origin.next.signExtend 52).toNat = some count) :
    letI : OtherOpcodeHandlers := X86Shift.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output mask,
      (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (put (X86Flags.putFlags state (merged flags output mask)) destination
          (evaluate operation value count)) next) := by
  let : OtherOpcodeHandlers := X86Shift.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0xc1#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0xc1#8) shape false state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes (extension operation) destination
    (modRM (extension operation) destination) (without_sib operation destination)
    origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs origin.segments
    origin.longMode origin.codeMode origin.application origin.rip origin.prefixByte origin.opcodeByte origin.modrmByte]
  rw [X86Shift.dispatch_linked other]
  have length : Functions.check_instruction_length origin.address next (0#3) = none := by
    apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  have run := handler operation state destination origin.address origin.next next
    (X86LegacyFetch.packet (0xc1#8)) origin.attributes (origin.address.signExtend 64) value flags count
    (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _) (by decide) advance length
    origin.segments origin.application origin.rip known flagsKnown quiet countPresent
  simpa only [rex32_high operation destination high] using run

theorem result_frame (operation : Shift) (state : State) (destination : Fin 16) (value : Word)
    (count : BitVec 8) (flags output mask : BitVec 32) (next : BitVec 48) :
    RegisterFrame {key destination,.rflags,.rip} state
      (X86Move.putPointer (put (X86Flags.putFlags state (merged flags output mask)) destination
        (evaluate operation value count)) next) :=
  X86Shift.result_frame state destination _ flags output mask next

theorem admitted_count : ∀ count : BitVec 8, count.toNat < 32 →
    ((count &&& 31).setWidth 6).toNat = count.toNat := by decide

theorem normalize_u32z (value : BitVec 32) :
    ScalarType.u32z.normalize (value.zeroExtend 64) = value.zeroExtend 64 := by
  change extend32 false (low32 (extend32 false value)) = extend32 false value
  rw [low32_extend32]

theorem source_u32z (operation : Shift) (value : Word) (destination : Fin 12)
    (count : BitVec 8) (admitted : count.toNat < 32) :
    P1Scalar.evaluate (.shift operation .u32z destination destination count.toNat) [value] =
      some (evaluate operation value count) := by
  unfold evaluate
  rw [admitted_count count admitted]
  simp only [P1Scalar.evaluate,P1Scalar.shiftWord,P1Scalar.narrow,ite_true,if_pos admitted,
    P1Scalar.normalize,normalize_u32z]

#print axioms encoded_result
#print axioms handler
#print axioms dispatch_original
#print axioms fetched_bare
#print axioms fetched_rex
#print axioms result_frame
#print axioms source_u32z
end Mettapedia.Machines.TIsa.X86Shift32Instruction
