import Mettapedia.Machines.TIsa.X86PositiveImmediate

/-!
# Fetched qword comparison with a signed immediate

The emitted counter and dispatch tests use nonnegative signed32
literals and the all-ones sentinel. The comparison writes the
subtraction flags and preserves the operand register.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86CmpImmediate64

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution
open X86PositiveImmediate (Immediate immediate32 immediate64)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Literal where
  | nonnegative (value : Immediate)
  | sentinel
  deriving DecidableEq, Repr

def Literal.bits : Literal → BitVec 32
  | .nonnegative value => immediate32 value
  | .sentinel => 0xffffffff

def Literal.value : Literal → Word
  | .nonnegative value => immediate64 value
  | .sentinel => 0xffffffffffffffff

def Literal.input : Literal → Int
  | .nonnegative value => value.val
  | .sentinel => 4294967295

def Literal.signed : Literal → Int
  | .nonnegative value => value.val
  | .sentinel => -1

private theorem raw_immediate (literal : Literal) :
    Sail.BitVec.toNatInt (Sail.BitVec.truncate (literal.bits.zeroExtend 128) 32) = literal.input := by
  cases literal with
  | nonnegative value => exact X86PositiveImmediate.immediate_value value
  | sentinel => rfl

private theorem signed_immediate (state : State) (literal : Literal) :
    (Functions.binary_logext 32 literal.input).run state = .ok literal.signed state := by
  cases literal with
  | nonnegative value => exact X86PositiveImmediate.logext32 state value
  | sentinel => rfl

private theorem signed_word (literal : Literal) :
    Functions.bits_of_int (Functions.loghead_int 64 literal.signed) 64 = literal.value := by
  cases literal with
  | nonnegative value => exact X86PositiveImmediate.normalized value
  | sentinel => rfl

def code (destination : Fin 16) (literal : Literal) : List Nat :=
  [(rex true 7 destination).toNat, 0x81, (modRM 7 destination).toNat] ++
    (List.range 4).map fun byte => (literal.bits.extractLsb' (8 * byte) 8).toNat

theorem code_length (destination : Fin 16) (literal : Literal) : (code destination literal).length = 7 := by
  simp [code]

private theorem rex_selects_operand : ∀ destination : Fin 16,
    rex true 7 destination = rex true 0 destination := by decide +kernel

structure Flags (state : State) (first second : Word) (incoming outgoing : BitVec 32) : Prop where
  computed : (Functions.gpr_sub_spec_8 first second incoming).run state =
    .ok (first - second, outgoing, 0#32) state
  carry : Functions._get_rflagsbits_cf (X86Flags.mergeFlags incoming outgoing) =
    Functions.bool_to_bits (first.toNat < second.toNat)
  zero : Functions._get_rflagsbits_zf (X86Flags.mergeFlags incoming outgoing) =
    Functions.zf_spec (first - second).toNat

theorem handler (state : State) (destination : Fin 16) (literal : Literal)
    (start immediate next : BitVec 48) (prefixes : BitVec 52)
    (attributes : Vector (BitVec 16) 6) (pointer value : Word) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressWidth : Functions._get_prefixes_adr prefixes = (0#8))
    (operandOverride : Functions._get_prefixes_opr prefixes = (0#8))
    (advance : immediate.toInt + 4 = next.toInt)
    (extent : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (known : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4, state.mem.get? ((address immediate.toInt index).signExtend 52).toNat =
      some (literal.bits.extractLsb' (8 * index) 8)) :
    ∃ output, (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediate
      prefixes (rex true 7 destination) (0x81#8) (modRM 7 destination) (0#8)).run state =
      .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) next) ∧
      Flags state value literal.value flags output := by
  obtain ⟨output, computed⟩ := X86Alu.sub_executes_defined state value literal.value flags
  have carry := X86Comparison.sub_carry state value literal.value flags
  have zero := X86Comparison.sub_zero state value literal.value flags
  simp only [map_eq_pure_bind, run_bind, computed, run_pure] at carry zero
  refine ⟨output, ?_, ⟨computed, (X86Comparison.merged_carry _ _).trans (EStateM.Result.ok.inj carry).1,
    (X86Comparison.merged_zero _ _).trans (EStateM.Result.ok.inj zero).1⟩⟩
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x81#8) == (0x80#8)) = false from rfl,
    show ((0x81#8) == (0x82#8)) = false from rfl, show ((0x81#8) == (0xf6#8)) = false from rfl,
    show ((0x81#8) == (0x83#8)) = false from rfl, Bool.false_or]
  rw [X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  have immediateSize : Functions.select_operand_size .Mode_64bit false (rex true 7 destination) true prefixes
      false false false = (pure 4 : SailM Int) := by
    simp [Functions.select_operand_size, Functions.in_64bit_mode, operandOverride]
  rw [immediateSize]
  simp only [pure_bind, show Functions.check_range 1 4 4 = (pure 4 : SailM Int) from rfl]
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressWidth, run_bind, run_pure]
  dsimp only
  have sameOperand : Functions._get_modr_m_r_m (modRM 7 destination) =
      Functions._get_modr_m_r_m (modRM 0 destination) := by fin_cases destination <;> rfl
  rw [show Int.toNat (8 : Int) = 8 from rfl, show Functions.bits_of_int 4 3 = (4#3) from rfl,
    rex_selects_operand, sameOperand, run_bind,
    X86AddImmediate.operand state destination value prefixes immediate (4#3) known]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl, run_bind, X86Move.add_pointer_zero]
  dsimp only
  have size : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressWidth]
  rw [size]
  simp only [pure_bind, bind_assoc, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  have upper := BitVec.toInt_lt (x := next)
  rw [run_bind, X86FrameStore.read_dword state immediate pointer attributes literal.bits
    (by omega) segments application rip present]
  dsimp only
  rw [show Functions.ash_left_int 4 3 = 32 from rfl, raw_immediate, run_bind, signed_immediate]
  dsimp only
  rw [show Functions.ash_left_int 8 3 = 64 from rfl,
    show Functions.bits_of_int 4 48 = (4#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state immediate (4#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49, extent]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, signed_word]
  change (do let (_, newFlags, undef) ← Functions.gpr_sub_spec_8 value literal.value flags
             Functions.write_user_rflags newFlags undef
             Functions.write_iptr .Mode_64bit next : SailM Unit).run state = _
  rw [run_bind, computed]
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags state flags output flagsKnown quiet]
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact quiet

private theorem dispatch (other : OtherOpcodeHandlers) (destination : Fin 16) (start immediate : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediate (X86LegacyFetch.packet (0x81#8))
      (rex true 7 destination) (0x81#8) (modRM 7 destination) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 8 .Mode_64bit start immediate
        (X86LegacyFetch.packet (0x81#8)) (rex true 7 destination) (0x81#8) (modRM 7 destination) (0#8) := by
  fin_cases destination <;> rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (destination : Fin 16) (literal : Literal) (value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (known : lookup state destination = some value) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true 7 destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (modRM 7 destination))
    (present : ∀ index < 4, state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
      some (literal.bits.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) finish) ∧
      Flags state value literal.value flags output := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x81#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide +kernel)
  have noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p (modRM 7 destination) address16 = false := by
    fin_cases destination <;> decide +kernel
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x81#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 7 destination (modRM 7 destination)
    noSib origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs origin.segments origin.longMode
    origin.codeMode origin.application origin.rip prefixByte opcodeByte modrmByte, dispatch other]
  refine handler state destination literal origin.address origin.next finish (X86LegacyFetch.packet (0x81#8))
    origin.attributes (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _)
    (X86LegacyFetch.packet_address _) (X86DwordLoad.packet_operand _) advance ?_ origin.segments
    origin.application origin.rip known flagsKnown quiet present
  apply X86FrameLoad.length_from_distance _ _ 7 (by decide)
  have := origin.step3
  have := origin.step2
  omega

end Mettapedia.Machines.TIsa.X86CmpImmediate64
