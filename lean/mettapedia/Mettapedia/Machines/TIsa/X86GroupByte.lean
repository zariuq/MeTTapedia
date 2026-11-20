import Mettapedia.Machines.TIsa.X86SubByteImmediate
import Mettapedia.Machines.TIsa.X86AddImmediate

/-!
# Fetched ADD, SUB and CMP with a nonnegative byte immediate

The three group-one forms share decoding and signed extension.
CMP retains its operand. ADD and SUB install the modular result.
The returned flags describe the sum carry or subtraction borrow.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Machines.TIsa.X86GroupByte

open _root_.X86Registers X86Execution X86RegisterRefinement X86RegisterEncoding
open X86SubByteImmediate (byte word immediate_value positive_logext normalized word_nat)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Kind where
  | add | sub | cmp
  deriving DecidableEq, Repr

def Kind.group : Kind → Nat | .add => 0 | .sub => 4 | .cmp => 8
def Kind.digit : Kind → Fin 16 | .add => 0 | .sub => 5 | .cmp => 7

def Kind.result (kind : Kind) (left right : Word) : Word :=
  match kind with | .add => left + right | .sub | .cmp => left - right

def Kind.carry (kind : Kind) (left right : Word) : Bool :=
  match kind with
  | .add => decide (2^64 ≤ left.toNat + right.toNat)
  | .sub | .cmp => decide (left.toNat < right.toNat)

def Kind.updated (kind : Kind) (state : State) (destination : Fin 16) (left right : Word) : State :=
  if kind = .cmp then state else put state destination (kind.result left right)

def code (kind : Kind) (destination : Fin 16) (immediate : Fin 128) : List Nat :=
  [(rex true kind.digit destination).toNat, 0x83, (modRM kind.digit destination).toNat, immediate.val]

private theorem arithmetic (kind : Kind) (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ out, (Functions.gpr_arith_logic_spec 8 kind.group left right flags).run state =
      .ok (kind.result left right, out, 0#32) state ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags out) = Functions.bool_to_bits (kind.carry left right) := by
  cases kind with
  | add =>
    obtain ⟨out, ran⟩ := X86Alu.add_executes_defined state left right flags
    have observed := X86AddImmediate.add_carry state left right flags
    simp only [map_eq_pure_bind, run_bind, ran, run_pure] at observed
    exact ⟨out, ran, (X86Comparison.merged_carry ..).trans (EStateM.Result.ok.inj observed).1⟩
  | sub | cmp =>
    obtain ⟨out, ran⟩ := X86Alu.sub_executes_defined state left right flags
    have observed := X86Comparison.sub_carry state left right flags
    simp only [map_eq_pure_bind, run_bind, ran, run_pure] at observed
    exact ⟨out, ran, (X86Comparison.merged_carry ..).trans (EStateM.Result.ok.inj observed).1⟩

private theorem register_only (prefixes : BitVec 52) (pointer : BitVec 48) (rexByte : BitVec 8)
    (rm : BitVec 3) (extra : BitVec 3) :
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer rexByte rm (3#2) (0#8) extra =
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer rexByte rm (3#2) (0#8) (0#3) := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [beq_self_eq_true, if_true]

theorem handler (kind : Kind) (state : State) (destination : Fin 16) (immediate : Fin 128)
    (start atByte next : BitVec 48) (prefixes : BitVec 52) (attributes : Vector (BitVec 16) 6)
    (pointer value : Word) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (advance : atByte.toInt + 1 = next.toInt)
    (length : Functions.check_instruction_length start next (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (rip : state.regs.get? .rip = some pointer)
    (read : lookup state destination = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : state.mem.get? (atByte.signExtend 52).toNat = some (byte immediate)) :
    ∃ out,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i kind.group .Mode_64bit start atByte
        prefixes (rex true kind.digit destination) (0x83#8) (modRM kind.digit destination) (0#8)).run state =
          .ok () (X86Move.putPointer
            (X86Flags.putFlags (kind.updated state destination value (word immediate))
              (X86Flags.mergeFlags flags out)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags out) =
        Functions.bool_to_bits (kind.carry value (word immediate)) := by
  obtain ⟨out, ran, carry⟩ := arithmetic kind state value (word immediate) flags
  refine ⟨out, ?_, carry⟩
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x83#8) == (0x80#8)) = false from rfl,
    show ((0x83#8) == (0x82#8)) = false from rfl, show ((0x83#8) == (0xf6#8)) = false from rfl,
    show ((0x83#8) == (0x83#8)) = true from rfl, Bool.false_or, Bool.true_or]
  rw [X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit true (rex true kind.digit destination) true prefixes
      false false false = (pure 1 : SailM Int) from rfl]
  simp only [pure_bind, show Functions.check_range 1 4 1 = (pure 1 : SailM Int) from rfl]
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, show Functions.bits_of_int 1 3 = (1#3) from rfl,
    register_only, run_bind, X86Arithmetic.operand_register64 state kind.digit destination value prefixes atByte read]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl, run_bind, X86Move.add_pointer_zero]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [addressSize]
  simp only [pure_bind, bind_assoc, show Int.toNat (1 : Int) = 1 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, X86SubImmediate.read_immediate state atByte pointer attributes (byte immediate)
    segments application rip present]
  dsimp only
  rw [show Functions.ash_left_int 1 3 = 8 from rfl, immediate_value, positive_logext, run_bind, run_pure]
  dsimp only
  rw [show Functions.bits_of_int 1 48 = (1#48) from rfl, run_bind,
    X86PrefixRead.add_pointer_checked state atByte (1#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49, length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, show Functions.ash_left_int 8 3 = 64 from rfl, normalized, run_bind, ran]
  dsimp only
  have operation : ((kind.group == 8 || kind.group == 7) = true) ↔ kind = .cmp := by
    cases kind <;> decide +kernel
  have writes :
      (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false
        (Sail.BitVec.zeroExtend (kind.result value (word immediate)) 128) 3 (0#64) prefixes
        (rex true kind.digit destination) (Functions._get_modr_m_r_m (modRM kind.digit destination))
          (3#2) (0#8)).run state = .ok () (put state destination (kind.result value (word immediate))) :=
    X86MovePrefix.write_operand_register64 state kind.digit destination _ prefixes quiet
  by_cases compare : kind = .cmp
  · rw [if_pos (operation.mpr compare), Kind.updated, if_pos compare, run_bind,
      X86Flags.write_defined_flags state flags out flagsKnown quiet]
    apply X86Move.write_pointer64
    exact (X86Flags.putFlags_other _ _ .log_register_writes (by decide)).trans quiet
  · rw [if_neg (fun accepted => compare (operation.mp accepted)), Kind.updated, if_neg compare, run_bind, writes]
    dsimp only
    rw [run_bind, X86Flags.write_defined_flags _ flags out
      (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
    apply X86Move.write_pointer64
    rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide), diagnostic_put]
    exact quiet

private theorem dispatch (other : OtherOpcodeHandlers) (kind : Kind) (destination : Fin 16)
    (start atByte : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start atByte (X86LegacyFetch.packet (0x83#8))
      (rex true kind.digit destination) (0x83#8) (modRM kind.digit destination) (0#8) =
    Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i kind.group .Mode_64bit start atByte
      (X86LegacyFetch.packet (0x83#8)) (rex true kind.digit destination) (0x83#8)
      (modRM kind.digit destination) (0#8) := by cases kind <;> fin_cases destination <;> rfl

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (kind : Kind) (destination : Fin 16) (immediate : Fin 128) (value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 1 = finish.toInt)
    (read : lookup state destination = some value) (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (rexByte : state.mem.get? (origin.address.signExtend 52).toNat = some (rex true kind.digit destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x83#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (modRM kind.digit destination))
    (present : state.mem.get? (origin.next.signExtend 52).toNat = some (byte immediate)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ out, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (kind.updated state destination value (word immediate)) (X86Flags.mergeFlags flags out))
        finish) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags out) =
        Functions.bool_to_bits (kind.carry value (word immediate)) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x83#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide +kernel)
  have noSib : ∀ override : Bool, Functions.x86_decode_sib_p (modRM kind.digit destination) override = false := by
    cases kind <;> fin_cases destination <;> decide +kernel
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x83#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes kind.digit destination (modRM kind.digit destination)
    noSib origin.step1 origin.step2 origin.step3 origin.status origin.fault origin.msrs origin.segments
    origin.longMode origin.codeMode origin.application origin.rip rexByte opcodeByte modrmByte, dispatch other]
  refine handler kind state destination immediate origin.address origin.next finish (X86LegacyFetch.packet (0x83#8))
    origin.attributes (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _)
    (X86LegacyFetch.packet_address _) advance ?_ origin.segments origin.application origin.rip read flagsKnown quiet present
  apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
  have := origin.step2
  have := origin.step3
  omega

end Mettapedia.Machines.TIsa.X86GroupByte
