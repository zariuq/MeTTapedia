import Mettapedia.Machines.TIsa.X86Flags
import Mettapedia.Machines.TIsa.X86LegacyFetch

/-!
# Fetched arithmetic instructions in the pinned Sail model

The original arithmetic handler is linked explicitly into the imported
opcode dispatcher. ADD and SUB read the encoded source and destination,
compute the portable result, update the defined flags and advance RIP.
The complete fetch theorem uses input bytes and architectural geometry,
with no assumed handler-correctness field. Controls exercise wraparound,
register aliasing and an opcode mutation that changes the answer.

X86BinBlock composes the captured U64 ADD/SUB templates. Other arithmetic
cases remain in the original handler dependency closure; their instruction
contracts and complete program refinement remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2_000_000

section
variable [X86Registers.MemoryPrimitives]

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/ArithmeticFunctions.lean.inc"
  sha256 "2da5e4d6fe8df92c3b9821a61e718ee61257fbf5f4545d3608f6193a080b36dc"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

end

namespace Mettapedia.Machines.TIsa.X86Arithmetic

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
open Sail.ConcurrencyInterfaceV1

inductive DefinedOperation where
  | add | sub
  deriving DecidableEq

def operationNumber : DefinedOperation → Nat
  | .add => 0 | .sub => 4

def opcode : DefinedOperation → BitVec 8
  | .add => 0x01#8 | .sub => 0x29#8

def result (operation : DefinedOperation) (left right : Word) : Word :=
  match operation with
  | .add => left + right | .sub => left - right

theorem calculate_defined (operation : DefinedOperation) (state : State)
    (left right : Word) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_arith_logic_spec 8 (operationNumber operation) left right flags).run state =
      .ok (result operation left right, output, 0#32) state := by
  cases operation with
  | add => exact X86Alu.add_executes_defined state left right flags
  | sub => exact X86Alu.sub_executes_defined state left right flags

theorem operand_register64 [MemoryPrimitives] (state : State) (source destination : Fin 16)
    (value : Word) (prefixes : BitVec 52) (pointer : BitVec 48)
    (known : lookup state destination = some value) :
    (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes pointer (rex true source destination)
      (Functions._get_modr_m_r_m (modRM source destination)) (3#2) (0#8) (0#3)).run state =
        .ok (Sail.BitVec.zeroExtend value 128, (0 : Int), (0#64)) state := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl,
    show ((0#1) == (0#1)) = true from rfl, ite_true, pure_bind]
  rw [show Functions.bits_of_int ((8 : Nat) : Int) 4 = (8#4) from rfl, destination_register]
  rw [run_bind, run_bind, X86Move.read_register64 state destination _ value known]
  rfl

theorem register64 [MemoryPrimitives] (operation : DefinedOperation)
    (state : State) (source destination : Fin 16) (left right : Word)
    (start next : BitVec 48) (prefixes : BitVec 52) (flags : BitVec 32)
    (segment : Functions._get_prefixes_seg prefixes = (0#8))
    (addressSize : Functions._get_prefixes_adr prefixes = (0#8))
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (length : Functions.check_instruction_length start next (0#3) = none) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (operationNumber operation)
        .Mode_64bit start next prefixes (rex true source destination) (opcode operation)
        (modRM source destination) (0#8)).run state =
          .ok () (X86Move.putPointer
            (X86Flags.putFlags (put state destination (result operation left right))
              (X86Flags.mergeFlags flags output)) next) := by
  obtain ⟨output, calculated⟩ := calculate_defined operation state left right flags
  refine ⟨output, ?_⟩
  have byteOperand : ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& opcode operation) 1) = false := by
    cases operation <;> decide
  have compare : ((operationNumber operation == 8) || (operationNumber operation == 7)) = false := by
    cases operation <;> decide
  have eightBits : Functions.bits_of_int 8 4 = (8#4) := rfl
  have zeroDelta : Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) := rfl
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [byteOperand, X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [eightBits, source_register, run_bind,
    X86Move.read_register64 state source _ right sourceKnown]
  dsimp only
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressSize, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    run_bind, operand_register64 state source destination left prefixes next destinationKnown]
  dsimp only
  rw [zeroDelta, run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length]
  rw [if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, run_bind, calculated]
  dsimp only
  rw [compare]
  rw [if_neg (by decide : ¬false = true)]
  rw [run_bind, X86MovePrefix.write_operand_register64 state source destination
    (result operation left right) prefixes quiet]
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown)
    (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide), diagnostic_put]
  exact quiet

abbrev linkedHandlers [MemoryPrimitives] (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g :=
    Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g }

theorem opcode_regular (operation : DefinedOperation) :
    X86LegacyFetch.RegularOpcode (opcode operation) := by
  apply (X86LegacyFetch.checkOpcode_iff _).mp
  cases operation <;> decide

theorem packet_segment (operation : DefinedOperation) :
    Functions._get_prefixes_seg (X86LegacyFetch.packet (opcode operation)) = (0#8) := by
  cases operation <;> decide

theorem dispatch_linked [MemoryPrimitives] (other : OtherOpcodeHandlers)
    (operation : DefinedOperation) (mode : proc_mode) (start next : BitVec 48)
    (rexByte modrm sib : BitVec 8) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    Functions.one_byte_opcode_execute mode start next (X86LegacyFetch.packet (opcode operation))
      rexByte (opcode operation) modrm sib =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g (operationNumber operation)
        mode start next (X86LegacyFetch.packet (opcode operation)) rexByte (opcode operation) modrm sib := by
  cases operation <;>
    simp only [Functions.one_byte_opcode_execute, Functions.ext_one_byte_opcode_execute,
      opcode, operationNumber, Functions.eq_bits_nat, Sail.BitVec.toNatInt,
      X86LegacyFetch.packet_lock, show ((0xf0#8) == (0#8)) = false from rfl,
      Bool.and_false, Bool.false_eq_true, ite_false]
  all_goals rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem fetched_register64 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (opcode operation) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (put state destination (result operation left right))
          (X86Flags.mergeFlags flags output)) window.next) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [X86LegacyFetch.Window.dispatches (opcode operation) (opcode_regular operation) true
    state source destination window]
  rw [dispatch_linked other operation]
  apply register64 operation state source destination left right window.address window.next
    (X86LegacyFetch.packet (opcode operation)) flags
    (packet_segment operation) (X86LegacyFetch.packet_address _) sourceKnown destinationKnown flagsKnown quiet
  exact X86InstructionFetch.length_from_geometry _ _ (by have := window.step2; have := window.step3; omega)

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped (operation : DefinedOperation) (destination : Fin 16) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .r8 (7#64)
  let registers := registers.insert .r9 (5#64)
  ⟨registers, (),
    (((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (rex true 8 destination)).insert 4097
      (opcode operation)).insert 4098 (modRM 8 destination), (), 0, #[]⟩

private def window (operation : DefinedOperation) (destination : Fin 16) :
    X86LegacyFetch.Window (mapped operation destination) (opcode operation) true 8 destination where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := control
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
  prefixByte := by simp [mapped, Std.ExtHashMap.getElem_insert]
  opcodeByte := by simp [mapped, Std.ExtHashMap.getElem_insert]
  modrmByte := by simp [mapped]

private theorem rightKnown (operation : DefinedOperation) (destination : Fin 16) :
    lookup (mapped operation destination) 8 = some (7#64) := by
  change ((mapped operation destination).regs.get? .r8).map (fun value : Word => value) = _
  simp [mapped, Std.ExtDHashMap.get?_insert]

private theorem leftKnown (operation : DefinedOperation) :
    lookup (mapped operation 9) 9 = some (5#64) := by
  change ((mapped operation 9).regs.get? .r9).map (fun value : Word => value) = _
  simp [mapped]

private theorem observed_result (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : DefinedOperation) (destination : Fin 16) (left : Word)
    (known : lookup (mapped operation destination) destination = some left) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped operation destination) = .ok () after ∧
      lookup after destination = some (result operation left (7#64)) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, executed⟩ := fetched_register64 other vector operation (mapped operation destination)
    8 destination (window operation destination) left (7#64) (0x200#32)
    (rightKnown operation destination) known
    (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert])
  refine ⟨_, executed, ?_⟩
  rw [X86Move.lookup_putPointer, X86Flags.putFlags_gpr, lookup_put_same]

theorem fetched_add (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped .add 9) = .ok () after ∧
      lookup after 9 = some (12#64) :=
  observed_result other vector .add 9 (5#64) (leftKnown .add)

theorem fetched_sub_wrap (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped .sub 9) = .ok () after ∧
      lookup after 9 = some (0xfffffffffffffffe#64) :=
  observed_result other vector .sub 9 (5#64) (leftKnown .sub)

theorem fetched_alias_add (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped .add 8) = .ok () after ∧
      lookup after 8 = some (14#64) :=
  observed_result other vector .add 8 (7#64) (rightKnown .add 8)

theorem altered_opcode_refuses_original_answer (other : OtherOpcodeHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped .sub 9) = .ok () after ∧
      lookup after 9 = some (12#64) := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, correct⟩ := fetched_sub_wrap other vector
  rintro ⟨supplied, suppliedRun, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans suppliedRun)).2
  rw [← same, correct] at wrong
  exact (by decide : (0xfffffffffffffffe#64) ≠ (12#64)) (Option.some.inj wrong)

end Controls
end Mettapedia.Machines.TIsa.X86Arithmetic

#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.register64
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.fetched_register64
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.Controls.fetched_add
#print axioms Mettapedia.Machines.TIsa.X86Arithmetic.Controls.altered_opcode_refuses_original_answer
