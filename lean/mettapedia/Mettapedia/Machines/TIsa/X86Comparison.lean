import Mettapedia.Machines.TIsa.X86Arithmetic
import Mettapedia.Machines.TIsa.X86Execution

import Mettapedia.Machines.TIsa.X86LogicalFlags

/-!
# Comparison and test flags from the original x86 arithmetic handler

CMP and TEST preserve both input registers and update flags and RIP. Carry
records unsigned comparison; zero records modular subtraction or conjunction.
The fetched contracts retain the original reads, instruction-length checks
and flag writer. The logical flag writer retains its original choice provider;
its defined carry and zero bits are independent of the auxiliary flag.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86Comparison

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
open Sail.ConcurrencyInterfaceV1

theorem merged_carry (original user : BitVec 32) :
    Functions._get_rflagsbits_cf (X86Flags.mergeFlags original user) =
      Functions._get_rflagsbits_cf user := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [X86Flags.mergeFlags, Functions._get_rflagsbits_cf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem merged_zero (original user : BitVec 32) :
    Functions._get_rflagsbits_zf (X86Flags.mergeFlags original user) =
      Functions._get_rflagsbits_zf user := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [X86Flags.mergeFlags, Functions._get_rflagsbits_zf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem sub_carry (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_cf value.2.1) <$>
      Functions.gpr_sub_spec_8 left right flags).run state =
        .ok (Functions.bool_to_bits (left.toNat < right.toNat)) state := by
  unfold Functions.gpr_sub_spec_8 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl,
    show ((64 : Int) ≥b 0) = true from rfl, ite_true]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_cf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange', Sail.BitVec.toNatInt]

theorem sub_zero (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_zf value.2.1) <$>
      Functions.gpr_sub_spec_8 left right flags).run state =
        .ok (Functions.zf_spec (left - right).toNat) state := by
  unfold Functions.gpr_sub_spec_8 Functions.pf_spec64 Functions.of_spec64
  unfold Functions.signed_byte_p_int Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl,
    show ((64 : Int) ≥b 0) = true from rfl, ite_true]
  simp only [X86Alu.sub_result, Sail.BitVec.toNatInt]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_zf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']
  rfl

theorem register_compare64 [MemoryPrimitives]
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
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 8
        .Mode_64bit start next prefixes (rex true source destination) (0x39#8)
        (modRM source destination) (0#8)).run state =
          .ok () (X86Move.putPointer
            (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf output = Functions.bool_to_bits (left.toNat < right.toNat) ∧
      Functions._get_rflagsbits_zf output = Functions.zf_spec (left - right).toNat := by
  obtain ⟨output, calculated⟩ := X86Alu.sub_executes_defined state left right flags
  have carry := sub_carry state left right flags
  have zero := sub_zero state left right flags
  simp only [map_eq_pure_bind, run_bind, calculated, run_pure] at carry zero
  refine ⟨output, ?_, (EStateM.Result.ok.inj carry).1, (EStateM.Result.ok.inj zero).1⟩
  have calculated' : (Functions.gpr_arith_logic_spec 8 8 left right flags).run state =
      .ok (left - right, output, 0#32) state := calculated
  have eightBits : Functions.bits_of_int 8 4 = (8#4) := rfl
  have zeroDelta : Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) := rfl
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x39#8)) 1) = false from rfl,
    X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [eightBits, source_register, run_bind,
    X86Move.read_register64 state source _ right sourceKnown]
  dsimp only
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressSize, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    X86Arithmetic.operand_register64 state source destination left prefixes next destinationKnown]
  dsimp only
  rw [zeroDelta, run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, run_bind, calculated']
  dsimp only
  rw [show ((8 : Nat) == 8 || (8 : Nat) == 7) = true from rfl]
  rw [if_pos rfl, run_bind]
  rw [X86Flags.write_defined_flags state flags output flagsKnown quiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact quiet

theorem register_test64 [MemoryPrimitives]
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
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 7
        .Mode_64bit start next prefixes (rex true source destination) (0x85#8)
        (modRM source destination) (0#8)).run state =
          .ok () (X86Move.putPointer
            (X86Flags.putFlags state (X86LogicalFlags.merged flags output (0#1))) next) ∧
      Functions._get_rflagsbits_cf output = (0#1) ∧
      Functions._get_rflagsbits_zf output = Functions.zf_spec (left &&& right).toNat := by
  obtain ⟨output, calculated⟩ := X86LogicalFlags.and_executes state left right flags
  have carry := X86LogicalFlags.and_carry state left right flags
  have zero := X86LogicalFlags.and_zero state left right flags
  simp only [map_eq_pure_bind, run_bind, calculated, run_pure] at carry zero
  refine ⟨output, ?_, (EStateM.Result.ok.inj carry).1, (EStateM.Result.ok.inj zero).1⟩
  have calculated' : (Functions.gpr_arith_logic_spec 8 7 left right flags).run state =
      .ok (left &&& right, output, 16#32) state := calculated
  have eightBits : Functions.bits_of_int 8 4 = (8#4) := rfl
  have zeroDelta : Sail.BitVec.zeroExtend (Functions.bits_of_int 0 3) 48 = (0#48) := rfl
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g
  dsimp only
  rw [show ((0#1) == Sail.BitVec.truncate ((0x01#8) &&& (0x85#8)) 1) = false from rfl,
    X86Move.operand_size64, run_bind, run_pure]
  dsimp only
  rw [eightBits, source_register, run_bind,
    X86Move.read_register64 state source _ right sourceKnown]
  dsimp only
  rw [register_mode, X86MovePrefix.segment64 prefixes _ _ segment addressSize, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl, run_bind,
    X86Arithmetic.operand_register64 state source destination left prefixes next destinationKnown]
  dsimp only
  rw [zeroDelta, run_bind, X86Move.add_pointer_zero]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate, run_bind, calculated']
  dsimp only
  rw [show ((7 : Nat) == 8 || (7 : Nat) == 7) = true from rfl]
  rw [if_pos rfl, run_bind]
  rw [X86LogicalFlags.write_logical_flags state flags output flagsKnown quiet]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide)]
  exact quiet

theorem dispatch_compare64 [MemoryPrimitives] (other : OtherOpcodeHandlers)
    (start next : BitVec 48) (source destination : Fin 16) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x39#8))
      (rex true source destination) (0x39#8) (modRM source destination) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 8 .Mode_64bit start next
        (X86LegacyFetch.packet (0x39#8)) (rex true source destination) (0x39#8)
        (modRM source destination) (0#8) := by rfl

theorem dispatch_test64 [MemoryPrimitives] (other : OtherOpcodeHandlers)
    (start next : BitVec 48) (source destination : Fin 16) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start next (X86LegacyFetch.packet (0x85#8))
      (rex true source destination) (0x85#8) (modRM source destination) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_g 7 .Mode_64bit start next
        (X86LegacyFetch.packet (0x85#8)) (rex true source destination) (0x85#8)
        (modRM source destination) (0#8) := by rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem fetched_compare64 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x39#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags state (X86Flags.mergeFlags flags output)) window.next) ∧
      Functions._get_rflagsbits_cf output = Functions.bool_to_bits (left.toNat < right.toNat) ∧
      Functions._get_rflagsbits_zf output = Functions.zf_spec (left - right).toNat := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have regular : X86LegacyFetch.RegularOpcode (0x39#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.Window.dispatches (0x39#8) regular true state source destination window,
    dispatch_compare64 other]
  apply register_compare64 state source destination left right window.address window.next
    (X86LegacyFetch.packet (0x39#8)) flags (by decide) (by decide)
    sourceKnown destinationKnown flagsKnown quiet
  exact X86InstructionFetch.length_from_geometry _ _ (by have := window.step2; have := window.step3; omega)

theorem fetched_test64 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x85#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output, (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags state (X86LogicalFlags.merged flags output (0#1))) window.next) ∧
      Functions._get_rflagsbits_cf output = (0#1) ∧
      Functions._get_rflagsbits_zf output = Functions.zf_spec (left &&& right).toNat := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have regular : X86LegacyFetch.RegularOpcode (0x85#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  rw [X86LegacyFetch.Window.dispatches (0x85#8) regular true state source destination window,
    dispatch_test64 other]
  apply register_test64 state source destination left right window.address window.next
    (X86LegacyFetch.packet (0x85#8)) flags (by decide) (by decide)
    sourceKnown destinationKnown flagsKnown quiet
  exact X86InstructionFetch.length_from_geometry _ _ (by have := window.step2; have := window.step3; omega)

theorem status_frame (state : State) (flags : BitVec 32) (next : BitVec 48) :
    X86Execution.RegisterFrame {.rflags, .rip} state
      (X86Move.putPointer (X86Flags.putFlags state flags) next) := by
  simpa using (X86Execution.flags_frame state flags).trans
    (X86Execution.pointer_frame (X86Flags.putFlags state flags) next)

theorem carry_readback (state : State) (flags : BitVec 32) (next : BitVec 48) :
    ((X86Move.putPointer (X86Flags.putFlags state flags) next).regs.get? .rflags).map
      Functions._get_rflagsbits_cf = some (Functions._get_rflagsbits_cf flags) := by
  simp [X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]

theorem zero_readback (state : State) (flags : BitVec 32) (next : BitVec 48) :
    ((X86Move.putPointer (X86Flags.putFlags state flags) next).regs.get? .rflags).map
      Functions._get_rflagsbits_zf = some (Functions._get_rflagsbits_zf flags) := by
  simp [X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]

theorem fetched_compare_observes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x39#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf =
        some (Functions.bool_to_bits (left.toNat < right.toNat)) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf =
        some (Functions.zf_spec (left - right).toNat) ∧
      X86Execution.RegisterFrame {.rflags, .rip} state after := by
  obtain ⟨output, executed, carry, zero⟩ := fetched_compare64 other vector state source destination window
    left right flags sourceKnown destinationKnown flagsKnown quiet
  refine ⟨_, executed, ?_, ?_, status_frame state _ window.next⟩
  · rw [carry_readback, merged_carry, carry]
  · rw [zero_readback, merged_zero, zero]

theorem fetched_test_observes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x85#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf =
        some (Functions.zf_spec (left &&& right).toNat) ∧
      X86Execution.RegisterFrame {.rflags, .rip} state after := by
  obtain ⟨output, executed, carry, zero⟩ := fetched_test64 other vector state source destination window
    left right flags sourceKnown destinationKnown flagsKnown quiet
  refine ⟨_, executed, ?_, ?_, status_frame state _ window.next⟩
  · rw [carry_readback, X86LogicalFlags.merged_carry, carry]
  · rw [zero_readback, X86LogicalFlags.merged_zero, zero]

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped (opcode : BitVec 8) (destination : Fin 16) (budget used : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x3000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .r14 budget
  let registers := registers.insert .r15 used
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 12288 (rex true 14 destination)
  let memory := memory.insert 12289 opcode
  let memory := memory.insert 12290 (modRM 14 destination)
  ⟨registers, (), memory, (), 0, #[]⟩

private def window (opcode : BitVec 8) (destination : Fin 16) (budget used : Word) :
    X86LegacyFetch.Window (mapped opcode destination budget used) opcode true 14 destination where
  address := 0x3000#48
  opcodeAddress := 0x3001#48
  modrmAddress := 0x3002#48
  next := 0x3003#48
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

private theorem known_budget (opcode : BitVec 8) (destination : Fin 16) (budget used : Word) :
    lookup (mapped opcode destination budget used) 14 = some budget := by
  change ((mapped opcode destination budget used).regs.get? .r14).map (fun value : Word => value) = _
  simp [mapped, Std.ExtDHashMap.get?_insert]

private theorem known_used (opcode : BitVec 8) (budget used : Word) :
    lookup (mapped opcode 15 budget used) 15 = some used := by
  change ((mapped opcode 15 budget used).regs.get? .r15).map (fun value : Word => value) = _
  simp [mapped]

theorem compare_below_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (0x39#8) 15 (11#64) (7#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (1#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf = some (0#1) ∧
      X86Execution.RegisterFrame {.rflags, .rip} (mapped (0x39#8) 15 (11#64) (7#64)) after := by
  exact fetched_compare_observes other vector _ 14 15 (window (0x39#8) 15 (11#64) (7#64))
    (7#64) (11#64) (0x200#32) (known_budget ..) (known_used ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])

theorem compare_at_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (0x39#8) 15 (11#64) (11#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf = some (1#1) ∧
      X86Execution.RegisterFrame {.rflags, .rip} (mapped (0x39#8) 15 (11#64) (11#64)) after := by
  exact fetched_compare_observes other vector _ 14 15 (window (0x39#8) 15 (11#64) (11#64))
    (11#64) (11#64) (0x200#32) (known_budget ..) (known_used ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])

theorem test_zero_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (0x85#8) 14 (0#64) (7#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf = some (1#1) ∧
      X86Execution.RegisterFrame {.rflags, .rip} (mapped (0x85#8) 14 (0#64) (7#64)) after := by
  exact fetched_test_observes other vector _ 14 14 (window (0x85#8) 14 (0#64) (7#64))
    (0#64) (0#64) (0x200#32) (known_budget ..) (known_budget ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])

theorem compare_unsigned_high_bit (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run
        (mapped (0x39#8) 15 (7#64) (0x8000000000000000#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf = some (0#1) ∧
      X86Execution.RegisterFrame {.rflags, .rip}
        (mapped (0x39#8) 15 (7#64) (0x8000000000000000#64)) after := by
  exact fetched_compare_observes other vector _ 14 15 (window (0x39#8) 15 (7#64) (0x8000000000000000#64))
    (0x8000000000000000#64) (7#64) (0x200#32) (known_budget ..) (known_used ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])

theorem test_nonzero_budget (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run
        (mapped (0x85#8) 14 (0x8000000000000000#64) (7#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_zf = some (0#1) ∧
      X86Execution.RegisterFrame {.rflags, .rip}
        (mapped (0x85#8) 14 (0x8000000000000000#64) (7#64)) after := by
  exact fetched_test_observes other vector _ 14 14 (window (0x85#8) 14 (0x8000000000000000#64) (7#64))
    (0x8000000000000000#64) (0x8000000000000000#64) (0x200#32) (known_budget ..) (known_budget ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])

theorem changed_opcode_refuses_compare_carry (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped (0x85#8) 15 (11#64) (7#64)) = .ok () after ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (1#1) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, carry, _, _⟩ := fetched_test_observes other vector _ 14 15
    (window (0x85#8) 15 (11#64) (7#64)) (7#64) (11#64) (0x200#32)
    (known_budget ..) (known_used ..)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
  rintro ⟨wrong, wrongExecution, wrongCarry⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans wrongExecution)).2
  rw [← same, carry] at wrongCarry
  cases wrongCarry

end Controls
end Mettapedia.Machines.TIsa.X86Comparison

#print axioms Mettapedia.Machines.TIsa.X86Comparison.register_compare64
#print axioms Mettapedia.Machines.TIsa.X86Comparison.fetched_compare64
#print axioms Mettapedia.Machines.TIsa.X86Comparison.fetched_test64
#print axioms Mettapedia.Machines.TIsa.X86Comparison.Controls.compare_below_budget
#print axioms Mettapedia.Machines.TIsa.X86Comparison.Controls.test_zero_budget
#print axioms Mettapedia.Machines.TIsa.X86Comparison.Controls.changed_opcode_refuses_compare_carry
