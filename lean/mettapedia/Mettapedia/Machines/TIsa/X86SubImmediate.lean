import Mettapedia.Machines.TIsa.X86Funding

/-!
# Fetched immediate subtraction in the p1 bounds check

The original group-1 immediate handler and fetch path execute the four-byte
SUB r15,4 form. Immediate-byte reading, sign extension, modular subtraction,
defined arithmetic flags, register write and RIP advancement are retained.
The carry theorem identifies exactly whether the subtraction borrowed.

The result frame changes only R15, arithmetic flags and RIP. These reusable
instruction contracts do not establish a complete bounds prefix or consumer.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86SubImmediate

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding
local instance : MemoryPrimitives := X86Memory.ordinary

theorem read_immediate (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (value : BitVec 8)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some value) :
    (Functions.rme_size .Mode_64bit 8 1 (address.signExtend 64) none 1 ":X" false false).run state =
      .ok (value.zeroExtend 128) state := by
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    pure (Sail.BitVec.zeroExtend byte 128) : SailM (BitVec 128)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes value
    segments application rip present]
  rfl

theorem register_operand_immediate_size (prefixes : BitVec 52) (address : BitVec 48)
    (immediateBytes : BitVec 3) :
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes address (0x49#8) (7#3) (3#2) (0#8) immediateBytes =
    Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
      prefixes address (0x49#8) (7#3) (3#2) (0#8) (0#3) := by
  unfold Functions.x86_operand_from_modr_m_and_sib_bytes
  simp only [show ((3#2) == (3#2)) = true from rfl, ite_true, pure_bind]

theorem handler_sub4 (state : State) (start immediateAddress next : BitVec 48)
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
    (immediatePresent : state.mem.get? (immediateAddress.signExtend 52).toNat = some (4#8)) :
    ∃ output,
      (Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 4 .Mode_64bit start immediateAddress
        prefixes (0x49#8) (0x83#8) (0xef#8) (0#8)).run state =
      .ok () (X86Move.putPointer
        (X86Flags.putFlags (put state 15 (value - (4#64))) (X86Flags.mergeFlags flags output)) next) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (value.toNat < 4) := by
  obtain ⟨output, arithmetic⟩ := X86Alu.sub_executes_defined state value (4#64) flags
  have carry := X86Comparison.sub_carry state value (4#64) flags
  simp only [map_eq_pure_bind, run_bind, arithmetic, run_pure] at carry
  have carryValue := (EStateM.Result.ok.inj carry).1
  refine ⟨output, ?_, ?_⟩
  swap
  · exact (X86Comparison.merged_carry flags output).trans (by simpa using carryValue)
  have size : Functions.select_operand_size .Mode_64bit false (0x49#8) false prefixes
      false false false = (pure 8 : SailM Int) := X86Move.operand_size64 (5 : Fin 16) 15 prefixes
  unfold Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i
  dsimp only
  simp only [show ((0x83#8) == (0x80#8)) = false from rfl,
    show ((0x83#8) == (0x82#8)) = false from rfl,
    show ((0x83#8) == (0xf6#8)) = false from rfl,
    show ((0x83#8) == (0x83#8)) = true from rfl,
    Bool.false_or, Bool.true_or]
  rw [size, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_operand_size .Mode_64bit true (0x49#8) true prefixes
      false false false = (pure 1 : SailM Int) from rfl]
  simp only [pure_bind, show Functions.check_range 1 4 1 = (pure 1 : SailM Int) from rfl]
  rw [show Functions._get_modr_m_mod (0xef#8) = (3#2) from rfl,
    show Functions._get_modr_m_r_m (0xef#8) = (7#3) from rfl,
    X86MovePrefix.segment64 prefixes (7#3) (0#8) segmentOverride addressOverride, run_bind, run_pure]
  dsimp only
  rw [show Int.toNat (8 : Int) = 8 from rfl,
    show Functions.bits_of_int 1 3 = (1#3) from rfl,
    register_operand_immediate_size prefixes immediateAddress (1#3), run_bind]
  have operand := X86Arithmetic.operand_register64 state (5 : Fin 16) 15 value prefixes immediateAddress known
  change (Functions.x86_operand_from_modr_m_and_sib_bytes .Mode_64bit (0#1) 8 true false 3
    prefixes immediateAddress (0x49#8) (7#3) (3#2) (0#8) (0#3)).run state =
      .ok (Sail.BitVec.zeroExtend value 128, (0 : Int), (0#64)) state at operand
  rw [operand]
  dsimp only
  rw [show Functions.bits_of_int 0 48 = (0#48) from rfl, run_bind, X86Move.add_pointer_zero]
  dsimp only
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  rw [addressSize]
  simp only [pure_bind, bind_assoc, show Int.toNat (1 : Int) = 1 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, read_immediate state immediateAddress pointer attributes (4#8) segments application rip immediatePresent]
  dsimp only
  rw [show Functions.ash_left_int 1 3 = 8 from rfl,
    show Sail.BitVec.toNatInt (Sail.BitVec.truncate ((4#8).zeroExtend 128) 32) = 4 from rfl,
    run_bind, show (Functions.binary_logext 8 4).run state = .ok (4 : Int) state from rfl]
  dsimp only
  rw [show Functions.bits_of_int 1 48 = (1#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state immediateAddress (1#48) next (by simpa using advance)]
  dsimp only
  rw [X86Move.truncate_pointer49, length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, flagsKnown]
  dsimp only
  rw [X86Move.widen_truncate]
  change (do
    let (result, resultFlags, undefined) ← Functions.gpr_sub_spec_8 value (4#64) flags
    Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false (result.zeroExtend 128) 3
      (0#64) prefixes (0x49#8) (7#3) (3#2) (0#8)
    Functions.write_user_rflags resultFlags undefined
    Functions.write_iptr .Mode_64bit next).run state = _
  rw [run_bind, arithmetic]
  dsimp only
  have write := X86MovePrefix.write_operand_register64 state (5 : Fin 16) 15 (value - (4#64)) prefixes quiet
  change (Functions.x86_operand_to_reg_mem .Mode_64bit 8 true false ((value - (4#64)).zeroExtend 128) 3
    (0#64) prefixes (0x49#8) (7#3) (3#2) (0#8)).run state = .ok () (put state 15 (value - (4#64))) at write
  rw [run_bind, write]
  dsimp only
  rw [run_bind, X86Flags.write_defined_flags _ flags output
    (by simpa only [put_flags] using flagsKnown) (by simpa only [diagnostic_put] using quiet)]
  change (Functions.write_iptr .Mode_64bit next).run _ = _
  apply X86Move.write_pointer64
  rw [X86Flags.putFlags_other _ _ .log_register_writes (by decide), diagnostic_put]
  exact quiet

set_option maxRecDepth 4096 in
theorem dispatch_sub4 (other : OtherOpcodeHandlers) (start immediateAddress : BitVec 48) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    Functions.one_byte_opcode_execute .Mode_64bit start immediateAddress (X86LegacyFetch.packet (0x83#8))
      (0x49#8) (0x83#8) (0xef#8) (0#8) =
      Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_test_e_i 4 .Mode_64bit start immediateAddress
        (X86LegacyFetch.packet (0x83#8)) (0x49#8) (0x83#8) (0xef#8) (0#8) := by rfl

theorem fetched_sub4 (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48)
    (value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 1 = finish.toInt)
    (known : lookup state 15 = some value)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0x49#8))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x83#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (0xef#8))
    (immediateByte : state.mem.get? (origin.next.signExtend 52).toNat = some (4#8)) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ output,
      (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (X86Move.putPointer
          (X86Flags.putFlags (put state 15 (value - (4#64))) (X86Flags.mergeFlags flags output)) finish) ∧
      Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
        Functions.bool_to_bits (value.toNat < 4) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have shape : X86LegacyFetch.RegularOpcode (0x83#8) := (X86LegacyFetch.checkOpcode_iff _).mp (by decide)
  have noSib : ∀ address16 : Bool, Functions.x86_decode_sib_p (0xef#8) address16 = false := by decide
  rw [X86LegacyFetch.fetch_to_dispatch_no_sib (0x83#8) shape true state origin.address origin.opcodeAddress
    origin.modrmAddress origin.next origin.control origin.attributes 5 15 (0xef#8) noSib origin.step1 origin.step2
    origin.step3 origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode
    origin.application origin.rip prefixByte opcodeByte modrmByte]
  rw [show rex true (5 : Fin 16) 15 = (0x49#8) from by decide]
  rw [dispatch_sub4 other]
  apply handler_sub4 state origin.address origin.next finish (X86LegacyFetch.packet (0x83#8)) origin.attributes
    (origin.address.signExtend 64) value flags (X86LegacyFetch.packet_segment _) (X86LegacyFetch.packet_address _)
    advance
  · apply X86FrameLoad.length_from_distance _ _ 4 (by decide)
    have := origin.step2
    have := origin.step3
    omega
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact known
  · exact flagsKnown
  · exact quiet
  · exact immediateByte

theorem no_borrow (value : Word) (flags output : BitVec 32)
    (enough : 4 ≤ value.toNat)
    (carry : Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) =
      Functions.bool_to_bits (value.toNat < 4)) :
    Functions._get_rflagsbits_cf (X86Flags.mergeFlags flags output) = (0#1) := by
  rw [carry]
  have notBelow : ¬ value.toNat < 4 := by omega
  simp [Functions.bool_to_bits, notBelow]

theorem result_frame (state : State) (value : Word) (flags output : BitVec 32) (finish : BitVec 48) :
    X86Execution.RegisterFrame {Register.r15, Register.rflags, Register.rip} state
      (X86Move.putPointer (X86Flags.putFlags (put state 15 (value - (4#64)))
        (X86Flags.mergeFlags flags output)) finish) := by
  simpa [key, Finset.insert_comm] using
    ((X86Execution.put_frame state 15 (value - (4#64))).trans
      (X86Execution.flags_frame _ (X86Flags.mergeFlags flags output))).trans
        (X86Execution.pointer_frame _ finish)

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)

private def mapped (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x3000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .r15 value
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 12288 (0x49#8)
  let memory := memory.insert 12289 (0x83#8)
  let memory := memory.insert 12290 (0xef#8)
  let memory := memory.insert 12291 (4#8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (value : Word) : X86LegacyFetch.Basis (mapped value) where
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

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (Functions.x86_fetch_decode_execute ()).run (mapped value) = .ok () after ∧
      lookup after 15 = some (value - (4#64)) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf =
        some (Functions.bool_to_bits (value.toNat < 4)) := by
  let : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, executed, carry⟩ := fetched_sub4 other vector (mapped value) (origin value) (0x3004#48)
    value (0x200#32) (by change (0x3003#48).toInt + 1 = (0x3004#48).toInt; decide)
    (by change ((mapped value).regs.get? .r15).map (fun word : Word => word) = _; simp [mapped])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, origin, Std.ExtHashMap.getElem_insert])
    (by simp [mapped, origin, Std.ExtHashMap.getElem_insert])
    (by simp [mapped, origin, Std.ExtHashMap.getElem_insert])
    (by simp [mapped, origin])
  refine ⟨_, executed, ?_, ?_⟩
  · rw [X86Move.lookup_putPointer, X86Flags.putFlags_gpr, lookup_put_same]
  · simp only [X86Move.putPointer, X86Flags.putFlags, Std.ExtDHashMap.get?_insert]
    simp [carry]

theorem enough_length (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped 32) = .ok () after ∧
      lookup after 15 = some 28 ∧ (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (0#1) := by
  simpa [Functions.bool_to_bits] using executes other vector 32

theorem short_length_borrows (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameIncrement.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped 3) = .ok () after ∧
      lookup after 15 = some (0xffffffffffffffff#64) ∧
      (after.regs.get? .rflags).map Functions._get_rflagsbits_cf = some (1#1) := by
  simpa [Functions.bool_to_bits] using executes other vector 3

end Controls


end Mettapedia.Machines.TIsa.X86SubImmediate
