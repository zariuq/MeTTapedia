import Mettapedia.Machines.TIsa.X86EscapeFetch

/-!
# Complete fetched near JMP in the original Sail model

The original E9 handler reads signed disp32, checks the five-byte length,
performs canonical-address additions and writes RIP. The complete fetch
contract derives its inputs from architectural state and code bytes through
the original prefix scanner and one-byte dispatcher. Memory and other
registers are preserved. Image placement and compiler composition remain
separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section
variable [X86Registers.MemoryPrimitives]
tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/JumpFunctions.lean.inc"
  sha256 "da6b8f585704f00469129f10f9741363fcce4113114c901b2bbea2ebc3abc58b"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]
end

namespace Mettapedia.Machines.TIsa.X86UnconditionalJump

open _root_.X86Registers X86RegisterRefinement X86PrefixRead

local instance : MemoryPrimitives := X86Memory.ordinary

theorem truncate_displacement (displacement : BitVec 32) :
    Sail.BitVec.truncate (displacement.signExtend 64) 32 = displacement := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have wide : index < 64 := by omega
  simp [Sail.BitVec.truncate, within, wide, BitVec.getElem_signExtend]

theorem handler (state : State) (start base finish target : BitVec 48) (prefixes : BitVec 52)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (displacement : BitVec 32)
    (first : base.toInt = start.toInt + 1)
    (advance : base.toInt + 4 = finish.toInt)
    (jump : target.toInt = finish.toInt + displacement.toInt)
    (addressOverride : Functions._get_prefixes_adr prefixes = (0#8))
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    (Functions.x86_near_jmp_op_en_d .Mode_64bit start base prefixes (0#8) (0xe9#8) (0#8) (0#8)).run state =
      .ok () (X86Move.putPointer state target) := by
  have addressSize : Functions.select_address_size .Mode_64bit (some prefixes) = (pure 8 : SailM Int) := by
    simp [Functions.select_address_size, Functions.in_64bit_mode, addressOverride]
  have codeUpper : base.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := finish)
    omega
  have length : Functions.check_instruction_length start finish (0#3) = none :=
    X86FrameLoad.length_from_distance start finish 5 (by decide) (by omega)
  unfold Functions.x86_near_jmp_op_en_d
  rw [show ((0xe9#8) == (0xeb#8)) = false from rfl]
  dsimp only
  rw [X86NearBranch.operand_size32]
  simp only [pure_bind]
  rw [check_range_ok 0 4 4 (by decide) (by decide)]
  simp only [pure_bind, addressSize, bind_assoc]
  rw [show Int.toNat (4 : Int) = 4 from rfl, show Int.toNat (8 : Int) = 8 from rfl,
    show Sail.BitVec.signExtend base 64 = base.signExtend 64 from rfl,
    run_bind, X86ReadWords.signed_displacement_exact state base attributes pointer displacement codeUpper
      segments application rip present]
  dsimp only
  rw [truncate_displacement, run_bind,
    add_pointer_checked state base (Functions.bits_of_int 4 48) finish
      (by change base.toInt + 4 = finish.toInt; exact advance)]
  dsimp only
  rw [length, if_neg (by decide : ¬Functions.is_some (none : Option Int) = true)]
  rw [run_bind, add_pointer_checked state finish (Sail.BitVec.signExtend displacement 48) target
    (by rw [show Sail.BitVec.signExtend displacement 48 = displacement.signExtend 48 from rfl,
      BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 48)]; omega)]
  dsimp only
  exact X86Move.write_pointer64 state target quiet

def packet : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) (0xe9#8)) (0#4)

theorem opcode_scan (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (0xe9#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15).run state =
      .ok (packet, (0#8)) state := by
  rw [X86Prefix.unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes (0xe9#8)
    segments application rip present]
  rfl

theorem fetch_to_handler [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (address opcodeAddress : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (advance : address.toInt + 1 = opcodeAddress.toInt)
    (status : state.regs.get? .ms_reg = some false)
    (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (address.signExtend 64))
    (opcodeByte : state.mem.get? (address.signExtend 52).toNat = some (0xe9#8)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.x86_near_jmp_op_en_d .Mode_64bit address opcodeAddress
        packet (0#8) (0xe9#8) (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state address rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, opcode_scan state address (address.signExtend 64) attributes
    segments application rip opcodeByte]
  dsimp only
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit address (1#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state address (1#48) opcodeAddress (by simpa using advance)]
  dsimp only
  simp only [pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rfl

noncomputable abbrev linked (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_near_jmp_op_en_d := Functions.x86_near_jmp_op_en_d }

theorem fetched_jump (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (start base finish target : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6) (displacement : BitVec 32)
    (first : start.toInt + 1 = base.toInt)
    (advance : base.toInt + 4 = finish.toInt)
    (jump : target.toInt = finish.toInt + displacement.toInt)
    (status : state.regs.get? .ms_reg = some false)
    (fault : state.regs.get? .fault_reg = some false)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1))
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (start.signExtend 64))
    (quiet : state.regs.get? .log_register_writes = some false)
    (opcodeByte : state.mem.get? (start.signExtend 52).toNat = some (0xe9#8))
    (displacementBytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok () (X86Move.putPointer state target) := by
  let : OtherOpcodeHandlers := linked other
  let : VectorOpcodeHandlers := vector
  rw [fetch_to_handler state start base control attributes first status fault msrs segments
    longMode codeMode application rip opcodeByte]
  change (Functions.x86_near_jmp_op_en_d .Mode_64bit start base packet (0#8) (0xe9#8) (0#8) (0#8)).run state = _
  exact handler state start base finish target packet attributes (start.signExtend 64) displacement
    (by omega) advance jump (by rfl) segments application rip quiet displacementBytes

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped (displacement : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x6000#64)
  let registers := registers.insert .log_register_writes false
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 24576 (0xe9#8)
  let memory := memory.insert 24577 (displacement.extractLsb' 0 8)
  let memory := memory.insert 24578 (displacement.extractLsb' 8 8)
  let memory := memory.insert 24579 (displacement.extractLsb' 16 8)
  let memory := memory.insert 24580 (displacement.extractLsb' 24 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private theorem run_jump (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (displacement : BitVec 32) (target : BitVec 48)
    (jump : target.toInt = (24581 : Int) + displacement.toInt) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped displacement) =
      .ok () (X86Move.putPointer (mapped displacement) target) := by
  apply fetched_jump other vector (mapped displacement) (0x6000#48) (0x6001#48) (0x6005#48) target
    control attributes displacement (by decide) (by decide) jump
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by decide) (by decide)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped]) (by simp [mapped, Std.ExtHashMap.getElem_insert])
  intro index within
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem forward_jump (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped (16#32)) =
      .ok () (X86Move.putPointer (mapped (16#32)) (0x6015#48)) :=
  run_jump other vector (16#32) (0x6015#48) (by decide)

theorem backward_jump (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped (0xfffffff0#32)) =
      .ok () (X86Move.putPointer (mapped (0xfffffff0#32)) (0x5ff5#48)) :=
  run_jump other vector (0xfffffff0#32) (0x5ff5#48) (by decide)

theorem changed_displacement_refuses_forward_target (other : OtherOpcodeHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped (0xfffffff0#32)) ≠
      .ok () (X86Move.putPointer (mapped (0xfffffff0#32)) (0x6015#48)) := by
  rw [backward_jump other vector]
  intro wrong
  have same := congrArg (fun state : State => state.regs.get? .rip) (EStateM.Result.ok.inj wrong).2
  simp [X86Move.putPointer] at same

end Controls
end Mettapedia.Machines.TIsa.X86UnconditionalJump

#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.handler
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.fetched_jump
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.Controls.backward_jump
#print axioms Mettapedia.Machines.TIsa.X86UnconditionalJump.Controls.changed_displacement_refuses_forward_target
