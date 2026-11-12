import Mettapedia.Machines.TIsa.X86TwoByteDispatch

/-!
# Complete fetch of admitted 0F conditional branches

Architectural state and the actual six code bytes drive the original prefix
scanner, outer fetch, one-byte escape dispatch, complete two-byte dispatch
and signed-displacement handler. No execution property is included in the
input facts. Other handlers remain arbitrary function data. The result
updates only RIP; native image/layout and structured-control composition
remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86EscapeFetch

open _root_.X86Registers X86RegisterRefinement X86PrefixRead
open X86TwoByteDispatch

local instance : MemoryPrimitives := X86Memory.ordinary

theorem escape_scan (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (0x0f#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15).run state =
      .ok (escapePacket, (0#8)) state := by
  rw [X86Prefix.unfold_original]
  unfold Functions.get_prefixes_body
  rw [code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes (0x0f#8)
    segments application rip present]
  rfl

theorem fetch_to_escape [OtherOpcodeHandlers] [VectorOpcodeHandlers]
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
    (escapeByte : state.mem.get? (address.signExtend 52).toNat = some (0x0f#8)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.two_byte_opcode_decode_and_execute .Mode_64bit address opcodeAddress
        escapePacket (0#8) (0x0f#8)).run state := by
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
  rw [run_bind, escape_scan state address (address.signExtend 64) attributes
    segments application rip escapeByte]
  dsimp only
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit address (1#48); _ : SailM Unit).run state = _
  rw [run_bind, add_pointer_checked state address (1#48) opcodeAddress (by simpa using advance)]
  dsimp only
  simp only [pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rfl

noncomputable abbrev linked (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  { other with two_byte_opcode_decode_and_execute :=
      @Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary other extra }

theorem fetched_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (condition : X86BranchCondition.Condition)
    (state : State) (address opcodeAddress base finish target : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (flags : BitVec 32) (displacement : BitVec 32)
    (step1 : address.toInt + 1 = opcodeAddress.toInt)
    (step2 : opcodeAddress.toInt + 1 = base.toInt)
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
    (rip : state.regs.get? .rip = some (address.signExtend 64))
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (escapeByte : state.mem.get? (address.signExtend 52).toNat = some (0x0f#8))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat =
      some (X86BranchCondition.opcode condition))
    (displacementBytes : ∀ index < 4,
      state.mem.get? ((X86Execution.address base.toInt index).signExtend 52).toNat =
        some (displacement.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer state (if X86BranchCondition.value condition flags then target else finish)) := by
  let : OtherOpcodeHandlers := linked other extra
  let : VectorOpcodeHandlers := vector
  rw [fetch_to_escape state address opcodeAddress control attributes step1 status fault msrs segments
    longMode codeMode application rip escapeByte]
  change (@Functions.two_byte_opcode_decode_and_execute X86Memory.ordinary other extra
    .Mode_64bit address opcodeAddress escapePacket (0#8) (0x0f#8)).run state = _
  rw [@X86TwoByteDispatch.decode_to_branch other extra condition state address opcodeAddress base
    (0#8) attributes (address.signExtend 64) step2 segments application rip opcodeByte]
  exact X86NearBranch.handler condition state address base finish target escapePacket (0#8)
    attributes (address.signExtend 64) flags displacement (by omega) advance jump (by rfl)
    segments application rip flagsKnown quiet displacementBytes

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped (condition : X86BranchCondition.Condition) (flags : BitVec 32)
    (displacement : BitVec 32) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x5000#64)
  let registers := registers.insert .rflags flags
  let registers := registers.insert .log_register_writes false
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 20480 (0x0f#8)
  let memory := memory.insert 20481 (X86BranchCondition.opcode condition)
  let memory := memory.insert 20482 (displacement.extractLsb' 0 8)
  let memory := memory.insert 20483 (displacement.extractLsb' 8 8)
  let memory := memory.insert 20484 (displacement.extractLsb' 16 8)
  let memory := memory.insert 20485 (displacement.extractLsb' 24 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private theorem run_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (condition : X86BranchCondition.Condition)
    (flags : BitVec 32) (displacement : BitVec 32) (target : BitVec 48)
    (jump : target.toInt = (20486 : Int) + displacement.toInt) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped condition flags displacement) =
      .ok () (X86Move.putPointer (mapped condition flags displacement)
        (if X86BranchCondition.value condition flags then target else (0x5006#48))) := by
  apply fetched_branch other extra vector condition (mapped condition flags displacement)
    (0x5000#48) (0x5001#48) (0x5002#48) (0x5006#48) target control attributes flags displacement
    (by decide) (by decide) (by decide) jump
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by decide) (by decide)
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped])
    (by simp [mapped, Std.ExtHashMap.getElem_insert]) (by simp [mapped, Std.ExtHashMap.getElem_insert])
  intro index within
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem forward_taken (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .aboveEqual (0#32) (16#32)) =
      .ok () (X86Move.putPointer (mapped .aboveEqual (0#32) (16#32)) (0x5016#48)) :=
  run_branch other extra vector .aboveEqual (0#32) (16#32) (0x5016#48) (by decide)

theorem backward_taken (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .aboveEqual (0#32) (0xfffffff0#32)) =
      .ok () (X86Move.putPointer (mapped .aboveEqual (0#32) (0xfffffff0#32)) (0x4ff6#48)) :=
  run_branch other extra vector .aboveEqual (0#32) (0xfffffff0#32) (0x4ff6#48) (by decide)

theorem falls_through (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .aboveEqual (1#32) (16#32)) =
      .ok () (X86Move.putPointer (mapped .aboveEqual (1#32) (16#32)) (0x5006#48)) :=
  run_branch other extra vector .aboveEqual (1#32) (16#32) (0x5016#48) (by decide)

theorem above_excludes_equality (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .above (0x40#32) (16#32)) =
      .ok () (X86Move.putPointer (mapped .above (0x40#32) (16#32)) (0x5006#48)) :=
  run_branch other extra vector .above (0x40#32) (16#32) (0x5016#48) (by decide)

theorem above_taken (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .above (0#32) (16#32)) =
      .ok () (X86Move.putPointer (mapped .above (0#32) (16#32)) (0x5016#48)) :=
  run_branch other extra vector .above (0#32) (16#32) (0x5016#48) (by decide)

theorem changed_displacement_refuses_forward_target (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .aboveEqual (0#32) (0xfffffff0#32)) ≠
      .ok () (X86Move.putPointer (mapped .aboveEqual (0#32) (0xfffffff0#32)) (0x5016#48)) := by
  rw [backward_taken other extra vector]
  intro wrong
  have same := congrArg (fun state : State => state.regs.get? .rip) (EStateM.Result.ok.inj wrong).2
  simp [X86Move.putPointer] at same

theorem changed_condition_refuses_taken_target (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped .below (0#32) (16#32)) ≠
      .ok () (X86Move.putPointer (mapped .below (0#32) (16#32)) (0x5016#48)) := by
  rw [run_branch other extra vector .below (0#32) (16#32) (0x5016#48) (by decide)]
  intro wrong
  have same := congrArg (fun state : State => state.regs.get? .rip) (EStateM.Result.ok.inj wrong).2
  simp [X86Move.putPointer, show X86BranchCondition.value .below (0#32) = false from rfl] at same

end Controls
theorem rex_escape_scan (state : State) (start escape : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (wide : Bool) (source destination : Fin 16)
    (advance : start.toInt + 1 = escape.toInt)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (rexByte : state.mem.get? (start.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (escapeByte : state.mem.get? (escape.signExtend 52).toNat = some (0x0f#8)) :
    (Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15).run state =
      .ok (X86LegacyFetch.packet (0x0f#8), X86RegisterEncoding.rex wide source destination) state := by
  rw [X86PrefixRead.rex_advances_scan state start escape pointer attributes wide source destination (0#8) 14 advance
    (by decide) (by decide) segments application rip rexByte]
  exact X86LegacyFetch.opcode_scan_stops (0x0f#8) (by decide) (by decide) state escape pointer attributes
    (X86RegisterEncoding.rex wide source destination) 13 segments application rip escapeByte

theorem fetch_to_rex_escape [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (start escape opcodeAddress : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (wide : Bool) (source destination : Fin 16)
    (step1 : start.toInt + 1 = escape.toInt) (step2 : start.toInt + 2 = opcodeAddress.toInt)
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
    (rexByte : state.mem.get? (start.signExtend 52).toNat =
      some (X86RegisterEncoding.rex wide source destination))
    (escapeByte : state.mem.get? (escape.signExtend 52).toNat = some (0x0f#8)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.two_byte_opcode_decode_and_execute .Mode_64bit start opcodeAddress
        (X86LegacyFetch.packet (0x0f#8)) (X86RegisterEncoding.rex wide source destination) (0x0f#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state start rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit start (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, rex_escape_scan state start escape (start.signExtend 64) attributes wide source destination
    step1 segments application rip rexByte escapeByte]
  dsimp only
  simp only [Functions.Mk_prefixes, X86LegacyFetch.packet_count]
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit start (2#48); _ : SailM Unit).run state = _
  rw [run_bind, X86PrefixRead.add_pointer_checked state start (2#48) opcodeAddress (by simpa using step2)]
  dsimp only
  simp only [X86LegacyFetch.packet_opcode,
    show ((0x0f#8) == (0xc5#8)) = false from rfl,
    show ((0x0f#8) == (0xc4#8)) = false from rfl,
    show ((0x0f#8) == (0x62#8)) = false from rfl,
    show Functions.one_byte_opcode_modr_m_p .Mode_64bit (0x0f#8) = false from rfl,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, pure_bind]
  rw [X86LegacyFetch.packet_address_size]
  simp only [pure_bind, Bool.false_eq_true, ite_false,
    Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rfl

end Mettapedia.Machines.TIsa.X86EscapeFetch

#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.fetch_to_escape
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.fetched_branch
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.forward_taken
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.above_excludes_equality
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.changed_displacement_refuses_forward_target
#print axioms Mettapedia.Machines.TIsa.X86EscapeFetch.Controls.changed_condition_refuses_taken_target
