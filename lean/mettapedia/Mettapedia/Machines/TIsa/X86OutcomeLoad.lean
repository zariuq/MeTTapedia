import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.X86UnconditionalJump

/-!
# Fetched EAX immediate loads for native outcome handlers

The original MOV immediate handler and complete five-byte B8 fetch establish
zero extension of the immediate into RAX, exact RIP and register-only framing.
The full-fetch controls use 0xffffffff and reject sign extension into RAX.
No assumption about the old RAX value or a handler execution is required.

The whole failure-handler, public epilogue, ABI and emitter refinements are
separate composition obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86OutcomeLoad
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

def packet : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) (0xb8#8)) (0#4)

theorem narrowed (value : BitVec 32) :
    Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32 = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp [Sail.BitVec.truncate, within]

theorem handler (state : State) (start immediateAddress finish : BitVec 48)
    (attributes : Vector (BitVec 16) 6) (pointer : Word) (value : BitVec 32)
    (advance : immediateAddress.toInt + 4 = finish.toInt)
    (length : Functions.check_instruction_length start finish (0#3) = none)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (quiet : state.regs.get? .log_register_writes = some false)
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address immediateAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    (Functions.x86_mov_op_en_oi .Mode_64bit start immediateAddress packet
      (0#8) (0xb8#8) (0#8) (0#8)).run state =
      .ok () (X86Move.putPointer (put state 0 (value.zeroExtend 64)) finish) := by
  have upper : immediateAddress.toInt + 4 ≤ (2 ^ 47 : Int) := by
    have := BitVec.toInt_lt (x := finish)
    omega
  unfold Functions.x86_mov_op_en_oi
  dsimp only
  rw [show (((176 : Int) ≤b Sail.BitVec.toNatInt (0xb8#8)) &&
      ((Sail.BitVec.toNatInt (0xb8#8) ≤b (183 : Int)) : Bool)) = false from rfl]
  rw [show Functions.select_operand_size .Mode_64bit false (0#8) false packet false false false =
      (pure 4 : SailM Int) from rfl, run_bind, run_pure]
  dsimp only
  rw [show Functions.select_address_size .Mode_64bit (some packet) = (pure 8 : SailM Int) from rfl]
  simp only [pure_bind, show Int.toNat (4 : Int) = 4 from rfl,
    show Int.toNat (8 : Int) = 8 from rfl, Sail.BitVec.signExtend]
  rw [run_bind, X86FrameStore.read_dword state immediateAddress pointer attributes value upper segments application rip present]
  dsimp only
  rw [show Functions.bits_of_int 4 48 = (4#48) from rfl,
    run_bind, X86PrefixRead.add_pointer_checked state immediateAddress (4#48) finish (by simpa using advance)]
  dsimp only
  rw [length]
  simp only [show Functions.is_some (none : Option Int) = false from rfl, Bool.false_eq_true, ite_false]
  change (do
    Functions.wr32 (0#4) (Sail.BitVec.truncate (Sail.BitVec.truncate (value.zeroExtend 128) 64) 32)
    Functions.write_iptr .Mode_64bit finish).run state = _
  have write := wr32_exact state (0 : Fin 16) value quiet
  change (Functions.wr32 (0#4) value).run state = .ok () (put state 0 (value.zeroExtend 64)) at write
  rw [narrowed, run_bind, write]
  change (Functions.write_iptr .Mode_64bit finish).run (put state 0 (value.zeroExtend 64)) = _
  exact X86Move.write_pointer64 _ finish
    ((put_other_register state (0 : Fin 16) (value.zeroExtend 64) .log_register_writes (by decide)).trans quiet)

theorem opcode_scan (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some (0xb8#8)) :
    (Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15).run state =
      .ok (packet, (0#8)) state := by
  rw [X86Prefix.unfold_original]
  unfold Functions.get_prefixes_body
  rw [X86PrefixRead.code_address_size]
  change (do
    let byte ← Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X"
    _ : SailM (BitVec 52 × BitVec 8)).run state = _
  rw [run_bind, X86EffectiveFetch.effective_read_exact state address pointer attributes (0xb8#8)
    segments application rip present]
  rfl

theorem fetch_to_handler [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (origin : X86LegacyFetch.Basis state)
    (opcodeByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0xb8#8)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (OtherOpcodeHandlers.x86_mov_op_en_oi .Mode_64bit origin.address origin.opcodeAddress
        packet (0#8) (0xb8#8) (0#8) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, origin.status]
  dsimp only
  rw [run_bind, readRegister_exact, origin.fault]
  dsimp only
  change (do let mode ← Functions.x86_operation_mode (); _ : SailM Unit).run state = _
  rw [run_bind, X86InstructionFetch.operation_mode64 state origin.control origin.attributes origin.msrs
    origin.segments origin.longMode origin.codeMode]
  dsimp only
  rw [run_bind, X86InstructionFetch.read_pointer64 state origin.address origin.rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit origin.address (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, opcode_scan state origin.address (origin.address.signExtend 64) origin.attributes
    origin.segments origin.application origin.rip opcodeByte]
  dsimp only
  change (do let pointer ← Functions.add_to_iptr .Mode_64bit origin.address (1#48); _ : SailM Unit).run state = _
  rw [run_bind, X86PrefixRead.add_pointer_checked state origin.address (1#48) origin.opcodeAddress
    (by simpa using origin.step1)]
  dsimp only
  simp only [pure_bind, Functions.Mk_modr_m, Functions.Mk_sib, bind_pure]
  rfl

theorem fetched_eax (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (origin : X86LegacyFetch.Basis state) (finish : BitVec 48) (value : BitVec 32)
    (advance : origin.opcodeAddress.toInt + 4 = finish.toInt)
    (quiet : state.regs.get? .log_register_writes = some false)
    (opcodeByte : state.mem.get? (origin.address.signExtend 52).toNat = some (0xb8#8))
    (present : ∀ index < 4,
      state.mem.get? ((X86Execution.address origin.opcodeAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state 0 (value.zeroExtend 64)) finish) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [fetch_to_handler state origin opcodeByte]
  change (Functions.x86_mov_op_en_oi .Mode_64bit origin.address origin.opcodeAddress
    packet (0#8) (0xb8#8) (0#8) (0#8)).run state = _
  apply handler state origin.address origin.opcodeAddress finish origin.attributes (origin.address.signExtend 64)
    value advance
  · apply X86FrameLoad.length_from_distance _ _ 5 (by decide)
    have := origin.step1
    omega
  · exact origin.segments
  · exact origin.application
  · exact origin.rip
  · exact quiet
  · exact present

theorem result_frame (state : State) (value : BitVec 32) (finish : BitVec 48) :
    X86Execution.RegisterFrame {.rax, .rip} state (X86Move.putPointer (put state 0 (value.zeroExtend 64)) finish) := by
  simpa [key] using (X86Execution.put_frame state 0 (value.zeroExtend 64)).trans
    (X86Execution.pointer_frame _ finish)

namespace Controls
private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def cells : List (Nat × BitVec 8) :=
  [(4096, 0xb8#8), (4097, 0xff#8), (4098, 0xff#8), (4099, 0xff#8), (4100, 0xff#8), (8192, 42#8)]
private def before : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .rax (0xaaaaaaaabbbbbbbb#64)
  let registers := registers.insert .log_register_writes false
  ⟨registers, (), Std.ExtHashMap.ofList cells, (), 0, #[]⟩
private theorem cell (key : Nat) (byte : BitVec 8) (present : (key, byte) ∈ cells) :
    before.mem.get? key = some byte := Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (by decide) present
private def origin : X86LegacyFetch.Basis before where
  address := 0x1000#48
  opcodeAddress := 0x1001#48
  modrmAddress := 0x1002#48
  next := 0x1003#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before, Std.ExtDHashMap.get?_insert]
  fault := by simp [before, Std.ExtDHashMap.get?_insert]
  msrs := by simp [before, Std.ExtDHashMap.get?_insert]
  segments := by simp [before, Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before, Std.ExtDHashMap.get?_insert]
  rip := by simp [before, Std.ExtDHashMap.get?_insert]

theorem zero_extends (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run before = .ok () after ∧
      lookup after 0 = some (0x00000000ffffffff#64) ∧ after.mem = before.mem := by
  have run := fetched_eax other vector before origin (0x1005#48) (0xffffffff#32)
    (by decide) (by simp [before]) (cell 4096 (0xb8#8) (by decide)) (by
      intro index within
      interval_cases index
      · exact cell 4097 (0xff#8) (by decide)
      · exact cell 4098 (0xff#8) (by decide)
      · exact cell 4099 (0xff#8) (by decide)
      · exact cell 4100 (0xff#8) (by decide))
  refine ⟨_, run, ?_, rfl⟩
  rw [X86Move.lookup_putPointer, lookup_put_same]
  rfl

theorem sign_extension_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (after : State)
    (wrong : lookup after 0 = some (0xffffffffffffffff#64)) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run before ≠ .ok () after := by
  intro observed
  obtain ⟨proved, run, value, _⟩ := zero_extends other vector
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at value
  contradiction

end Controls
end Mettapedia.Machines.TIsa.X86OutcomeLoad

#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.fetched_eax
#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.result_frame
#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.Controls.zero_extends
#print axioms Mettapedia.Machines.TIsa.X86OutcomeLoad.Controls.sign_extension_refused
