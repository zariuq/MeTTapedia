import Mettapedia.Machines.TIsa.X86FetchModel
import Mettapedia.Machines.TIsa.X86PrefixRead
import Mettapedia.Machines.TIsa.X86MovePrefix

/-!
# A fetched register MOV in the pinned Sail x86 model

The theorem follows x86_fetch_decode_execute through architectural mode
selection, RIP, prefix bytes, ModRM and the actual MOV dispatcher. Code-byte
and architectural-state preconditions are explicit. Instruction length follows
from address geometry. The resulting state has exactly the destination and
RIP updates made by the imported handler.

The concrete control changes the ModRM destination bit and rejects the old
answer. This instruction-level result is separate from emitted-program,
ABI, native address linkage and generic compiler refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86InstructionFetch

open _root_.X86Registers X86RegisterRefinement

def movPrefixes : BitVec 52 := Functions._update_prefixes_num
  (Functions._update_prefixes_nxt (0#52) (0x89#8)) (1#4)

theorem packet_opcode : Functions._get_prefixes_nxt movPrefixes = (0x89#8) := by decide
theorem packet_count : Functions._get_prefixes_num movPrefixes = (1#4) := by decide
theorem packet_segment : Functions._get_prefixes_seg movPrefixes = (0#8) := by decide
theorem packet_address : Functions._get_prefixes_adr movPrefixes = (0#8) := by decide
theorem packet_address_size : Functions.select_address_size .Mode_64bit (some movPrefixes) =
    (pure 8 : SailM Int) := rfl

theorem no_sib (source destination : Fin 16) (address16 : Bool) :
    Functions.x86_decode_sib_p (X86RegisterEncoding.modRM source destination) address16 = false := by
  unfold Functions.x86_decode_sib_p
  rw [X86RegisterEncoding.register_mode]
  simp

theorem dispatch_mov [MemoryPrimitives] [OtherOpcodeHandlers] (mode : proc_mode)
    (start next : BitVec 48) (rex modrm sib : BitVec 8) :
    Functions.one_byte_opcode_execute mode start next movPrefixes rex (0x89#8) modrm sib =
      Functions.x86_mov_op_en_mr mode start next movPrefixes rex (0x89#8) modrm sib := rfl

theorem mode64_exact (state : State) (control : Vector (BitVec 64) 7)
    (attributes : Vector (BitVec 16) 6)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1)) :
    (Functions.n64_bit_modep ()).run state = .ok true state := by
  unfold Functions.n64_bit_modep Functions.read_msr
  simp only [run_bind, run_pure]
  rw [readRegister_exact, msrs]
  dsimp only
  rw [readRegister_exact, segments]
  dsimp only
  rw [longMode, codeMode]
  rfl

theorem operation_mode64 (state : State) (control : Vector (BitVec 64) 7)
    (attributes : Vector (BitVec 16) 6)
    (msrs : state.regs.get? .msrs = some control)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (longMode : Functions._get_ia32_eferbits_lma
      (Functions.Mk_ia32_eferbits (Sail.BitVec.truncate control[0]! 12)) = (1#1))
    (codeMode : Functions._get_code_segment_descriptor_attributesbits_l
      (Functions.Mk_code_segment_descriptor_attributesbits attributes[1]!) = (1#1)) :
    (Functions.x86_operation_mode ()).run state = .ok .Mode_64bit state := by
  unfold Functions.x86_operation_mode
  rw [run_bind, mode64_exact state control attributes msrs segments longMode codeMode]
  rfl

theorem read_pointer64 (state : State) (address : BitVec 48)
    (rip : state.regs.get? .rip = some (address.signExtend 64)) :
    (Functions.read_iptr .Mode_64bit).run state = .ok address state := by
  have narrow : Sail.BitVec.truncate (address.signExtend 64) 48 = address := by
    simpa [Functions.sail_mask_signed, Sail.BitVec.length] using X86FetchMemory.narrow_pointer address
  have readRip : (Functions.read_rip ()).run state = .ok address state := by
    unfold Functions.read_rip
    rw [run_bind, readRegister_exact, rip]
    change (pure (Sail.BitVec.truncate (address.signExtend 64) 48) : SailM (BitVec 48)).run state = _
    rw [narrow]
    rfl
  unfold Functions.read_iptr
  rw [run_bind, readRip]
  rfl


local instance : MemoryPrimitives := X86Memory.ordinary

theorem fetch_to_dispatch [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (address opcodeAddress modrmAddress next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (source destination : Fin 16)
    (step1 : address.toInt + 1 = opcodeAddress.toInt)
    (step2 : address.toInt + 2 = modrmAddress.toInt)
    (step3 : modrmAddress.toInt + 1 = next.toInt)
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
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex true source destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat =
      some (X86RegisterEncoding.modRM source destination)) :
    (Functions.x86_fetch_decode_execute ()).run state =
      (Functions.one_byte_opcode_execute .Mode_64bit address next movPrefixes
        (X86RegisterEncoding.rex true source destination) (0x89#8)
        (X86RegisterEncoding.modRM source destination) (0#8)).run state := by
  unfold Functions.x86_fetch_decode_execute Functions.ms Functions.fault
  rw [run_bind, readRegister_exact, status]
  dsimp only
  rw [run_bind, readRegister_exact, fault]
  dsimp only
  change (do
    let mode ← Functions.x86_operation_mode ()
    _ : SailM Unit).run state = _
  rw [run_bind, operation_mode64 state control attributes msrs segments longMode codeMode]
  dsimp only
  rw [run_bind, read_pointer64 state address rip]
  dsimp only
  change (do
    let decoded ← Functions.get_prefixes .Mode_64bit address (0#52) (0#8) 15
    _ : SailM Unit).run state = _
  rw [run_bind, X86PrefixRead.rex_then_opcode state address opcodeAddress
    (address.signExtend 64) attributes true source destination (0#8) step1
    segments application rip prefixByte opcodeByte]
  dsimp only
  change (do
    let modrmPointer ← Functions.add_to_iptr .Mode_64bit address (2#48)
    _ : SailM Unit).run state = _
  rw [run_bind, X86PrefixRead.add_pointer_checked state address (2#48) modrmAddress
    (by simpa using step2)]
  dsimp only
  have opcodePacket : Functions._get_prefixes_nxt
      (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) (0x89#8)) (1#4)) =
        (0x89#8) := by decide
  have needsModrm : Functions.one_byte_opcode_modr_m_p .Mode_64bit (0x89#8) = true := by decide
  have notVex2 : ((0x89#8) == (0xc5#8)) = false := by decide
  have notVex3 : ((0x89#8) == (0xc4#8)) = false := by decide
  have notEvex : ((0x89#8) == (0x62#8)) = false := by decide
  simp only [Functions.Mk_prefixes, opcodePacket, needsModrm, notVex2, notVex3, notEvex,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, ite_true, pure_bind]
  have addressSize : Functions.select_address_size .Mode_64bit
      (some (Functions._update_prefixes_num (Functions._update_prefixes_nxt (0#52) (0x89#8)) (1#4))) =
        (pure 8 : SailM Int) := rfl
  rw [addressSize]
  simp only [pure_bind, Functions.Mk_modr_m, bind_pure, Sail.BitVec.signExtend]
  have readModrm : (Functions.rme08 .Mode_64bit (Int.toNat (8 : Int))
      (modrmAddress.signExtend 64) none 1 ":X").run state =
        .ok (X86RegisterEncoding.modRM source destination) state := by
    exact X86EffectiveFetch.effective_read_exact state modrmAddress
      (address.signExtend 64) attributes (X86RegisterEncoding.modRM source destination)
      segments application rip modrmByte
  rw [run_bind, readModrm]
  dsimp only
  rw [run_bind, X86PrefixRead.add_pointer_checked state modrmAddress (1#48) next
    (by simpa using step3)]
  dsimp only
  simp only [pure_bind, no_sib, Bool.and_false, Bool.false_eq_true, ite_false,
    Functions.Mk_sib, bind_pure]
  rfl

theorem length_from_geometry (address next : BitVec 48)
    (distance : next.toInt = address.toInt + 3) :
    Functions.check_instruction_length address next (0#3) = none := by
  have lower : -(2 ^ 47 : Int) ≤ address.toInt := by simpa using BitVec.le_toInt address
  have upper : address.toInt + 3 < (2 ^ 47 : Int) := by
    rw [← distance]
    simpa using (BitVec.toInt_lt (x := next))
  have finish : BitVec.ofInt 48 (address.toInt + 3) = next := by
    rw [← distance]
    simp
  simpa only [BitVec.ofInt_toInt, finish] using
    X86Move.instruction_length_three address.toInt lower upper

theorem fetch_register64 [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : State) (address opcodeAddress modrmAddress next : BitVec 48)
    (control : Vector (BitVec 64) 7) (attributes : Vector (BitVec 16) 6)
    (source destination : Fin 16)
    (step1 : address.toInt + 1 = opcodeAddress.toInt)
    (step2 : address.toInt + 2 = modrmAddress.toInt)
    (step3 : modrmAddress.toInt + 1 = next.toInt)
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
    (prefixByte : state.mem.get? (address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex true source destination))
    (opcodeByte : state.mem.get? (opcodeAddress.signExtend 52).toNat = some (0x89#8))
    (modrmByte : state.mem.get? (modrmAddress.signExtend 52).toNat =
      some (X86RegisterEncoding.modRM source destination))
    (value : Word) (known : lookup state source = some value)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination value) next) := by
  rw [fetch_to_dispatch state address opcodeAddress modrmAddress next control attributes
    source destination step1 step2 step3 status fault msrs segments longMode codeMode
    application rip prefixByte opcodeByte modrmByte, dispatch_mov]
  exact X86MovePrefix.register64 state source destination value address next movPrefixes
    packet_segment packet_address known quiet (length_from_geometry address next (by omega))

namespace Controls

variable [OtherOpcodeHandlers] [VectorOpcodeHandlers]

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

private def mapped : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .r8 (0x1234#64)
  let registers := registers.insert .r9 (99#64)
  ⟨registers,
    (), (((∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x4d#8)).insert 4097 (0x89#8)).insert
      4098 (0xc1#8), (), 0, #[]⟩

theorem step_mov : (Functions.x86_fetch_decode_execute ()).run mapped =
    .ok () (X86Move.putPointer (put mapped 9 (0x1234#64)) (0x1003#48)) := by
  apply fetch_register64 mapped (0x1000#48) (0x1001#48) (0x1002#48) (0x1003#48)
    control attributes 8 9
  · decide
  · decide
  · decide
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · decide
  · decide
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtHashMap.getElem_insert, X86RegisterEncoding.rex]
  · simp [mapped, Std.ExtHashMap.getElem_insert]
  · simp [mapped, X86RegisterEncoding.modRM]
  · have present : mapped.regs.get? .r8 = some (0x1234#64) := by
      simp [mapped, Std.ExtDHashMap.get?_insert]
    change (mapped.regs.get? .r8).map (fun value : Word => value) = some (0x1234#64)
    rw [present]
    rfl
  · simp [mapped, Std.ExtDHashMap.get?_insert]

theorem wrong_result_refused : (Functions.x86_fetch_decode_execute ()).run mapped ≠
    .ok () (X86Move.putPointer (put mapped 9 (0x1235#64)) (0x1003#48)) := by
  rw [step_mov]
  intro wrong
  have states := (EStateM.Result.ok.inj wrong).2
  have destination := congrArg (fun state : State => lookup state 9) states
  simp only [X86Move.lookup_putPointer, lookup_put_same] at destination
  exact (by decide : (some (0x1234#64)) ≠ some (0x1235#64)) destination

private def altered : State := { mapped with mem := mapped.mem.insert 4098 (0xc0#8) }

theorem altered_step : (Functions.x86_fetch_decode_execute ()).run altered =
    .ok () (X86Move.putPointer (put altered 8 (0x1234#64)) (0x1003#48)) := by
  have sourceKnown : lookup altered 8 = some (0x1234#64) := by
    have present : altered.regs.get? .r8 = some (0x1234#64) := by
      simp [altered, mapped, Std.ExtDHashMap.get?_insert]
    change (altered.regs.get? .r8).map (fun value : Word => value) = some (0x1234#64)
    rw [present]
    rfl
  apply fetch_register64 altered (0x1000#48) (0x1001#48) (0x1002#48) (0x1003#48)
    control attributes 8 8
  all_goals first
    | exact sourceKnown
    | decide
    | simp [altered, mapped, Std.ExtDHashMap.get?_insert, Std.ExtHashMap.getElem_insert,
        X86RegisterEncoding.rex, X86RegisterEncoding.modRM]

theorem altered_modrm_refuses_original_answer :
    (Functions.x86_fetch_decode_execute ()).run altered ≠
      .ok () (X86Move.putPointer (put altered 9 (0x1234#64)) (0x1003#48)) := by
  rw [altered_step]
  intro wrong
  have states := (EStateM.Result.ok.inj wrong).2
  have destination := congrArg (fun state : State => lookup state 9) states
  have before : lookup altered 9 = some (99#64) := by
    have present : altered.regs.get? .r9 = some (99#64) := by
      simp [altered, mapped]
    change (altered.regs.get? .r9).map (fun value : Word => value) = some (99#64)
    rw [present]
    rfl
  rw [X86Move.lookup_putPointer, X86Move.lookup_putPointer, lookup_put_same,
    lookup_put_other _ 8 9 _ (by decide), before] at destination
  exact (by decide : (some (99#64)) ≠ some (0x1234#64)) destination

end Controls


end Mettapedia.Machines.TIsa.X86InstructionFetch
