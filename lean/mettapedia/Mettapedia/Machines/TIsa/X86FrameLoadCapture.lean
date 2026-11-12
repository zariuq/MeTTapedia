import Mettapedia.Machines.TIsa.JsonImport
import Mettapedia.Machines.TIsa.X86FrameLoad
import Mettapedia.Machines.TIsa.X86MovCapture
import Mettapedia.Tools.KernelReflexivity

/-!
# Captured native frame-load helper and its fetched execution

Every aligned eight-byte field of the exported 192-byte runtime frame is
captured at every logical and scratch destination. The capture calls the
actual C helper. FRAME_LOAD is an interval assigned by the capture probe,
not an event emitted internally by that helper; its zero recorded scratch
mask does not certify absence of architectural register effects.

The finite output checks feed the original Sail seven-byte fetch theorem
for arbitrary represented frame contents. Concrete controls load distinct
fuel fields and reject the original answer after changing the field offset.
Compiler-buffer, pointer-layout, surrounding fuel code and ABI composition
remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace Mettapedia.Machines.TIsa.X86FrameLoadCapture

open _root_.X86Registers X86RegisterRefinement
open X86FrameLoad

noncomputable def captured : List Nat × List NativeImage.TemplateSample :=
  tisa_template_capture% "Mettapedia/Machines/TIsa/Models/NativeX86/FrameLoadHelper.json"

def physical (slot : Fin 14) : Fin 16 := X86MovCapture.physical slot

def displacement (field : Fin 24) : BitVec 32 := BitVec.ofNat 32 (8 * field.val)

def expected (destination : Fin 14) (offset : Nat) : List Nat :=
  [(frameRex (physical destination)).toNat, 139, (frameModRM (physical destination)).toNat] ++
    (List.range 4).map (fun index => ((BitVec.ofNat 32 offset).extractLsb' (8 * index) 8).toNat)

def sampleCheck (sample : NativeImage.TemplateSample) : Bool :=
  match sample.inputs with
  | [destination, offset] =>
    if valid : destination < 14 ∧ offset < 192 ∧ offset % 8 = 0 then
      (sample.bytes == expected ⟨destination, valid.1⟩ offset) &&
        (sample.spans == [⟨0, 7, "FRAME_LOAD"⟩]) && (sample.scratchMask == 0)
    else false
  | _ => false

def inventory : List (List Nat) :=
  (List.range 14).flatMap fun destination => (List.range 24).map fun field => [destination, 8 * field]

theorem register_map_exact : captured.1 = (Registers.canonical .x86_64).registers := by kernel_reflexivity
theorem row_count : captured.2.length = 336 := by kernel_reflexivity
theorem row_inventory : captured.2.map NativeImage.TemplateSample.inputs = inventory := by kernel_reflexivity
theorem every_sample_checked : captured.2.all sampleCheck = true := by kernel_reflexivity

theorem sample_present (destination : Fin 14) (field : Fin 24) :
    ∃ sample ∈ captured.2, sample.inputs = [destination.val, 8 * field.val] := by
  apply List.mem_map.mp
  rw [row_inventory]
  simp only [inventory, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨destination.val, destination.isLt, field.val, field.isLt, rfl⟩

theorem checked_bytes (destination : Fin 14) (field : Fin 24) (sample : NativeImage.TemplateSample)
    (member : sample ∈ captured.2) (inputs : sample.inputs = [destination.val, 8 * field.val]) :
    sample.bytes = expected destination (8 * field.val) := by
  have checked := List.all_eq_true.mp every_sample_checked sample member
  rw [sampleCheck, inputs] at checked
  have valid : destination.val < 14 ∧ 8 * field.val < 192 ∧ (8 * field.val) % 8 = 0 :=
    ⟨destination.isLt, by omega, by omega⟩
  simp only [dif_pos valid, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1.1

theorem displacement_byte (destination : Fin 14) (field : Fin 24) (index : Nat) (within : index < 4) :
    (expected destination (8 * field.val))[3 + index]? =
      some (((displacement field).extractLsb' (8 * index) 8).toNat) := by
  interval_cases index <;> rfl

theorem captured_fields (destination : Fin 14) (field : Fin 24) (sample : NativeImage.TemplateSample)
    (member : sample ∈ captured.2) (inputs : sample.inputs = [destination.val, 8 * field.val])
    (state : State) (origin : X86LegacyFetch.Basis state)
    (loaded : X86Execution.codeLoaded state origin.address.toInt sample.bytes) :
    state.mem.get? (origin.address.signExtend 52).toNat = some (frameRex (physical destination)) ∧
      state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x8b#8) ∧
      state.mem.get? (origin.modrmAddress.signExtend 52).toNat = some (frameModRM (physical destination)) ∧
      ∀ index < 4,
        state.mem.get? ((X86Execution.address origin.next.toInt index).signExtend 52).toNat =
          some ((displacement field).extractLsb' (8 * index) 8) := by
  have same := checked_bytes destination field sample member inputs
  rw [same] at loaded
  have at0 : X86Execution.address origin.address.toInt 0 = origin.address := by simp [X86Execution.address]
  have at1 : X86Execution.address origin.address.toInt 1 = origin.opcodeAddress := by
    change BitVec.ofInt 48 (origin.address.toInt + 1) = _
    rw [origin.step1, BitVec.ofInt_toInt]
  have at2 : X86Execution.address origin.address.toInt 2 = origin.modrmAddress := by
    change BitVec.ofInt 48 (origin.address.toInt + 2) = _
    rw [origin.step2, BitVec.ofInt_toInt]
  have nextPosition : origin.next.toInt = origin.address.toInt + 3 := by
    have := origin.step2
    have := origin.step3
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [at0, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded 0 (frameRex (physical destination)).toNat rfl
  · simpa only [at1] using loaded 1 139 rfl
  · simpa only [at2, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded 2 (frameModRM (physical destination)).toNat rfl
  · intro index within
    have shifted : X86Execution.address origin.address.toInt (3 + index) =
        X86Execution.address origin.next.toInt index := by
      unfold X86Execution.address
      rw [nextPosition]
      congr 1
      omega
    simpa only [shifted, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      loaded (3 + index) _ (displacement_byte destination field index within)

local instance : MemoryPrimitives := X86Memory.ordinary

theorem captured_executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 14) (field : Fin 24) (sample : NativeImage.TemplateSample)
    (member : sample ∈ captured.2) (inputs : sample.inputs = [destination.val, 8 * field.val])
    (state : State) (origin : X86LegacyFetch.Basis state) (finish dataAddress : BitVec 48)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (frame value : Word) (flags : BitVec 32)
    (advance : origin.next.toInt + 4 = finish.toInt)
    (dataUpper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (frameKnown : lookup state 7 = some frame)
    (controlKnown : state.regs.get? .ctrs = some controls)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (effective : frame + (displacement field).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (loaded : X86Execution.codeLoaded state origin.address.toInt sample.bytes)
    (dataPresent : ∀ index < 8,
      state.mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state (physical destination) value) finish) := by
  obtain ⟨prefixByte, opcodeByte, modrmByte, codePresent⟩ :=
    captured_fields destination field sample member inputs state origin loaded
  exact fetched_frame other vector state (physical destination) origin finish dataAddress visible controls frame value flags
    (displacement field) advance dataUpper frameKnown controlKnown flagsKnown visibleKnown quiet effective aligned
    prefixByte opcodeByte modrmByte codePresent dataPresent

noncomputable def firstSample : NativeImage.TemplateSample := captured.2[0]'(by rw [row_count]; decide)
def mutateRegister (sample : NativeImage.TemplateSample) : NativeImage.TemplateSample :=
  { sample with bytes := sample.bytes.set 0 76 }
def mutateOffset (sample : NativeImage.TemplateSample) : NativeImage.TemplateSample :=
  { sample with bytes := sample.bytes.set 3 8 }

theorem first_sample_checked : sampleCheck firstSample = true := by kernel_reflexivity
theorem changed_register_byte_refused : sampleCheck (mutateRegister firstSample) = false := by kernel_reflexivity
theorem changed_offset_byte_refused : sampleCheck (mutateOffset firstSample) = false := by kernel_reflexivity

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)
private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def budget : Word := 0x123456789abcdef0#64
private def used : Word := 0x1020304050607080#64

private def mapped (field : Fin 24) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x2000#64)
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .rdi (0x1000#64)
  let registers := registers.insert .r14 (99#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 8192 (0x4c#8)
  let memory := memory.insert 8193 (0x8b#8)
  let memory := memory.insert 8194 (0xb7#8)
  let memory := memory.insert 8195 ((displacement field).extractLsb' 0 8)
  let memory := memory.insert 8196 ((displacement field).extractLsb' 8 8)
  let memory := memory.insert 8197 ((displacement field).extractLsb' 16 8)
  let memory := memory.insert 8198 ((displacement field).extractLsb' 24 8)
  let memory := memory.insert 4256 (budget.extractLsb' 0 8)
  let memory := memory.insert 4257 (budget.extractLsb' 8 8)
  let memory := memory.insert 4258 (budget.extractLsb' 16 8)
  let memory := memory.insert 4259 (budget.extractLsb' 24 8)
  let memory := memory.insert 4260 (budget.extractLsb' 32 8)
  let memory := memory.insert 4261 (budget.extractLsb' 40 8)
  let memory := memory.insert 4262 (budget.extractLsb' 48 8)
  let memory := memory.insert 4263 (budget.extractLsb' 56 8)
  let memory := memory.insert 4264 (used.extractLsb' 0 8)
  let memory := memory.insert 4265 (used.extractLsb' 8 8)
  let memory := memory.insert 4266 (used.extractLsb' 16 8)
  let memory := memory.insert 4267 (used.extractLsb' 24 8)
  let memory := memory.insert 4268 (used.extractLsb' 32 8)
  let memory := memory.insert 4269 (used.extractLsb' 40 8)
  let memory := memory.insert 4270 (used.extractLsb' 48 8)
  let memory := memory.insert 4271 (used.extractLsb' 56 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (field : Fin 24) : X86LegacyFetch.Basis (mapped field) where
  address := 0x2000#48
  opcodeAddress := 0x2001#48
  modrmAddress := 0x2002#48
  next := 0x2003#48
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

private theorem loaded (field : Fin 24) :
    X86Execution.codeLoaded (mapped field) 8192 (expected 12 (8 * field.val)) := by
  change X86Execution.codeLoaded (mapped field) 8192
    [76, 139, 183, ((displacement field).extractLsb' 0 8).toNat,
      ((displacement field).extractLsb' 8 8).toNat, ((displacement field).extractLsb' 16 8).toNat,
      ((displacement field).extractLsb' 24 8).toNat]
  intro index byte present
  have bounded : index < 7 := (List.getElem?_eq_some_iff.mp present).choose
  interval_cases index <;> simp_all [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]
  all_goals apply BitVec.eq_of_toNat_eq; simp [← present]

private theorem actual_run (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (field : Fin 24) (dataAddress : BitVec 48) (value : Word)
    (upper : dataAddress.toInt + 8 ≤ (2 ^ 47 : Int))
    (effective : (0x1000#64) + (displacement field).signExtend 64 = dataAddress.signExtend 64)
    (aligned : dataAddress &&& (7#48) = (0#48))
    (present : ∀ index < 8,
      (mapped field).mem.get? ((X86Execution.address dataAddress.toInt index).signExtend 52).toNat =
        some (value.extractLsb' (8 * index) 8)) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped field) =
      .ok () (X86Move.putPointer (put (mapped field) 14 value) (0x2007#48)) := by
  obtain ⟨sample, member, inputs⟩ := sample_present 12 field
  have bytes := checked_bytes 12 field sample member inputs
  have code : X86Execution.codeLoaded (mapped field) 8192 sample.bytes := by rw [bytes]; exact loaded field
  have frameKnown : lookup (mapped field) 7 = some (0x1000#64) := by
    change ((mapped field).regs.get? .rdi).map (fun value : Word => value) = _
    simp [mapped, Std.ExtDHashMap.get?_insert]
  have result := captured_executes other vector 12 field sample member inputs (mapped field) (origin field)
    (0x2007#48) dataAddress visible controls (0x1000#64) value (0x200#32)
    (by change (8195 : Int) + 4 = (8199 : Int); decide) upper
    frameKnown (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    (by simp [mapped, Std.ExtDHashMap.get?_insert]) (by simp [mapped, Std.ExtDHashMap.get?_insert])
    effective aligned code present
  simpa only [show physical 12 = (14 : Fin 16) from rfl] using result

theorem captured_budget_load (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped 20) =
      .ok () (X86Move.putPointer (put (mapped 20) 14 budget) (0x2007#48)) := by
  apply actual_run other vector 20 (0x10a0#48) budget (by decide) (by decide) (by decide)
  intro index within
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem captured_used_load (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped 21) =
      .ok () (X86Move.putPointer (put (mapped 21) 14 used) (0x2007#48)) := by
  apply actual_run other vector 21 (0x10a8#48) used (by decide) (by decide) (by decide)
  intro index within
  interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]

theorem changed_field_refuses_budget_answer (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬∃ after, (Functions.x86_fetch_decode_execute ()).run (mapped 21) = .ok () after ∧ lookup after 14 = some budget := by
  let : OtherOpcodeHandlers := linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rintro ⟨after, executed, wrong⟩
  have same := (EStateM.Result.ok.inj ((captured_used_load other vector).symm.trans executed)).2
  rw [← same, X86Move.lookup_putPointer, lookup_put_same] at wrong
  exact (by decide : used ≠ budget) (Option.some.inj wrong)

end Controls
end Mettapedia.Machines.TIsa.X86FrameLoadCapture

#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.captured_executes
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.changed_offset_byte_refused
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.Controls.captured_budget_load
#print axioms Mettapedia.Machines.TIsa.X86FrameLoadCapture.Controls.changed_field_refuses_budget_answer
