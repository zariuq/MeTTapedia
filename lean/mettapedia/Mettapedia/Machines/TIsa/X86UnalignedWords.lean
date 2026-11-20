import Mettapedia.Machines.TIsa.X86Alignment
import Mettapedia.Machines.TIsa.X86DataStore

/-!
# Unaligned word data accesses in the original x86 model

The shared load/store contracts accept the actual alignment-check condition:
checking disabled or the effective address aligned. Concrete controls set
CR0.AM and user privilege while clearing AC, then fetch the seven-byte MOV
instructions at an unaligned data address. Full-word loads retain high bits;
stores produce exactly the declared four- or eight-byte update. The four-byte
store keeps its suffix, and a control rejects an eight-byte effect. Enabled checking
rejects this successful-entry profile; no fault outcome is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86UnalignedWords
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

namespace Load

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
private def visible : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)

private def mapped (destination : Fin 16) (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rsi (0x2001#64)
  let registers := registers.insert .r10 (0xffffffffffffffff#64)
  let registers := registers.insert .r11 (33#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (loadRex true destination 6)
  let memory := memory.insert 4097 (0x8b#8)
  let memory := memory.insert 4098 (loadModRM destination 6)
  let memory := memory.insert 4099 0
  let memory := memory.insert 4100 0
  let memory := memory.insert 4101 0
  let memory := memory.insert 4102 0
  let memory := memory.insert 8193 (value.extractLsb' 0 8)
  let memory := memory.insert 8194 (value.extractLsb' 8 8)
  let memory := memory.insert 8195 (value.extractLsb' 16 8)
  let memory := memory.insert 8196 (value.extractLsb' 24 8)
  let memory := memory.insert 8197 (value.extractLsb' 32 8)
  let memory := memory.insert 8198 (value.extractLsb' 40 8)
  let memory := memory.insert 8199 (value.extractLsb' 48 8)
  let memory := memory.insert 8200 (value.extractLsb' 56 8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (destination : Fin 16) (value : Word) :
    X86LegacyFetch.Basis (mapped destination value) where
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

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (value : Word) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped destination value) =
      .ok () (X86Move.putPointer (put (mapped destination value) destination value) (0x1007#48)) := by
  apply X86QwordLoad.fetched_qword_checked other vector (mapped destination value) destination 6 (by decide) (by decide)
    (origin destination value) (0x1007#48) (0x2001#48) visible controls (0x2001#64) value (0x200#32) (0#32)
  · change (0x1003#48).toInt + 4 = (0x1007#48).toInt
    decide
  · decide
  · change ((mapped destination value).regs.get? .rsi).map (fun word : Word => word) = _
    simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · decide
  · decide
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · simp [origin, mapped, Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [origin, mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [mapped, X86Execution.address, Std.ExtHashMap.getElem_insert]
theorem high_word_preserved (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x8000000000000001#64)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) = some (0x8000000000000001#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  simp [X86Move.lookup_putPointer,lookup_put_same]

theorem low_word_truncation_rejected (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x8000000000000001#64)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) ≠ some (1#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [high_word_preserved]
  decide

end Load

namespace Store

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
private def visible : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)

private def mapped (destination : Fin 16) (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rsi (0x2001#64)
  let registers := registers.insert .r10 value
  let registers := registers.insert .r11 (33#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (loadRex true destination 6)
  let memory := memory.insert 4097 (0x89#8)
  let memory := memory.insert 4098 (loadModRM destination 6)
  let memory := memory.insert 4099 0
  let memory := memory.insert 4100 0
  let memory := memory.insert 4101 0
  let memory := memory.insert 4102 0
  let memory := memory.insert 8193 (0xaa#8)
  let memory := memory.insert 8194 (0xaa#8)
  let memory := memory.insert 8195 (0xaa#8)
  let memory := memory.insert 8196 (0xaa#8)
  let memory := memory.insert 8197 (0xaa#8)
  let memory := memory.insert 8198 (0xaa#8)
  let memory := memory.insert 8199 (0xaa#8)
  let memory := memory.insert 8200 (0xaa#8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (destination : Fin 16) (value : Word) :
    X86LegacyFetch.Basis (mapped destination value) where
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
theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped 10 value) =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 8 (mapped 10 value) (0x2001#48) value) (0x1007#48)) := by
  apply X86DataStore.fetched64_checked other vector (mapped 10 value) 10 6 (by decide) (by decide)
    (origin 10 value) (0x1007#48) (0x2001#48) visible controls (0x2001#64) value (0x200#32) (0#32)
  · change (0x1003#48).toInt + 4 = (0x1007#48).toInt
    decide
  · decide
  · change ((mapped 10 value).regs.get? .rsi).map (fun word : Word => word) = _
    simp [mapped,Std.ExtDHashMap.get?_insert]
  · change ((mapped 10 value).regs.get? .r10).map (fun word : Word => word) = _
    simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · decide
  · decide
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [origin,mapped,X86Execution.address,Std.ExtHashMap.getElem_insert]

theorem enabled_alignment_rejects_success_profile :
    ¬(X86FrameLoad.alignmentEnabled controls (0x40200#32) visible = false ∨
      (0x2001#48) &&& (7#48) = (0#48)) := by decide

end Store

namespace StoreDword

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
private def visible : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)

private def mapped (destination : Fin 16) (value : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs control
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (0x1000#64)
  let registers := registers.insert .ctrs controls
  let registers := registers.insert .rflags (0x200#32)
  let registers := registers.insert .seg_visibles visible
  let registers := registers.insert .log_register_writes false
  let registers := registers.insert .rsi (0x2001#64)
  let registers := registers.insert .r10 value
  let registers := registers.insert .r11 (33#64)
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (loadRex false destination 6)
  let memory := memory.insert 4097 (0x89#8)
  let memory := memory.insert 4098 (loadModRM destination 6)
  let memory := memory.insert 4099 0
  let memory := memory.insert 4100 0
  let memory := memory.insert 4101 0
  let memory := memory.insert 4102 0
  let memory := memory.insert 8193 (0xaa#8)
  let memory := memory.insert 8194 (0xaa#8)
  let memory := memory.insert 8195 (0xaa#8)
  let memory := memory.insert 8196 (0xaa#8)
  let memory := memory.insert 8197 (0xaa#8)
  let memory := memory.insert 8198 (0xaa#8)
  let memory := memory.insert 8199 (0xaa#8)
  let memory := memory.insert 8200 (0xaa#8)
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (destination : Fin 16) (value : Word) :
    X86LegacyFetch.Basis (mapped destination value) where
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
theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped 10 value) =
      .ok () (X86Move.putPointer (X86WriteWords.storeBytes 4 (mapped 10 value) (0x2001#48) (low32 value)) (0x1007#48)) := by
  apply X86DataStore.fetched32_checked other vector (mapped 10 value) 10 6 (by decide) (by decide)
    (origin 10 value) (0x1007#48) (0x2001#48) visible controls (0x2001#64) value (0x200#32) (0#32)
  · change (0x1003#48).toInt + 4 = (0x1007#48).toInt
    decide
  · decide
  · change ((mapped 10 value).regs.get? .rsi).map (fun word : Word => word) = _
    simp [mapped,Std.ExtDHashMap.get?_insert]
  · change ((mapped 10 value).regs.get? .r10).map (fun word : Word => word) = _
    simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · simp [mapped,Std.ExtDHashMap.get?_insert]
  · decide
  · decide
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · simp [origin,mapped,Std.ExtHashMap.getElem_insert]
  · intro index within
    interval_cases index <;> simp [origin,mapped,X86Execution.address,Std.ExtHashMap.getElem_insert]

theorem enabled_alignment_rejects_success_profile :
    ¬(X86FrameLoad.alignmentEnabled controls (0x40200#32) visible = false ∨
      (0x2001#48) &&& (3#48) = (0#48)) := by decide

theorem suffix_preserved (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (value : Word) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 value) with
      | .ok _ after => after.mem.get? 8197
      | .error _ _ => none) = some (0xaa#8) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  change (X86WriteWords.storeBytes 4 (mapped 10 value) (0x2001#48) (low32 value)).mem.get? 8197 = _
  rw [(X86WriteWords.storeBytes_frame 4 (mapped 10 value) (0x2001#48) (low32 value)).memory 8197 (by decide)]
  simp [mapped,Std.ExtHashMap.getElem_insert]

theorem qword_effect_rejected (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x8000000100000001#64)) with
      | .ok _ after => after.mem.get? 8197
      | .error _ _ => none) ≠ some (1#8) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  rw [suffix_preserved]
  decide


end StoreDword

end Mettapedia.Machines.TIsa.X86UnalignedWords
