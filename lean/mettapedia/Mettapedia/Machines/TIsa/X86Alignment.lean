import Mettapedia.Machines.TIsa.X86DwordLoad
import Mettapedia.Machines.TIsa.X86Flags

/-!
# Alignment-check profiles and unaligned U32 loads

The original alignment predicate can be false even in application mode at
privilege level three with CR0.AM set, because RFLAGS.AC is clear. Arithmetic
flag writes preserve AC, so they preserve that entry condition.

Concrete controls fetch an unaligned four-byte load through the original
Sail decoder, retain zero extension and the memory frame, and reject the
successful-load profile when alignment checking is enabled. The latter is a
profile rejection, not an asserted theorem about the model's fault outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Alignment

open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86DwordLoad
local instance : MemoryPrimitives := X86Memory.ordinary

theorem disabled_when_ac_clear (controls : Vector (BitVec 64) 17) (flags : BitVec 32)
    (visible : Vector (BitVec 16) 6) (clear : Functions._get_rflagsbits_ac flags = (0#1)) :
    X86FrameLoad.alignmentEnabled controls flags visible = false := by
  simp [X86FrameLoad.alignmentEnabled,clear,Sail.BitVec.zeroExtend]

theorem arithmetic_preserves_ac (flags result : BitVec 32) :
    Functions._get_rflagsbits_ac (X86Flags.mergeFlags flags result) = Functions._get_rflagsbits_ac flags := by
  simp [X86Flags.mergeFlags,Functions._get_rflagsbits_ac,Functions._update_rflagsbits_cf,
    Functions._update_rflagsbits_pf,Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of]
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  (interval_cases index;
    simp [Sail.BitVec.extractLsb,Sail.BitVec.updateSubrange,Sail.BitVec.updateSubrange',BitVec.extractLsb])

namespace Controls

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
private def controls : Vector (BitVec 64) 17 := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
private def visible : Vector (BitVec 16) 6 := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)

private def mapped (destination : Fin 16) (value : BitVec 32) : State :=
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
  let memory := (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (loadRex false destination 6)
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
  ⟨registers, (), memory, (), 0, #[]⟩

private def origin (destination : Fin 16) (value : BitVec 32) :
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
    (destination : Fin 16) (value : BitVec 32) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run (mapped destination value) =
      .ok () (X86Move.putPointer (put (mapped destination value) destination (value.zeroExtend 64)) (0x1007#48)) := by
  apply X86DwordLoad.fetched_dword_checked other vector (mapped destination value) destination 6 (by decide) (by decide)
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

theorem high_dword_zero_extended (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) = some (0x89abcdef#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  simp [X86Move.lookup_putPointer, lookup_put_same]

theorem sign_extension_rejected (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 10 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) ≠ some (0xffffffff89abcdef#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [high_dword_zero_extended]
  decide

theorem changed_modrm_changes_destination (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped 11 (0x89abcdef#32)) with
      | .ok _ after => lookup after 10
      | .error _ _ => none) = some (0xffffffffffffffff#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  dsimp only
  rw [X86Move.lookup_putPointer, lookup_put_other _ 11 10 _ (by decide)]
  change ((mapped 11 (0x89abcdef#32)).regs.get? .r10).map (fun word : Word => word) = _
  simp [mapped, Std.ExtDHashMap.get?_insert]

theorem unaligned_address : (0x2001#48) &&& (3#48) ≠ (0#48) := by decide

theorem disabled_despite_am_and_user_mode :
    X86FrameLoad.alignmentEnabled controls (0x200#32) visible = false := by decide

theorem enabled_profile_rejects_unaligned :
    ¬(X86FrameLoad.alignmentEnabled controls (0x40200#32) visible = false ∨
      (0x2001#48) &&& (3#48) = (0#48)) := by decide

theorem arithmetic_keeps_alignment_disabled (result : BitVec 32) :
    X86FrameLoad.alignmentEnabled controls (X86Flags.mergeFlags (0x200#32) result) visible = false := by
  apply disabled_when_ac_clear
  rw [arithmetic_preserves_ac]
  decide

theorem memory_preserved (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (destination : Fin 16) (value : BitVec 32) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (match (Functions.x86_fetch_decode_execute ()).run (mapped destination value) with
      | .ok _ after => some after.mem
      | .error _ _ => none) = some (mapped destination value).mem := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  rw [executes]
  rfl



end Controls

end Mettapedia.Machines.TIsa.X86Alignment
