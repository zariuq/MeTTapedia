import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState

/-! Controls separating sticky context faults, retained effects and view refusal. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.RuntimeControls

open NativeWord64

private def sourceMemory : SourceMemory :=
  ⟨fun _ _ => none, fun _ => none⟩

private def targetMemory : TargetMemory :=
  ⟨fun _ _ => none, fun _ => none⟩

private def sourceState : SourceState (Bool × Nat) :=
  ⟨sourceMemory, none, true, true, (false, 0), AllocatorStats.sourceEmpty⟩

private def targetState : TargetState (Bool × Nat) :=
  ⟨targetMemory, none, true, true, (false, 0), AllocatorStats.targetEmpty⟩

theorem clear_context_normal_return :
    (targetObserve targetState (.word 7)).result = .ok (.word 7) := rfl

theorem private_default_is_not_normal_return :
    (targetObserve { targetState with fault := some .resourceFault } (.word 0)).result =
      .error .resourceFault := rfl

theorem first_fault_survives_later_division_refusal :
    (targetFinish { targetState with fault := some .resourceFault }
      (.error .divisionByZero) (.word 0)).result = .error .resourceFault := rfl

theorem reader_poison_does_not_poison_context :
    (targetObserve { targetState with external := (true, 1) } (.word 17)).result =
      .ok (.word 17) := rfl

theorem reader_poison_is_retained_after_context_refusal :
    (targetFinish { targetState with external := (true, 1) }
      (.error .lengthOverflow) (.word 0)).state.external = (true, 1) := rfl

theorem source_effects_before_resource_refusal_are_retained :
    (sourceFinish { sourceState with external := (false, 9) }
      (.error .resourceFault)).state.external = (false, 9) := rfl

theorem target_effects_before_resource_refusal_are_retained :
    (targetFinish { targetState with external := (false, 9) }
      (.error .resourceFault) (.word 0)).state.external = (false, 9) := rfl

theorem allocation_table_rehash_before_resource_refusal_is_retained :
    (targetFinish { targetState with
      allocatorStats := AllocatorStats.targetRehash ⟨8, 1, 16, 1, 3⟩ 32 }
      (.error .resourceFault) (.word 0)).state.allocatorStats = ⟨8, 1, 32, 1, 0⟩ := rfl

private def liveSource : SourceMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.word (bounded 64 13)) else none,
    fun storage => if storage = 1 then some (bounded 64 8) else none⟩

private def liveTarget : TargetMemory :=
  ⟨fun storage index => if storage = 1 ∧ index = 0 then some (.word 13) else none,
    fun storage => if storage = 1 then some 8 else none⟩

theorem source_allocation_before_later_refusal_is_retained :
    (sourceFinish { sourceState with memory := liveSource }
      (.error .resourceFault)).state.memory.cells 1 0 = some (.word (bounded 64 13)) := rfl

theorem target_allocation_before_later_refusal_is_retained :
    (targetFinish { targetState with memory := liveTarget }
      (.error .resourceFault) (.word 0)).state.memory.cells 1 0 = some (.word 13) := rfl

end Mettapedia.GSLT.LanguageDef.NativeOps.RuntimeControls
