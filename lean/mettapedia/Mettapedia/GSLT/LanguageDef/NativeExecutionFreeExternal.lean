import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeCall

/-!
The two typed reference arguments, unit return and full post-state of the
execution-free external interface. Physical ownership effects follow the
proved ordered destructor and first-node unlink relations. The operational
context, callbacks and compact allocator statistics are retained exactly.
Binding this interface name to its admitted C symbol is an artifact obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeExternal

open NativeOps (Address SourceState TargetState SourceValue TargetValue SourceExternalSemantics
  TargetExternalSemantics ExternalCorrespondence StateRelated)
open NativeExecutionNodeRelease (World)

def sourceExternal : SourceExternalSemantics World :=
  ⟨fun name arguments pre raw post => ∃ scope handle,
    name = "execution-free" ∧ arguments = [.reference scope, .reference handle] ∧
      raw = .unit ∧ NativeExecutionFreeCall.SourceCall pre scope handle post⟩

def targetExternal : TargetExternalSemantics World :=
  ⟨fun name arguments pre raw post => ∃ scope handle,
    name = "execution-free" ∧ arguments = [.reference scope, .reference handle] ∧
      raw = .unit ∧ NativeExecutionFreeCall.TargetCall pre scope handle post⟩

theorem external_correspondence : ExternalCorrespondence sourceExternal targetExternal Eq := by
  constructor
  · intro name arguments sourcePre targetPre sourceRaw sourcePost related called
    obtain ⟨scope, handle, named, args, raw, body⟩ := called
    subst name
    subst arguments
    subst sourceRaw
    obtain ⟨targetPost, nativeBody, postRelated⟩ := NativeExecutionFreeCall.call_forward
      sourcePre targetPre related scope handle sourcePost body
    exact ⟨targetPost, ⟨scope, handle, rfl, rfl, rfl, nativeBody⟩, postRelated⟩
  · intro name arguments sourcePre targetPre targetRaw targetPost related called
    obtain ⟨scope, handle, named, args, raw, body⟩ := called
    have sourceArgs : arguments = [.reference scope, .reference handle] := by
      apply congrArg NativeOps.decodeValues at args
      simpa only [NativeOps.decode_encode_values, NativeOps.decodeValues, NativeOps.decodeValue]
        using args
    subst name
    subst arguments
    subst targetRaw
    obtain ⟨sourcePost, sourceBody, postRelated⟩ := NativeExecutionFreeCall.call_backward
      sourcePre targetPre related scope handle targetPost body
    exact ⟨.unit, sourcePost, ⟨scope, handle, rfl, rfl, rfl, sourceBody⟩, rfl, postRelated⟩

theorem source_call_retains_context (pre post : SourceState World)
    (scope handle : Option Address) (called : NativeExecutionFreeCall.SourceCall pre scope handle post) :
    post.fault = pre.fault ∧ post.allocatorAvailable = pre.allocatorAvailable ∧
      post.releaseAvailable = pre.releaseAvailable ∧ post.allocatorStats = pre.allocatorStats := by
  cases called <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem target_call_retains_context (pre post : TargetState World)
    (scope handle : Option Address) (called : NativeExecutionFreeCall.TargetCall pre scope handle post) :
    post.fault = pre.fault ∧ post.allocatorAvailable = pre.allocatorAvailable ∧
      post.releaseAvailable = pre.releaseAvailable ∧ post.allocatorStats = pre.allocatorStats := by
  cases called <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem undeclared_operation_has_no_call (name : String) (different : name ≠ "execution-free")
    (arguments : List TargetValue) (pre post : TargetState World) (raw : TargetValue) :
    ¬ targetExternal.call name arguments pre raw post := by
  rintro ⟨_, _, equal, _⟩
  exact different equal

theorem extra_argument_has_no_call (pre post : TargetState World)
    (scope handle : Option Address) (raw extra : TargetValue) :
    ¬ targetExternal.call "execution-free" [.reference scope, .reference handle, extra]
      pre raw post := by
  rintro ⟨_, _, _, equal, _⟩
  have lengths := congrArg List.length equal
  cases lengths

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeExternal
