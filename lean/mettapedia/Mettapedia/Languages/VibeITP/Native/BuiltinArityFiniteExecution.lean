import Mettapedia.Languages.VibeITP.Native.BuiltinArityArtifactCorrespondence
import Mettapedia.GSLT.LanguageDef.NativeOpsFiniteStorage

/-!
# Total builtin-arity execution on finite abstract storage

A finite storage support supplies the invocation frame; no fixed storage or
word bound is added. Both clear and faulted entries preserve the complete
state. This theorem concerns the operational body admitted from the generated
artifact. Concrete C/ABI execution remains a separate realization boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityFiniteExecution

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeOps.NativeC
open NativeWord64 (Word encode)
open BuiltinArityLowering BuiltinArityCNormalization BuiltinArityArtifactCorrespondence

theorem finite_admitted_execution_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (finite : TargetFiniteStorage state.memory)
    (slot : Word) (out : TargetRawResult World) :
    (∃ function, normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
        [.word (encode slot)] state out) ↔
      out = ⟨if state.fault.isSome then .word 0
        else .word (encode (BuiltinAritySource.signatureArity slot)), state⟩ := by
  have fresh := target_finite_fresh finite
  cases incoming : state.fault with
  | none =>
      change (∃ function, normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
        TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
          [.word (encode slot)] state out) ↔
        out = ⟨.word (encode (BuiltinAritySource.signatureArity slot)), state⟩
      rw [admitted_execution_exact state slot out incoming]
      exact and_iff_right fresh
  | some fault =>
      change (∃ function, normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
        TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
          [.word (encode slot)] state out) ↔ out = ⟨.word 0, state⟩
      constructor
      · rintro ⟨function, admitted, ran⟩
        cases admitted_body_unique admitted
        exact ((BuiltinArityTarget.actual_function_entry_fault_exact state slot out incoming).mp ran).2
      · intro same
        exact ⟨actualFunction, actual_function_normalized,
          (BuiltinArityTarget.actual_function_entry_fault_exact state slot out incoming).mpr ⟨fresh, same⟩⟩

theorem finite_source_execution_has_admitted_target {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (finite : SourceFiniteStorage source.memory)
    (slot : Word) {sourceOut : SourceRawResult SourceWorld}
    (ran : SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
      NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut) :
    ∃ function targetOut,
      normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
        function [.word (encode slot)] target targetOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  cases incoming : source.fault with
  | none => exact source_execution_has_admitted_target states incoming slot ran
  | some fault =>
      obtain ⟨out, executed, value, after⟩ :=
        BuiltinArityCorrespondence.function_preservation_entry_fault states incoming
          (source_finite_fresh finite) slot ran
      exact ⟨actualFunction, out, actual_function_normalized, executed, value, after⟩

/-- Empty storage supplies invocation space for every input and incoming fault. -/
theorem empty_storage_has_admitted_execution {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World)
    (empty : state.memory = ⟨fun _ _ => none, fun _ => none⟩) (slot : Word) :
    ∃ function out,
      normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
        [.word (encode slot)] state out := by
  have finite : TargetFiniteStorage state.memory := by
    rw [empty]
    exact empty_target_storage_finite
  obtain ⟨function, admitted, ran⟩ :=
    (finite_admitted_execution_exact state finite slot _).mpr rfl
  exact ⟨function, _, admitted, ran⟩

/-- Unrestricted infinite storage really can prevent an admitted invocation. -/
theorem infinite_storage_has_no_admitted_execution {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (clear : state.fault = none)
    (infinite : state.memory = ⟨fun _ _ => some .unit, fun _ => none⟩)
    (slot : Word) (out : TargetRawResult World) :
    ¬ ∃ function,
      normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
        [.word (encode slot)] state out := by
  intro ran
  have fresh := ((admitted_execution_exact state slot out clear).mp ran).1
  rw [infinite] at fresh
  exact infinite_target_cells_no_fresh_frame fresh

end Mettapedia.Languages.VibeITP.Native.BuiltinArityFiniteExecution
