import Mettapedia.Languages.VibeITP.Native.BuiltinArityCNormalization
import Mettapedia.Languages.VibeITP.Native.BuiltinArityCorrespondence

/-!
# Execution of the body admitted from the builtin-arity artifact

The exact original C artifact selects a unique operational function. Its
independent target execution returns the specified builtin arity and restores
the caller state. Theorems concern that admitted operational semantics;
concrete C layout and machine execution are separate realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityArtifactCorrespondence

open Mettapedia.GSLT.LanguageDef
open NativeOps NativeOps.NativeC
open NativeWord64 (Word encode)
open BuiltinArityLowering BuiltinArityCNormalization

theorem admitted_body_unique {function : NativeIR.Function}
    (admitted : normalizeFunction? NativeOpsCGuest.representation
      NativeOpsCGuest.function_019 = some function) : function = actualFunction :=
  Option.some.inj (admitted.symm.trans actual_function_normalized)

theorem admitted_execution_exact {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (slot : Word) (out : TargetRawResult World)
    (clear : state.fault = none) :
    (∃ function, normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
        [.word (encode slot)] state out) ↔
      (∃ storage, targetFreshFrame state.memory storage) ∧
        out = ⟨.word (encode (BuiltinAritySource.signatureArity slot)), state⟩ := by
  constructor
  · rintro ⟨function, admitted, ran⟩
    cases admitted_body_unique admitted
    exact (BuiltinArityTarget.actual_function_exact state slot out clear).mp ran
  · intro outcome
    exact ⟨actualFunction, actual_function_normalized,
      (BuiltinArityTarget.actual_function_exact state slot out clear).mpr outcome⟩

theorem source_execution_has_admitted_target {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (slot : Word) {sourceOut : SourceRawResult SourceWorld}
    (ran : SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
      NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut) :
    ∃ function targetOut,
      normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
        function [.word (encode slot)] target targetOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  obtain ⟨out, executed, value, after⟩ :=
    BuiltinArityCorrespondence.function_preservation_clear states clear slot ran
  exact ⟨actualFunction, out, actual_function_normalized, executed, value, after⟩

theorem admitted_execution_reflects_source {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (slot : Word)
    {function : NativeIR.Function} {targetOut : TargetRawResult TargetWorld}
    (admitted : normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function)
    (ran : TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
      function [.word (encode slot)] target targetOut) :
    ∃ sourceOut,
      SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
        NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  cases admitted_body_unique admitted
  exact BuiltinArityCorrespondence.function_reflection states slot ran

/-- An admitted artifact cannot add a different answer through a different body. -/
theorem different_answer_refused {World : Type}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World}
    (state : TargetState World) (slot : Word) (out : TargetRawResult World)
    (clear : state.fault = none)
    (different : out.value ≠ .word (encode (BuiltinAritySource.signatureArity slot))) :
    ¬ ∃ function, normalizeFunction? NativeOpsCGuest.representation NativeOpsCGuest.function_019 = some function ∧
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface heap calls function
        [.word (encode slot)] state out := by
  intro ran
  have same := ((admitted_execution_exact state slot out clear).mp ran).2
  exact different (congrArg TargetRawResult.value same)

end Mettapedia.Languages.VibeITP.Native.BuiltinArityArtifactCorrespondence
