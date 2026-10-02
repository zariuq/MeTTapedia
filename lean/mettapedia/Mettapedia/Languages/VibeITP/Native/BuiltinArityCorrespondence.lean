import Mettapedia.Languages.VibeITP.Native.BuiltinArityTarget

/-!
# Two-sided whole-function builtin signature correspondence

The actual source body and actual compiler output execute under independently
defined relations. Their exact outcomes agree on all unsigned slot values,
including incoming faults and complete post-state. Source-to-target fault-entry
construction needs available invocation storage because the target relation
explicitly creates and releases a frame before returning the typed zero.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.BuiltinArityCorrespondence

open Mettapedia.GSLT.LanguageDef
open NativeOps
open NativeWord64 (Word encode)
open BuiltinArityLowering

theorem function_preservation_clear {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (clear : source.fault = none)
    (slot : Word) {sourceOut : SourceRawResult SourceWorld}
    (ran : SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
      NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut) :
    ∃ targetOut,
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
        actualFunction [.word (encode slot)] target targetOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  obtain ⟨⟨storage, fresh⟩, same⟩ :=
    (BuiltinAritySource.actual_function_exact source slot sourceOut clear).mp ran
  subst sourceOut
  refine ⟨⟨.word (encode (BuiltinAritySource.signatureArity slot)), target⟩, ?_, rfl, states⟩
  exact (BuiltinArityTarget.actual_function_exact target slot _ (states.fault.trans clear)).mpr
    ⟨⟨storage, (fresh_function_frame_correspondence states.memory storage).mp fresh⟩, rfl⟩

theorem function_preservation_entry_fault {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) {fault : NativeWord64.Fault}
    (failed : source.fault = some fault)
    (available : ∃ storage, sourceFreshFrame source.memory storage)
    (slot : Word) {sourceOut : SourceRawResult SourceWorld}
    (ran : SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
      NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut) :
    ∃ targetOut,
      TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
        actualFunction [.word (encode slot)] target targetOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  have same := (BuiltinAritySource.actual_function_entry_fault_exact source slot sourceOut failed).mp ran
  subst sourceOut
  obtain ⟨storage, fresh⟩ := available
  refine ⟨⟨.word 0, target⟩, ?_, rfl, states⟩
  exact (BuiltinArityTarget.actual_function_entry_fault_exact target slot _
    (states.fault.trans failed)).mpr
    ⟨⟨storage, (fresh_function_frame_correspondence states.memory storage).mp fresh⟩, rfl⟩

theorem function_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target) (slot : Word)
    {targetOut : TargetRawResult TargetWorld}
    (ran : TargetFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface targetHeap targetCalls
      actualFunction [.word (encode slot)] target targetOut) :
    ∃ sourceOut,
      SourceFunctionBody NativeOpsSourceGuestSnapshot.expectedInterface sourceHeap sourceCalls
        NativeOpsSourceGuestSnapshot.function_040 [.word slot] source sourceOut ∧
      targetOut.value = encodeValue sourceOut.value ∧
      StateRelated worldRelated sourceOut.state targetOut.state := by
  cases incoming : source.fault with
  | none =>
      obtain ⟨⟨storage, fresh⟩, same⟩ :=
        (BuiltinArityTarget.actual_function_exact target slot targetOut (states.fault.trans incoming)).mp ran
      subst targetOut
      refine ⟨⟨.word (BuiltinAritySource.signatureArity slot), source⟩, ?_, rfl, states⟩
      exact (BuiltinAritySource.actual_function_exact source slot _ incoming).mpr
        ⟨⟨storage, (fresh_function_frame_correspondence states.memory storage).mpr fresh⟩, rfl⟩
  | some fault =>
      obtain ⟨_, same⟩ := (BuiltinArityTarget.actual_function_entry_fault_exact target slot targetOut
        (states.fault.trans incoming)).mp ran
      subst targetOut
      refine ⟨⟨.word 0, source⟩, ?_, rfl, states⟩
      exact (BuiltinAritySource.actual_function_entry_fault_exact source slot _ incoming).mpr rfl

end Mettapedia.Languages.VibeITP.Native.BuiltinArityCorrespondence
