import Mettapedia.GSLT.LanguageDef.NativeExecutionMatchesExternal
import Mettapedia.Languages.VibeITP.Native.JITScopeBridge

/-!
Scope-owned guarded execution results checked through the caller's typed byte
views. The actual buffer comparison and the emitted unsigned length comparison
determine the request and result. Derivability still requires the independent
safe-code premise and the physical execution contract. The generated function
body and its concrete pointer realization remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.JITByteBridge

open Spec
open Mettapedia.GSLT.LanguageDef
open NativeOps (Address SourceMemory TargetMemory SourceValue MemoryRelated encodeValue)

theorem buffer_receipt (scope : NativeExecutionScope.Scope) (handle : Option Address)
    (source : SourceMemory) (target : TargetMemory) (related : MemoryRelated source target)
    (request : JITRequest.Request) (code input1 input2 output : SourceValue)
    (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source code = some request.code)
    (input1Read : NativeOps.ByteViews.sourceView source input1 = some request.input1)
    (input2Read : NativeOps.ByteViews.sourceView source input2 = some request.input2)
    (outputRead : NativeOps.ByteViews.sourceView source output = some outputBytes)
    (checked : NativeExecutionBytes.targetMatchesViews scope handle target (encodeValue code)
      (encodeValue input1) (encodeValue input2) (encodeValue output) = some true) :
    NativeExecutionScope.targetMatches scope handle (JITScopeBridge.inputs request) outputBytes = true := by
  have contents := NativeExecutionBytes.target_views_with_contents scope handle source target
    related code input1 input2 output (JITScopeBridge.inputs request) outputBytes
    codeRead input1Read input2Read outputRead
  exact Option.some.inj (contents.symm.trans checked)

theorem checked_length (source : SourceMemory) (outputAddress : Option Address)
    (outputLength : NativeWord64.Word) (outputBytes : List UInt8) (request : JITRequest.Request)
    (outputRead : NativeOps.ByteViews.sourceView source
      (.array .byte outputAddress outputLength) = some outputBytes)
    (compared : NativeWord64.encode outputLength = request.outputLength) :
    outputBytes.length = request.outputLength.toNat := by
  have length := NativeOps.ByteViews.source_view_length source outputAddress outputLength outputBytes
    outputRead
  have encoded := congrArg BitVec.toNat compared
  exact length.trans encoded

theorem checked_buffer_observation
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (JITScopeBridge.physicalContract contract) scope)
    (handle : Option Address) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (safe : Term) (request : JITRequest.Request)
    (guard : JITRequest.request? safe = some request)
    (code input1 input2 : SourceValue) (outputAddress : Option Address)
    (outputLength : NativeWord64.Word) (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source code = some request.code)
    (input1Read : NativeOps.ByteViews.sourceView source input1 = some request.input1)
    (input2Read : NativeOps.ByteViews.sourceView source input2 = some request.input2)
    (outputRead : NativeOps.ByteViews.sourceView source
      (.array .byte outputAddress outputLength) = some outputBytes)
    (lengthCompared : NativeWord64.encode outputLength = request.outputLength)
    (buffersCompared : NativeExecutionBytes.targetMatchesViews scope handle target (encodeValue code)
      (encodeValue input1) (encodeValue input2)
      (.array .byte outputAddress (NativeWord64.encode outputLength)) = some true) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (JITScopeBridge.decodeObservation observation).realized contract ∧
      GuardedExecution safe (JITScopeBridge.decodeObservation observation) ∧
      (JITScopeBridge.decodeObservation observation).statement = request.statement outputBytes := by
  exact JITScopeBridge.checked_owned_observation contract scope reached handle safe request outputBytes
    guard
    (buffer_receipt scope handle source target related request code input1 input2
      (.array .byte outputAddress outputLength) outputBytes
      codeRead input1Read input2Read outputRead buffersCompared)
    (checked_length source outputAddress outputLength outputBytes request outputRead lengthCompared)

theorem checked_buffer_result_derived
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (JITScopeBridge.physicalContract contract) scope)
    (handle : Option Address) (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (T : Theory) (prior : List ExecutionObservation)
    (safe : Term) (request : JITRequest.Request) (premise : DerivesWithExecution T prior safe)
    (guard : JITRequest.request? safe = some request)
    (code input1 input2 : SourceValue) (outputAddress : Option Address)
    (outputLength : NativeWord64.Word) (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source code = some request.code)
    (input1Read : NativeOps.ByteViews.sourceView source input1 = some request.input1)
    (input2Read : NativeOps.ByteViews.sourceView source input2 = some request.input2)
    (outputRead : NativeOps.ByteViews.sourceView source
      (.array .byte outputAddress outputLength) = some outputBytes)
    (lengthCompared : NativeWord64.encode outputLength = request.outputLength)
    (buffersCompared : NativeExecutionBytes.targetMatchesViews scope handle target (encodeValue code)
      (encodeValue input1) (encodeValue input2)
      (.array .byte outputAddress (NativeWord64.encode outputLength)) = some true) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (JITScopeBridge.decodeObservation observation).realized contract ∧
      DerivesWithExecution T (prior ++ [JITScopeBridge.decodeObservation observation])
        (request.statement outputBytes) := by
  exact JITScopeBridge.checked_owned_result_derived contract scope reached handle T prior safe request
    outputBytes premise guard
    (buffer_receipt scope handle source target related request code input1 input2
      (.array .byte outputAddress outputLength) outputBytes
      codeRead input1Read input2Read outputRead buffersCompared)
    (checked_length source outputAddress outputLength outputBytes request outputRead lengthCompared)

theorem checked_external_result_derived
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (JITScopeBridge.physicalContract contract) scope)
    (source : NativeOps.SourceState NativeExecutionMatchesExternal.World)
    (target post : NativeOps.TargetState NativeExecutionMatchesExternal.World)
    (related : NativeOps.StateRelated Eq source target)
    (scopePointer handle : Option Address)
    (scopeRead : NativeExecutionMatchesExternal.targetScope target.external scopePointer = some scope)
    (T : Theory) (prior : List ExecutionObservation) (safe : Term) (request : JITRequest.Request)
    (premise : DerivesWithExecution T prior safe) (guard : JITRequest.request? safe = some request)
    (code input1 input2 : SourceValue) (outputAddress : Option Address)
    (outputLength : NativeWord64.Word) (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source.memory code = some request.code)
    (input1Read : NativeOps.ByteViews.sourceView source.memory input1 = some request.input1)
    (input2Read : NativeOps.ByteViews.sourceView source.memory input2 = some request.input2)
    (outputRead : NativeOps.ByteViews.sourceView source.memory
      (.array .byte outputAddress outputLength) = some outputBytes)
    (lengthCompared : NativeWord64.encode outputLength = request.outputLength)
    (raw : NativeOps.TargetValue)
    (called : NativeExecutionMatchesExternal.targetExternal.call "execution-matches"
      [.reference scopePointer, .reference handle, encodeValue code, encodeValue input1,
        encodeValue input2, .array .byte outputAddress (NativeWord64.encode outputLength)]
      target raw post)
    (contextChecked : (NativeOps.targetObserve post raw).result = .ok (.bool true)) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (JITScopeBridge.decodeObservation observation).realized contract ∧
      DerivesWithExecution T (prior ++ [JITScopeBridge.decodeObservation observation])
        (request.statement outputBytes) := by
  obtain ⟨buffers, _, _⟩ := NativeExecutionMatchesExternal.target_checked_call target post raw
    scopePointer handle scope (encodeValue code) (encodeValue input1) (encodeValue input2)
    (.array .byte outputAddress (NativeWord64.encode outputLength)) scopeRead called contextChecked
  exact checked_buffer_result_derived contract scope reached handle source.memory target.memory
    related.memory T prior safe request premise guard code input1 input2 outputAddress outputLength
    outputBytes codeRead input1Read input2Read outputRead lengthCompared buffers

theorem absent_handle_cannot_produce_true_buffer_receipt
    (scope : NativeExecutionScope.Scope) (handle : Option Address)
    (absent : NativeExecutionScope.targetRead scope handle = none)
    (memory : TargetMemory) (code input1 input2 output : NativeOps.TargetValue) :
    NativeExecutionBytes.targetMatchesViews scope handle memory code input1 input2 output = some false := by
  simp only [NativeExecutionBytes.targetMatchesViews, absent]

theorem released_handle_cannot_produce_true_buffer_receipt
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (JITScopeBridge.physicalContract contract) scope)
    (handle : Address) (memory : TargetMemory)
    (code input1 input2 output : NativeOps.TargetValue) :
    NativeExecutionBytes.targetMatchesViews (NativeExecutionScope.targetRelease scope (some handle))
      (some handle) memory code input1 input2 output = some false :=
  absent_handle_cannot_produce_true_buffer_receipt _ _
    (NativeExecutionScope.released_handle_unreadable scope handle
      (NativeExecutionScope.reached_valid reached).1) memory code input1 input2 output

end Mettapedia.Languages.VibeITP.Native.JITByteBridge
