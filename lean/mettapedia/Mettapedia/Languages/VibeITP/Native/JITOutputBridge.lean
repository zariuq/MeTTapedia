import Mettapedia.GSLT.LanguageDef.NativeExecutionOutputExternal
import Mettapedia.Languages.VibeITP.Native.JITByteBridge

/-!
Guarded derivability through the returned execution-output view and subsequent
execution-matches call. Both external calls and their emitted context checks
are retained. The length comparison and byte observation concern the actual
returned value. The full generated caller body and physical pointer realization
are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.JITOutputBridge

open Spec
open Mettapedia.GSLT.LanguageDef
open NativeOps (Address SourceValue TargetValue encodeValue)
open NativeExecutionMatchesExternal (World)

def targetReturnedLength : TargetValue → Option (BitVec 64)
  | .array .byte _ length => some length
  | _ => none

theorem checked_output_then_receipt_derived
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (JITScopeBridge.physicalContract contract) scope)
    (source : NativeOps.SourceState World)
    (target afterOutput afterMatches : NativeOps.TargetState World)
    (related : NativeOps.StateRelated Eq source target)
    (header : Nat) (scopePointer handle : Option Address)
    (scopeRead : NativeExecutionMatchesExternal.targetScope target.external scopePointer = some scope)
    (T : Theory) (prior : List ExecutionObservation) (safe : Term) (request : JITRequest.Request)
    (premise : DerivesWithExecution T prior safe) (guard : JITRequest.request? safe = some request)
    (code input1 input2 : SourceValue) (output : TargetValue) (outputBytes : List UInt8)
    (codeRead : NativeOps.ByteViews.sourceView source.memory code = some request.code)
    (input1Read : NativeOps.ByteViews.sourceView source.memory input1 = some request.input1)
    (input2Read : NativeOps.ByteViews.sourceView source.memory input2 = some request.input2)
    (outputCalled : (NativeExecutionOutputExternal.targetExternal header).call "execution-output"
      [.reference scopePointer, .reference handle] target output afterOutput)
    (outputChecked : (NativeOps.targetObserve afterOutput output).result = .ok output)
    (outputRead : NativeOps.ByteViews.targetView afterOutput.memory output = some outputBytes)
    (lengthCompared : targetReturnedLength output = some request.outputLength)
    (raw : TargetValue)
    (matchesCalled : NativeExecutionMatchesExternal.targetExternal.call "execution-matches"
      [.reference scopePointer, .reference handle, encodeValue code, encodeValue input1,
        encodeValue input2, output] afterOutput raw afterMatches)
    (matchesChecked : (NativeOps.targetObserve afterMatches raw).result = .ok (.bool true)) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (JITScopeBridge.decodeObservation observation).realized contract ∧
      DerivesWithExecution T (prior ++ [JITScopeBridge.decodeObservation observation])
        (request.statement outputBytes) := by
  obtain ⟨pointer, length, shape, unchanged, _⟩ := NativeExecutionOutputExternal.target_checked_call
    header source target afterOutput related scopePointer handle output outputCalled outputChecked
  subst afterOutput
  have decodedRead : NativeOps.ByteViews.sourceView source.memory
      (.array .byte pointer length) = some outputBytes := by
    rw [← NativeOps.ByteViews.view_correspondence source.memory target.memory related.memory]
    simpa only [encodeValue, ← shape] using outputRead
  have compared : NativeWord64.encode length = request.outputLength := by
    apply Option.some.inj
    simpa only [shape, targetReturnedLength] using lengthCompared
  rw [shape] at matchesCalled
  exact JITByteBridge.checked_external_result_derived contract scope reached source target afterMatches
    related scopePointer handle scopeRead T prior safe request premise guard code input1 input2
    pointer length outputBytes codeRead input1Read input2Read decodedRead compared raw
    matchesCalled matchesChecked

theorem nonbyte_array_is_not_an_output_length (length : BitVec 64) :
    targetReturnedLength (.array .word none length) = none := rfl

theorem malformed_raw_value_has_no_output_length : targetReturnedLength .unit = none := rfl

theorem zero_output_length_remains_a_real_comparison :
    targetReturnedLength (.array .byte (some ⟨1, 8, []⟩) 0) = some 0 := rfl

theorem changed_length_refuses_the_returned_view (pointer : Option Address)
    (actual expected : BitVec 64) (different : actual ≠ expected) :
    targetReturnedLength (.array .byte pointer actual) ≠ some expected := by
  intro equal
  exact different (Option.some.inj equal)

end Mettapedia.Languages.VibeITP.Native.JITOutputBridge
