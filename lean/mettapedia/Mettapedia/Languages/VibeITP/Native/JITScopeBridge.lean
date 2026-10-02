import Mettapedia.GSLT.LanguageDef.NativeExecutionScope
import Mettapedia.Languages.VibeITP.Native.JITRequest

/-!
Scope-owned native observations authorize the independent guarded execution
rule only after the actual four-literal request, byte comparisons and result
length checks. Scope validity follows from completed calls and release; it
is not a caller-provided receipt. The native function-body and pointer-memory
bridges establish these concrete checks for deployed execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.JITScopeBridge

open Spec
open Mettapedia.GSLT.LanguageDef

def decodeRequest (request : NativeExecutionScope.Request) : ExecutionRequest :=
  ⟨request.inputs.code, request.inputs.input1, request.inputs.input2, request.outputLength.val⟩

def decodeObservation (observation : NativeExecutionScope.Observation) : ExecutionObservation :=
  ⟨decodeRequest observation.request, observation.output⟩

def physicalContract (contract : ExecutionContract) : NativeExecutionScope.Contract :=
  fun request output => contract (decodeRequest request) output

def inputs (request : JITRequest.Request) : NativeExecutionScope.Inputs :=
  ⟨request.code, request.input1, request.input2⟩

theorem realized_correspondence (contract : ExecutionContract) (observation : NativeExecutionScope.Observation) :
    observation.realized (physicalContract contract) ↔
      (decodeObservation observation).realized contract := Iff.rfl

theorem owned_result_request (request : JITRequest.Request) (observation : NativeExecutionScope.Observation)
    (bytes : observation.request.inputs = inputs request)
    (output : List UInt8) (sameOutput : observation.output = output)
    (completedLength : observation.output.length = observation.request.outputLength.val)
    (guestLength : output.length = request.outputLength.toNat) :
    decodeRequest observation.request = request.decode := by
  have length : observation.request.outputLength.val = request.outputLength.toNat :=
    completedLength.symm.trans ((congrArg List.length sameOutput).trans guestLength)
  simp only [decodeRequest, JITRequest.Request.decode, ExecutionRequest.mk.injEq]
  exact ⟨congrArg NativeExecutionScope.Inputs.code bytes,
    congrArg NativeExecutionScope.Inputs.input1 bytes,
    congrArg NativeExecutionScope.Inputs.input2 bytes, length⟩

theorem checked_owned_observation
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (physicalContract contract) scope)
    (handle : Option NativeOps.Address) (safe : Term) (request : JITRequest.Request)
    (output : List UInt8)
    (guard : JITRequest.request? safe = some request)
    (receipt : NativeExecutionScope.targetMatches scope handle (inputs request) output = true)
    (length : output.length = request.outputLength.toNat) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (decodeObservation observation).realized contract ∧
      GuardedExecution safe (decodeObservation observation) ∧
      (decodeObservation observation).statement = request.statement output := by
  obtain ⟨observation, found, bytes, sameOutput⟩ :=
    (NativeExecutionScope.matches_iff scope handle (inputs request) output).mp receipt
  have physical := NativeExecutionScope.reached_read_realized reached found
  have sameRequest := owned_result_request request observation bytes output sameOutput physical.2 length
  refine ⟨observation, found, (realized_correspondence contract observation).mp physical, ?_, ?_⟩
  · constructor
    · change executionRequest? safe = some (decodeRequest observation.request)
      rw [sameRequest]
      exact (JITRequest.request_result_iff safe request).mp guard
    · exact physical.2
  · change (ExecutionObservation.mk (decodeRequest observation.request) observation.output).statement =
      request.statement output
    rw [sameRequest, sameOutput]
    exact (JITRequest.statement_correspondence request output).symm

theorem checked_owned_result_derived
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (physicalContract contract) scope)
    (handle : Option NativeOps.Address) (T : Theory) (prior : List ExecutionObservation)
    (safe : Term) (request : JITRequest.Request) (output : List UInt8)
    (premise : DerivesWithExecution T prior safe)
    (guard : JITRequest.request? safe = some request)
    (receipt : NativeExecutionScope.targetMatches scope handle (inputs request) output = true)
    (length : output.length = request.outputLength.toNat) :
    ∃ observation, NativeExecutionScope.targetRead scope handle = some observation ∧
      (decodeObservation observation).realized contract ∧
      DerivesWithExecution T (prior ++ [decodeObservation observation]) (request.statement output) := by
  obtain ⟨observation, found, physical, guarded, statement⟩ :=
    checked_owned_observation contract scope reached handle safe request output guard receipt length
  refine ⟨observation, found, physical, ?_⟩
  rw [← statement]
  exact .jit
    (derives_with_execution_observation_extension
      (fun _ member => List.mem_append_left _ member) premise)
    (by simp) guarded

theorem released_receipt_cannot_authorize
    (contract : ExecutionContract) (scope : NativeExecutionScope.Scope)
    (reached : NativeExecutionScope.Reached (physicalContract contract) scope)
    (handle : NativeOps.Address) (request : JITRequest.Request) (output : List UInt8) :
    NativeExecutionScope.targetMatches (NativeExecutionScope.targetRelease scope (some handle)) (some handle)
      (inputs request) output = false :=
  NativeExecutionScope.absent_handle_never_matches _ _
    (NativeExecutionScope.released_handle_unreadable scope handle (NativeExecutionScope.reached_valid reached).1) _ _

theorem absent_receipt_cannot_authorize
    (scope : NativeExecutionScope.Scope) (handle : Option NativeOps.Address)
    (absent : NativeExecutionScope.targetRead scope handle = none)
    (request : JITRequest.Request) (output : List UInt8) :
    NativeExecutionScope.targetMatches scope handle (inputs request) output = false :=
  NativeExecutionScope.absent_handle_never_matches _ _ absent _ _

end Mettapedia.Languages.VibeITP.Native.JITScopeBridge
