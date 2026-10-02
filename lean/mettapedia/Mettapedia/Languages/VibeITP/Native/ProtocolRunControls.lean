import Mettapedia.Languages.VibeITP.Native.ProtocolRunSoundness

/-! Accepted and refused complete-byte runs, phase ordering, and JIT-capability controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ProtocolRunControls

open Spec Spec.ProtocolExecution Spec.ProtocolObserved Spec.ProtocolRuns

def unavailable : Capability Unit := fun _ _ => .error ()

def literalSetup : List (List UInt8) :=
  [[5, 1, 1, 0, 6, 4, 1, 0, 1, 13, 1, 0]]

def literalProof : List (List UInt8) := [[18, 1, 0, 14, 0, 0]]

def isFullSuccess {ε : Type} : CheckResult ε → Bool
  | .completed verdict _ => verdict.success
  | _ => false

theorem literal_goal_accepted :
    isFullSuccess (ProtocolRuns.checkRun unavailable literalSetup literalProof) = true := by
  cbv

theorem wrong_literal_goal_refused :
    ProtocolRuns.checkRun unavailable literalSetup [[18, 2, 0, 14, 0, 0]] =
      .rejected 1 1 (.protocol .challengeMismatch) := by cbv

theorem open_goal_is_not_full_success :
    isFullSuccess (ProtocolRuns.checkRun unavailable literalSetup [[]]) = false := by cbv

theorem zero_registered_goals_is_not_full_success :
    isFullSuccess (ProtocolRuns.checkRun unavailable [] [[]]) = false := by cbv

theorem setup_only_is_not_full_success :
    isFullSuccess (ProtocolRuns.checkRun unavailable literalSetup []) = false := by cbv

theorem later_malformed_precedes_earlier_semantic_error (capability : Capability Unit) :
    ProtocolRuns.checkRun capability [[3, 0]] [[26]] = .malformed 1 (.unknownOpcode 26) := by
  cbv

theorem setup_inference_refused (capability : Capability Unit) :
    ProtocolRuns.checkRun capability [[18, 1, 0]] [[]] =
      .rejected 0 0 (.protocol (.inferenceInSetup .litIsNat)) := by cbv

theorem duplicate_challenge_destination_refused (capability : Capability Unit) :
    ProtocolRuns.checkRun capability
      [[5, 1, 1, 0, 6, 4, 1, 0, 1, 13, 1, 0, 13, 1, 0]] [[]] =
      .rejected 0 3 (.protocol (.occupied .challenge)) := by cbv

def jitSetup : List (List UInt8) :=
  [[5, 1, 195, 0, 5, 0, 1, 5, 0, 2, 5, 1, 0, 3,
    6, 11, 4, 0, 1, 2, 3, 4, 9, 4, 0,
    6, 12, 4, 0, 1, 2, 2, 5, 13, 5, 0]]

def jitProof : List (List UInt8) := [[25, 0, 1, 6, 14, 0, 1]]

/-- A protocol-control capability; no physical-execution claim is attached. -/
def emptyOutput : Capability Unit := fun _ request =>
  if request.outputLength = 0 then .ok [] else .error ()

theorem guarded_jit_goal_accepted :
    isFullSuccess (ProtocolRuns.checkRun emptyOutput jitSetup jitProof) = true := by cbv

theorem guarded_jit_physical_failure_preserved :
    ProtocolRuns.checkRun unavailable jitSetup jitProof = .rejected 1 0 (.capability ()) := by
  cbv

def wrongOutput : Capability Unit := fun _ _ => .ok [0]

theorem guarded_jit_wrong_output_length_refused :
    ProtocolRuns.checkRun wrongOutput jitSetup jitProof =
      .rejected 1 0 (.protocol .theoremFailed) := by cbv

theorem jit_in_setup_precedes_capability_call (capability : Capability Unit) :
    ProtocolRuns.checkRun capability [[25, 0, 1, 0]] [[]] =
      .rejected 0 0 (.protocol (.inferenceInSetup .jit)) := by cbv

def varyingOutput : Capability Unit := fun ordinal _ => .ok [UInt8.ofNat ordinal]

def unitRequest : ExecutionRequest := ⟨[], [], [], 1⟩

theorem invocation_index_can_change_output :
    varyingOutput 0 unitRequest = .ok [0] ∧ varyingOutput 1 unitRequest = .ok [1] := by
  constructor <;> rfl

theorem registered_literal_transcript :
    Spec.ProtocolRegistrations.check unavailable literalSetup literalProof = [litIsNatStatement 1] := by
  cbv

theorem registered_jit_transcript :
    Spec.ProtocolRegistrations.check emptyOutput jitSetup jitProof =
      [.app (.builtin .executedTo) [.lit [195], .lit [], .lit [], .lit []]] := by cbv

end Mettapedia.Languages.VibeITP.Native.ProtocolRunControls
