import Mettapedia.Languages.VibeITP.Native.DecodedBounds
import Mettapedia.Languages.VibeITP.Native.SourceFileAgreement
import Mettapedia.Languages.VibeITP.Spec.ProtocolRegistrations
import Mettapedia.Languages.VibeITP.Spec.ProtocolRunCompletion

/-!
Raw-byte soundness of the independent observation-bearing protocol. The source
reader theorem covers the authored binary grammar. Operational-source lowering
and its native-storage correspondence are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ProtocolRunSoundness

open Spec
open Spec.ProtocolExecution Spec.ProtocolInvariant Spec.ProtocolObserved
open Spec.ProtocolRuns Spec.ProtocolChallenges Spec.ProtocolChallengePreservation
open Spec.ProtocolRunCompletion

theorem authored_source_instructions_bounded (bytes : List UInt8) (instructions : List Instr)
    (accepted : SourceFileAgreement.fromSource GeneratedBinarySource.authoredBinaryText bytes =
      some (.ok instructions)) : BoundedInstructions instructions := by
  rw [SourceFileAgreement.authored_source_file_correct] at accepted
  cases decoded : Spec.decodeFile bytes with
  | error error => simp [BinaryFile.embed, decoded] at accepted
  | ok result =>
    simp only [decoded, BinaryFile.embed, Option.some.injEq, Except.ok.injEq] at accepted
    subst instructions
    exact DecodedBounds.file_establishes bytes result decoded

theorem decoded_files_bounded (files : List (List UInt8)) (index : Nat)
    (decoded : List (List Instr)) (accepted : Spec.decodeFiles index files = .ok decoded) :
    BoundedFiles decoded := by
  induction files generalizing index decoded with
  | nil =>
    have same : [] = decoded := Except.ok.inj accepted
    subst decoded
    simp [BoundedFiles]
  | cons bytes rest ih =>
    cases current : Spec.decodeFile bytes with
    | error error => simp [Spec.decodeFiles, current] at accepted
    | ok instructions =>
      cases following : Spec.decodeFiles (index + 1) rest with
      | error error => simp [Spec.decodeFiles, current, following] at accepted
      | ok tail =>
        have same : instructions :: tail = decoded := by
          simpa only [Spec.decodeFiles, current, following, Except.ok.injEq] using accepted
        subst decoded
        intro items member
        rcases List.mem_cons.mp member with newest | later
        · subst items
          exact DecodedBounds.file_establishes bytes instructions current
        · exact ih (index + 1) tail following items later

theorem completed_valid {ε : Type} (capability : Capability ε) (contract : ExecutionContract)
    (realizes : Realizes capability contract) (setup proofs : List (List UInt8))
    (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    ValidState contract final := by
  obtain ⟨decoded, prepared, decodedRead, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  have bounded := decoded_files_bounded (setup ++ proofs) 0 decoded decodedRead
  have setupBounded : BoundedFiles (decoded.take setup.length) := by
    intro items member
    exact bounded items (List.mem_of_mem_take member)
  have preparedValid := runFiles_valid realizes _ setupBounded 0 (initial_valid contract) setupRun
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty] at completed
    rwa [completed.1]
  · simp only [if_neg empty] at completed
    have setupPhase : prepared.kernel.phase = .setup := runFiles_phase _ 0 setupRun
    have proofBounded : BoundedFiles (decoded.drop setup.length) := by
      intro items member
      exact bounded items (List.mem_of_mem_drop member)
    exact runFiles_valid realizes _ proofBounded setup.length
      (proofBoundary_valid prepared preparedValid setupPhase) completed.1

theorem completed_registrations_tracked {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    ∀ goal ∈ ProtocolRegistrations.check capability setup proofs, Tracked final.kernel goal := by
  obtain ⟨decoded, prepared, decodedRead, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  intro goal member
  simp only [ProtocolRegistrations.check, decodedRead, setupRun] at member
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty, List.append_nil] at member
    simp only [if_pos empty] at completed
    rw [completed.1]
    exact ProtocolRegistrations.files_tracked _ 0 setupRun goal member
  · simp only [if_neg empty, List.mem_append] at member
    simp only [if_neg empty] at completed
    rcases member with setupGoal | proofGoal
    · have preparedGoal := ProtocolRegistrations.files_tracked _ 0 setupRun goal setupGoal
      have boundaryGoal : Tracked (proofBoundary prepared).kernel goal := preparedGoal
      exact runFiles_tracked _ setup.length boundaryGoal completed.1
    · exact ProtocolRegistrations.files_tracked _ setup.length completed.1 goal proofGoal

theorem completed_success_shape {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (success : verdict.success = true) :
    final.kernel.phase = .proofs ∧ final.kernel.openChallenges = 0 ∧
      0 < final.kernel.setupChallenges + final.kernel.proofChallenges := by
  obtain ⟨decoded, prepared, _, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty] at completed
    simp [completed.2, Verdict.success] at success
  · simp only [if_neg empty] at completed
    have phase : final.kernel.phase = .proofs := runFiles_phase _ setup.length completed.1
    rw [completed.2] at success
    cases openCount : final.kernel.openChallenges with
    | zero =>
      refine ⟨phase, rfl, ?_⟩
      simpa only [openCount, Verdict.success, decide_eq_true_eq] using success
    | succ count => simp [openCount, Verdict.success] at success

theorem raw_bytes_success_registered_goals_derived {ε : Type} (capability : Capability ε)
    (contract : ExecutionContract) (realizes : Realizes capability contract)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (success : verdict.success = true) :
    ∀ goal ∈ ProtocolRegistrations.check capability setup proofs,
      DerivesWithExecution final.kernel.theory final.observations goal := by
  have valid := completed_valid capability contract realizes setup proofs verdict final accepted
  have closed := (completed_success_shape capability setup proofs verdict final accepted success).2.1
  intro goal registered
  exact closed_tracked_is_derived valid.logical valid.challenges closed
    (completed_registrations_tracked capability setup proofs verdict final accepted goal registered)

theorem raw_bytes_completed_theorems_derived {ε : Type} (capability : Capability ε)
    (contract : ExecutionContract) (realizes : Realizes capability contract)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    ∀ slot statement, final.kernel.theorems slot = some statement →
      DerivesWithExecution final.kernel.theory final.observations statement :=
  (completed_valid capability contract realizes setup proofs verdict final accepted).logical.theorems

theorem raw_bytes_success_exact_challenge_total {ε : Type} (capability : Capability ε)
    (contract : ExecutionContract) (realizes : Realizes capability contract)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (success : verdict.success = true) :
    final.kernel.satisfied.length = final.kernel.setupChallenges + final.kernel.proofChallenges ∧
      0 < final.kernel.satisfied.length := by
  have valid := completed_valid capability contract realizes setup proofs verdict final accepted
  obtain ⟨phase, closed, positive⟩ := completed_success_shape capability setup proofs verdict final accepted success
  obtain ⟨_, _, _, totals⟩ := valid.challenges
  have total : final.kernel.satisfied.length = final.kernel.setupChallenges + final.kernel.proofChallenges := by
    simpa [Totals, phase, closed] using totals
  exact ⟨total, by omega⟩

end Mettapedia.Languages.VibeITP.Native.ProtocolRunSoundness
