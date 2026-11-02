import Mettapedia.Languages.VibeITP.Native.ProtocolV2Bounds
import Mettapedia.Languages.VibeITP.Spec.ProtocolV2Invariant
import Mettapedia.Languages.VibeITP.Spec.ProtocolRegistrations

/-!
# Decoded v2 runs retain proof-calculus evidence

The byte decoder establishes the operand domain. Successful reference runs
preserve logical evidence and the original registered-goal tracking. Closing
every pending challenge therefore supplies a v2 derivation for each previously
registered goal. Native storage/process refinement remains a separate claim.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Native.ProtocolV2Soundness

open Spec Spec.ProtocolV2 Spec.ProtocolV2Invariant
open Spec.ProtocolChallenges Spec.ProtocolChallengePreservation Spec.ProtocolInvariant
open Spec.ProtocolMaintenance Spec.ProtocolExecution Spec.ProtocolSuccess

theorem decoded_run_derives_registered_goal
    (bytes : List UInt8) (instructions : List Instruction) (index : Nat)
    {before after : State} {observations : List ExecutionObservation} {goal : Term}
    (decoded : ProtocolV2.decodeFile bytes = .ok instructions)
    (invariant : Invariant before observations) (accounted : Accounting before)
    (tracked : Tracked before goal)
    (accepted : ProtocolV2.runInstrs before index instructions = .ok after)
    (closed : after.openChallenges = 0) :
    DerivesWithExecutionV2 after.theory observations goal :=
  closed_run_derives_registered_goal instructions index invariant accounted tracked
    (ProtocolV2Bounds.file_establishes bytes instructions decoded) accepted closed

theorem decoded_files_derives_registered_goal
    (bytes : List (List UInt8)) (instructions : List (List Instruction)) (index : Nat)
    {before after : State} {observations : List ExecutionObservation} {goal : Term}
    (decoded : ProtocolV2.decodeFiles index bytes = .ok instructions)
    (invariant : Invariant before observations) (accounted : Accounting before)
    (tracked : Tracked before goal)
    (accepted : ProtocolV2.runFiles before index instructions = .ok after)
    (closed : after.openChallenges = 0) :
    DerivesWithExecutionV2 after.theory observations goal := by
  have final := runFiles_preserves instructions index invariant
    (ProtocolV2Bounds.files_establishes bytes index instructions decoded) accepted
  obtain ⟨finalAccounting, _, retained⟩ := runFiles_tracks instructions index accounted accepted
  exact closed_tracked_is_derived final finalAccounting closed (retained goal tracked)

/-- Registration uses the existing challenge event. The new instruction only
publishes a theorem and therefore introduces no challenge event. -/
def event (state : State) : Instruction → Option Term
  | .legacy instruction => ProtocolRegistrations.event state instruction
  | .instantiateMany .. => none

theorem event_tracked {before after : State} (instruction : Instruction) {goal : Term}
    (registered : event before instruction = some goal)
    (accepted : ProtocolV2.execute before instruction = some (.ok after)) : Tracked after goal := by
  cases instruction with
  | instantiateMany source assignments destination => cases registered
  | legacy instruction =>
      cases instruction <;> simp only [event, ProtocolRegistrations.event] at registered
      all_goals try cases registered
      rename_i source destination
      obtain ⟨statement, read, _, shape⟩ := challengeAdd_success accepted
      have same : statement = goal := Option.some.inj (read.symm.trans registered)
      right
      refine ⟨destination, ?_⟩
      rw [shape]
      simp [setSlot, same]

/-- Ordered registrations from actual successful instruction steps, including
duplicate statements and registrations made in the proof phase. -/
def registrations : State → List Instruction → List Term
  | _, [] => []
  | state, instruction :: rest =>
      match ProtocolV2.execute state instruction with
      | some (.ok next) => (event state instruction).toList ++ registrations next rest
      | _ => []

def fileRegistrations : State → List (List Instruction) → List Term
  | _, [] => []
  | state, instructions :: rest =>
      match ProtocolV2.runInstrs state 0 instructions with
      | .ok next => registrations state instructions ++ fileRegistrations next rest
      | _ => []

theorem registrations_tracked (instructions : List Instruction) (index : Nat)
    {before after : State} (accounted : Accounting before)
    (accepted : ProtocolV2.runInstrs before index instructions = .ok after) :
    ∀ goal ∈ registrations before instructions, Tracked after goal := by
  induction instructions generalizing before index with
  | nil => simp [registrations]
  | cons instruction rest ih =>
      cases transition : ProtocolV2.execute before instruction with
      | none => simp [ProtocolV2.runInstrs, transition] at accepted
      | some result =>
          cases result with
          | error error => simp [ProtocolV2.runInstrs, transition] at accepted
          | ok next =>
              have following : ProtocolV2.runInstrs next (index + 1) rest = .ok after := by
                simpa only [ProtocolV2.runInstrs, transition] using accepted
              have nextAccounting := execute_accounting instruction accounted transition
              intro goal member
              simp only [registrations, transition, List.mem_append] at member
              rcases member with newest | later
              · have registered : event before instruction = some goal := by simpa using newest
                exact (runInstrs_tracks rest (index + 1) nextAccounting following).2.2 goal
                  (event_tracked instruction registered transition)
              · exact ih (index + 1) nextAccounting following goal later

theorem fileRegistrations_tracked (files : List (List Instruction)) (index : Nat)
    {before after : State} (accounted : Accounting before)
    (accepted : ProtocolV2.runFiles before index files = .ok after) :
    ∀ goal ∈ fileRegistrations before files, Tracked after goal := by
  induction files generalizing before index with
  | nil => simp [fileRegistrations]
  | cons instructions rest ih =>
      cases transition : ProtocolV2.runInstrs before 0 instructions with
      | error position error => simp [ProtocolV2.runFiles, transition] at accepted
      | unsupported position => simp [ProtocolV2.runFiles, transition] at accepted
      | ok next =>
          have following : ProtocolV2.runFiles next (index + 1) rest = .ok after := by
            simpa only [ProtocolV2.runFiles, transition] using accepted
          have nextAccounting := (runInstrs_tracks instructions 0 accounted transition).1
          intro goal member
          simp only [fileRegistrations, transition, List.mem_append] at member
          rcases member with current | later
          · exact (runFiles_tracks rest (index + 1) nextAccounting following).2.2 goal
              (registrations_tracked instructions 0 accounted transition goal current)
          · exact ih (index + 1) nextAccounting following goal later

def registeredGoals (setup proofs : List (List UInt8)) : List Term :=
  match ProtocolV2.decodeFiles 0 (setup ++ proofs) with
  | .error _ => []
  | .ok decoded =>
      match ProtocolV2.runFiles initialState 0 (decoded.take setup.length) with
      | .stop _ => []
      | .ok prepared => fileRegistrations initialState (decoded.take setup.length) ++
          if proofs.isEmpty then []
          else fileRegistrations (enterProofs prepared) (decoded.drop setup.length)

/-- Exact decoded execution through the setup/proof boundary, with an actual
final state. This records completion, not satisfaction of every challenge. -/
def ProofCompletion (setup proofs : List (List UInt8)) (final : State) : Prop :=
  ∃ decoded prepared,
    ProtocolV2.decodeFiles 0 (setup ++ proofs) = .ok decoded ∧
    ProtocolV2.runFiles initialState 0 (decoded.take setup.length) = .ok prepared ∧
    proofs.isEmpty = false ∧
    ProtocolV2.runFiles (enterProofs prepared) setup.length (decoded.drop setup.length) = .ok final

theorem stopped_not_success (files : List (List Instruction)) (index : Nat)
    {before : State} {verdict : Verdict}
    (stopped : ProtocolV2.runFiles before index files = .stop verdict) : verdict.success = false := by
  induction files generalizing before index with
  | nil => cases stopped
  | cons instructions rest ih =>
      cases transition : ProtocolV2.runInstrs before 0 instructions with
      | error position error =>
          have same : Verdict.rejected index position error = verdict := by
            simpa only [ProtocolV2.runFiles, transition, FilesResult.stop.injEq] using stopped
          subst verdict
          rfl
      | unsupported position =>
          have same : Verdict.unsupported index position = verdict := by
            simpa only [ProtocolV2.runFiles, transition, FilesResult.stop.injEq] using stopped
          subst verdict
          rfl
      | ok next =>
          exact ih (index + 1) (by simpa only [ProtocolV2.runFiles, transition] using stopped)

theorem checkRun_success_iff (setup proofs : List (List UInt8)) :
    (ProtocolV2.checkRun setup proofs).success = true ↔
      ∃ final, ProofCompletion setup proofs final ∧ final.openChallenges = 0 ∧
        0 < final.setupChallenges + final.proofChallenges := by
  constructor
  · intro success
    cases decodedRead : ProtocolV2.decodeFiles 0 (setup ++ proofs) with
    | error error =>
        rcases error with ⟨file, error⟩
        simp [ProtocolV2.checkRun, decodedRead, Verdict.success] at success
    | ok decoded =>
        cases setupRun : ProtocolV2.runFiles initialState 0 (decoded.take setup.length) with
        | stop verdict =>
            simp only [ProtocolV2.checkRun, decodedRead, setupRun] at success
            rw [stopped_not_success _ _ setupRun] at success
            cases success
        | ok prepared =>
            cases empty : proofs.isEmpty with
            | true => simp [ProtocolV2.checkRun, decodedRead, setupRun, empty, Verdict.success] at success
            | false =>
                cases proofRun : ProtocolV2.runFiles (enterProofs prepared) setup.length
                    (decoded.drop setup.length) with
                | stop verdict =>
                    simp only [ProtocolV2.checkRun, decodedRead, setupRun, empty, Bool.false_eq_true,
                      if_false, proofRun] at success
                    rw [stopped_not_success _ _ proofRun] at success
                    cases success
                | ok final =>
                    simp only [ProtocolV2.checkRun, decodedRead, setupRun, empty, Bool.false_eq_true,
                      if_false, proofRun] at success
                    refine ⟨final, ⟨decoded, prepared, decodedRead, setupRun, empty, proofRun⟩, ?_⟩
                    cases count : final.openChallenges with
                    | zero =>
                        refine ⟨rfl, ?_⟩
                        simpa only [count, Verdict.success, decide_eq_true_eq] using success
                    | succ n => simp [count, Verdict.success] at success
  · rintro ⟨final, ⟨decoded, prepared, decodedRead, setupRun, empty, proofRun⟩, closed, positive⟩
    simp [ProtocolV2.checkRun, decodedRead, setupRun, empty, proofRun, closed, Verdict.success, positive]

theorem completion_valid (setup proofs : List (List UInt8)) {final : State}
    (completed : ProofCompletion setup proofs final) : Invariant final [] ∧ Accounting final := by
  obtain ⟨decoded, prepared, decodedRead, setupRun, _, proofRun⟩ := completed
  have bounded := ProtocolV2Bounds.files_establishes (setup ++ proofs) 0 decoded decodedRead
  have setupBounded : ∀ items ∈ decoded.take setup.length, ∀ instruction ∈ items, instruction.Bounded :=
    fun items member => bounded items (List.mem_of_mem_take member)
  have proofBounded : ∀ items ∈ decoded.drop setup.length, ∀ instruction ∈ items, instruction.Bounded :=
    fun items member => bounded items (List.mem_of_mem_drop member)
  have preparedInvariant := runFiles_preserves _ 0 (initial_invariantFor DerivesWithExecutionV2)
    setupBounded setupRun
  obtain ⟨preparedAccounting, setupPhase, _⟩ := runFiles_tracks _ 0 initial_accounting setupRun
  have boundaryInvariant : Invariant (enterProofs prepared) [] :=
    enterProofs_preserves prepared preparedInvariant
  have boundaryAccounting := enterProofs_accounting prepared setupPhase preparedAccounting
  exact ⟨runFiles_preserves _ setup.length boundaryInvariant proofBounded proofRun,
    (runFiles_tracks _ setup.length boundaryAccounting proofRun).1⟩

theorem completion_registrations_tracked (setup proofs : List (List UInt8)) {final : State}
    (completed : ProofCompletion setup proofs final) :
    ∀ goal ∈ registeredGoals setup proofs, Tracked final goal := by
  obtain ⟨decoded, prepared, decodedRead, setupRun, empty, proofRun⟩ := completed
  obtain ⟨preparedAccounting, setupPhase, _⟩ := runFiles_tracks _ 0 initial_accounting setupRun
  have boundaryAccounting := enterProofs_accounting prepared setupPhase preparedAccounting
  intro goal member
  simp only [registeredGoals, decodedRead, setupRun, empty, Bool.false_eq_true, if_false,
    List.mem_append] at member
  rcases member with setupGoal | proofGoal
  · have tracked := fileRegistrations_tracked _ 0 initial_accounting setupRun goal setupGoal
    have atBoundary : Tracked (enterProofs prepared) goal := tracked
    exact (runFiles_tracks _ setup.length boundaryAccounting proofRun).2.2 goal atBoundary
  · exact fileRegistrations_tracked _ setup.length boundaryAccounting proofRun goal proofGoal

/-- A successful raw-byte run derives every goal actually registered anywhere
in that run. No initial invariant, operand bound, or preselected goal is assumed.
The final theory still contains precisely the axioms/definitions admitted by
the input; derivability here does not assert their semantic truth. -/
theorem raw_bytes_success_registered_goals_derived (setup proofs : List (List UInt8))
    (success : (ProtocolV2.checkRun setup proofs).success = true) :
    ∃ final, ProofCompletion setup proofs final ∧ Invariant final [] ∧
      final.satisfied.length = final.setupChallenges + final.proofChallenges ∧
      0 < final.satisfied.length ∧
      ∀ goal ∈ registeredGoals setup proofs, DerivesV2 final.theory goal := by
  obtain ⟨final, completed, closed, positive⟩ := (checkRun_success_iff setup proofs).mp success
  obtain ⟨invariant, accounted⟩ := completion_valid setup proofs completed
  have phase : final.phase = .proofs := by
    obtain ⟨_, prepared, _, setupRun, _, proofRun⟩ := completed
    obtain ⟨preparedAccounting, setupPhase, _⟩ := runFiles_tracks _ 0 initial_accounting setupRun
    exact (runFiles_tracks _ setup.length
      (enterProofs_accounting prepared setupPhase preparedAccounting) proofRun).2.1
  have totals : Totals final := by
    obtain ⟨_, _, _, totals⟩ := accounted
    exact totals
  have total : final.satisfied.length = final.setupChallenges + final.proofChallenges := by
    simpa [Totals, phase, closed] using totals
  refine ⟨final, completed, invariant, total, by omega, ?_⟩
  intro goal member
  exact closed_tracked_is_derived invariant accounted closed
    (completion_registrations_tracked setup proofs completed goal member)

#print axioms decoded_run_derives_registered_goal
#print axioms decoded_files_derives_registered_goal
#print axioms raw_bytes_success_registered_goals_derived

end Mettapedia.Languages.VibeITP.Native.ProtocolV2Soundness
