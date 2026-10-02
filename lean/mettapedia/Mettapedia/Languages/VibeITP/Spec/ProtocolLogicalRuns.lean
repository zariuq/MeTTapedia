import Mettapedia.Languages.VibeITP.Spec.ProtocolRunCompletion

/-!
Logical reached-state invariants require the protocol's actual guarded
observation rule, but do not require a hypothesis about physical execution.
Physical realization of an observation ledger remains a separate property.
Execution-free decoded streams retain the empty initial observation ledger.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolLogicalRuns

open ProtocolExecution ProtocolInvariant ProtocolObserved ProtocolRuns ProtocolRunCompletion

def hasExecution : Instr → Bool
  | .jit _ _ _ => true
  | _ => false

def NoExecution (instructions : List Instr) : Prop :=
  ∀ instruction ∈ instructions, hasExecution instruction = false

def NoExecutionFiles (files : List (List Instr)) : Prop :=
  ∀ instructions ∈ files, NoExecution instructions

theorem runInstrs_logical {ε : Type} {capability : Capability ε}
    (instructions : List Instr) (bounded : BoundedInstructions instructions)
    {before after : ObservedState} (index : Nat) (logical : LogicalInvariant before)
    (accepted : ProtocolRuns.runInstrs capability before index instructions = .ok after) :
    LogicalInvariant after := by
  induction instructions generalizing before index with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [ProtocolRuns.runInstrs, transition] at accepted
    | ok next =>
      apply ih (fun item member => bounded item (List.mem_cons_of_mem _ member)) (index + 1)
        (step_preserves instruction logical (bounded instruction (by simp)) transition)
      simpa only [ProtocolRuns.runInstrs, transition] using accepted

theorem runFiles_logical {ε : Type} {capability : Capability ε}
    (files : List (List Instr)) (bounded : BoundedFiles files)
    {before after : ObservedState} (file : Nat) (logical : LogicalInvariant before)
    (accepted : ProtocolRuns.runFiles capability before file files = .ok after) :
    LogicalInvariant after := by
  induction files generalizing before file with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instructions rest ih =>
    cases transition : ProtocolRuns.runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [ProtocolRuns.runFiles, transition] at accepted
    | ok next =>
      apply ih (fun items member => bounded items (List.mem_cons_of_mem _ member)) (file + 1)
        (runInstrs_logical instructions (bounded instructions (by simp)) 0 logical transition)
      simpa only [ProtocolRuns.runFiles, transition] using accepted

theorem completed_logical {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (boundedRead : ∀ decoded, decodeFiles 0 (setup ++ proofs) = .ok decoded → BoundedFiles decoded)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    LogicalInvariant final := by
  obtain ⟨decoded, prepared, decodedRead, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  have bounded := boundedRead decoded decodedRead
  have setupBounded : BoundedFiles (decoded.take setup.length) := by
    intro items member
    exact bounded items (List.mem_of_mem_take member)
  have preparedLogical := runFiles_logical _ setupBounded 0 initial_invariant setupRun
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty] at completed
    rwa [completed.1]
  · simp only [if_neg empty] at completed
    have proofBounded : BoundedFiles (decoded.drop setup.length) := by
      intro items member
      exact bounded items (List.mem_of_mem_drop member)
    exact runFiles_logical _ proofBounded setup.length
      (ProtocolMaintenance.enterProofs_invariant prepared preparedLogical) completed.1

theorem runInstrs_accounting {ε : Type} {capability : Capability ε}
    (instructions : List Instr) {before after : ObservedState} (index : Nat)
    (accounted : ProtocolChallenges.Accounting before.kernel)
    (accepted : ProtocolRuns.runInstrs capability before index instructions = .ok after) :
    ProtocolChallenges.Accounting after.kernel := by
  induction instructions generalizing before index with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [ProtocolRuns.runInstrs, transition] at accepted
    | ok next =>
      apply ih (index + 1)
        (ProtocolChallengePreservation.step_accounting instruction accounted transition)
      simpa only [ProtocolRuns.runInstrs, transition] using accepted

theorem runFiles_accounting {ε : Type} {capability : Capability ε}
    (files : List (List Instr)) {before after : ObservedState} (file : Nat)
    (accounted : ProtocolChallenges.Accounting before.kernel)
    (accepted : ProtocolRuns.runFiles capability before file files = .ok after) :
    ProtocolChallenges.Accounting after.kernel := by
  induction files generalizing before file with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instructions rest ih =>
    cases transition : ProtocolRuns.runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [ProtocolRuns.runFiles, transition] at accepted
    | ok next =>
      apply ih (file + 1) (runInstrs_accounting instructions 0 accounted transition)
      simpa only [ProtocolRuns.runFiles, transition] using accepted

theorem completed_accounting {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    ProtocolChallenges.Accounting final.kernel := by
  obtain ⟨decoded, prepared, _, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  have preparedAccounting := runFiles_accounting _ 0 ProtocolChallenges.initial_accounting setupRun
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty] at completed
    rwa [completed.1]
  · simp only [if_neg empty] at completed
    have setupPhase : prepared.kernel.phase = .setup := runFiles_phase _ 0 setupRun
    exact runFiles_accounting _ setup.length
      (ProtocolChallenges.enterProofs_accounting prepared.kernel setupPhase preparedAccounting) completed.1

theorem nonexecution_step_ledger {ε : Type} {capability : Capability ε}
    {before after : ObservedState} (instruction : Instr)
    (static : hasExecution instruction = false)
    (accepted : step capability before instruction = .ok after) :
    after.observations = before.observations := by
  cases instruction <;> simp only [ProtocolObserved.step] at accepted
  case jit => cases static
  all_goals exact (staticStep_success accepted).2

theorem runInstrs_ledger {ε : Type} {capability : Capability ε}
    (instructions : List Instr) (static : NoExecution instructions)
    {before after : ObservedState} (index : Nat)
    (accepted : ProtocolRuns.runInstrs capability before index instructions = .ok after) :
    after.observations = before.observations := by
  induction instructions generalizing before index with
  | nil => exact congrArg ObservedState.observations (Except.ok.inj accepted).symm
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [ProtocolRuns.runInstrs, transition] at accepted
    | ok next =>
      exact (ih (fun item member => static item (List.mem_cons_of_mem _ member)) (index + 1)
        (by simpa only [ProtocolRuns.runInstrs, transition] using accepted)).trans
        (nonexecution_step_ledger instruction (static instruction (by simp)) transition)

theorem runFiles_ledger {ε : Type} {capability : Capability ε}
    (files : List (List Instr)) (static : NoExecutionFiles files)
    {before after : ObservedState} (file : Nat)
    (accepted : ProtocolRuns.runFiles capability before file files = .ok after) :
    after.observations = before.observations := by
  induction files generalizing before file with
  | nil => exact congrArg ObservedState.observations (Except.ok.inj accepted).symm
  | cons instructions rest ih =>
    cases transition : ProtocolRuns.runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [ProtocolRuns.runFiles, transition] at accepted
    | ok next =>
      exact (ih (fun items member => static items (List.mem_cons_of_mem _ member)) (file + 1)
        (by simpa only [ProtocolRuns.runFiles, transition] using accepted)).trans
        (runInstrs_ledger instructions (static instructions (by simp)) 0 transition)

theorem decoded_nonexecution_completed_ledger {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (decoded : List (List Instr))
    (decodedRead : decodeFiles 0 (setup ++ proofs) = .ok decoded)
    (static : NoExecutionFiles decoded) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    final.observations = [] := by
  obtain ⟨actual, prepared, actualRead, setupRun, completed⟩ :=
    (checkRun_completed_iff _ _ _ _ _).mp accepted
  have same : actual = decoded := Except.ok.inj (actualRead.symm.trans decodedRead)
  subst actual
  have setupStatic : NoExecutionFiles (decoded.take setup.length) := by
    intro items member
    exact static items (List.mem_of_mem_take member)
  have preparedLedger := runFiles_ledger _ setupStatic 0 setupRun
  by_cases empty : proofs.isEmpty = true
  · simp only [if_pos empty] at completed
    rw [completed.1, preparedLedger]
    rfl
  · simp only [if_neg empty] at completed
    have proofStatic : NoExecutionFiles (decoded.drop setup.length) := by
      intro items member
      exact static items (List.mem_of_mem_drop member)
    rw [runFiles_ledger _ proofStatic setup.length completed.1]
    change prepared.observations = []
    rw [preparedLedger]
    rfl

end Mettapedia.Languages.VibeITP.Spec.ProtocolLogicalRuns
