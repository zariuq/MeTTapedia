import Mettapedia.Languages.VibeITP.Spec.ProtocolChallengePreservation

/-! Finite observation-bearing protocol runs and their reached-state invariants. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolRuns

open ProtocolExecution ProtocolInvariant ProtocolObserved ProtocolChallenges
open ProtocolChallengePreservation

def BoundedInstructions (instructions : List Instr) : Prop :=
  ∀ instruction ∈ instructions, instruction.MachineBounded

def BoundedFiles (files : List (List Instr)) : Prop :=
  ∀ instructions ∈ files, BoundedInstructions instructions

structure ValidState (contract : ExecutionContract) (state : ObservedState) : Prop where
  logical : LogicalInvariant state
  realized : RealizedLedger contract state
  challenges : Accounting state.kernel

theorem initial_valid (contract : ExecutionContract) : ValidState contract initial :=
  ⟨initial_invariant, initial_realized contract, initial_accounting⟩

theorem step_valid {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    {before after : ObservedState} (instruction : Instr) (realizes : Realizes capability contract)
    (valid : ValidState contract before) (bounded : instruction.MachineBounded)
    (accepted : step capability before instruction = .ok after) : ValidState contract after :=
  ⟨step_preserves instruction valid.logical bounded accepted,
    step_realized instruction realizes valid.realized accepted,
    step_accounting instruction valid.challenges accepted⟩

def proofBoundary (state : ObservedState) : ObservedState :=
  ⟨enterProofs state.kernel, state.observations⟩

theorem proofBoundary_valid {contract : ExecutionContract} (state : ObservedState)
    (valid : ValidState contract state) (setup : state.kernel.phase = .setup) :
    ValidState contract (proofBoundary state) :=
  ⟨ProtocolMaintenance.enterProofs_invariant state valid.logical, valid.realized,
    enterProofs_accounting state.kernel setup valid.challenges⟩

inductive Reached {ε : Type} (capability : Capability ε) : ObservedState → Prop where
  | initial : Reached capability initial
  | step {before after : ObservedState} (instruction : Instr) :
    Reached capability before → instruction.MachineBounded →
      ProtocolObserved.step capability before instruction = .ok after → Reached capability after
  | proofBoundary {before : ObservedState} : Reached capability before →
    before.kernel.phase = .setup → Reached capability (ProtocolRuns.proofBoundary before)

theorem reached_valid {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    (realizes : Realizes capability contract) {state : ObservedState}
    (reached : Reached capability state) : ValidState contract state := by
  induction reached with
  | initial => exact initial_valid contract
  | step instruction _ bounded accepted prior => exact step_valid instruction realizes prior bounded accepted
  | proofBoundary _ setup prior => exact proofBoundary_valid _ prior setup

theorem step_phase {ε : Type} {capability : Capability ε} {before after : ObservedState}
    (instruction : Instr) (accepted : step capability before instruction = .ok after) :
    after.kernel.phase = before.kernel.phase := by
  cases instruction <;> simp only [step] at accepted
  case jit source theoremDestination termDestination =>
    obtain ⟨_, _, _, _, _, _, published⟩ := jitStep_success accepted
    exact (jit_challenge_frame published).phase
  all_goals
    obtain ⟨transition, _⟩ := staticStep_success accepted
    exact ProtocolFrame.execute_preserves_phase _ transition

def runInstrs {ε : Type} (capability : Capability ε) :
    ObservedState → Nat → List Instr → Except (Nat × Fault ε) ObservedState
  | state, _, [] => .ok state
  | state, index, instruction :: rest =>
    match step capability state instruction with
    | .error error => .error (index, error)
    | .ok next => runInstrs capability next (index + 1) rest

def runFiles {ε : Type} (capability : Capability ε) :
    ObservedState → Nat → List (List Instr) → Except (Nat × Nat × Fault ε) ObservedState
  | state, _, [] => .ok state
  | state, file, instructions :: rest =>
    match runInstrs capability state 0 instructions with
    | .error (index, error) => .error (file, index, error)
    | .ok next => runFiles capability next (file + 1) rest

theorem runInstrs_valid {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    (realizes : Realizes capability contract) (instructions : List Instr)
    (bounded : BoundedInstructions instructions) {before after : ObservedState} (index : Nat)
    (valid : ValidState contract before)
    (accepted : runInstrs capability before index instructions = .ok after) : ValidState contract after := by
  induction instructions generalizing before index with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [runInstrs, transition] at accepted
    | ok next =>
      apply ih (fun item member => bounded item (List.mem_cons_of_mem _ member)) (index + 1)
        (step_valid instruction realizes valid (bounded instruction (by simp)) transition)
      simpa only [runInstrs, transition] using accepted

theorem runFiles_valid {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    (realizes : Realizes capability contract) (files : List (List Instr))
    (bounded : BoundedFiles files) {before after : ObservedState} (file : Nat)
    (valid : ValidState contract before)
    (accepted : runFiles capability before file files = .ok after) : ValidState contract after := by
  induction files generalizing before file with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instructions rest ih =>
    cases transition : runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [runFiles, transition] at accepted
    | ok next =>
      apply ih (fun items member => bounded items (List.mem_cons_of_mem _ member)) (file + 1)
        (runInstrs_valid realizes instructions (bounded instructions (by simp)) 0 valid transition)
      simpa only [runFiles, transition] using accepted

theorem runInstrs_phase {ε : Type} {capability : Capability ε} (instructions : List Instr)
    {before after : ObservedState} (index : Nat)
    (accepted : runInstrs capability before index instructions = .ok after) :
    after.kernel.phase = before.kernel.phase := by
  induction instructions generalizing before index with
  | nil => exact congrArg (fun state => state.kernel.phase) (Except.ok.inj accepted).symm
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [runInstrs, transition] at accepted
    | ok next =>
      exact (ih (index + 1) (by simpa only [runInstrs, transition] using accepted)).trans
        (step_phase instruction transition)

theorem runFiles_phase {ε : Type} {capability : Capability ε} (files : List (List Instr))
    {before after : ObservedState} (file : Nat)
    (accepted : runFiles capability before file files = .ok after) :
    after.kernel.phase = before.kernel.phase := by
  induction files generalizing before file with
  | nil => exact congrArg (fun state => state.kernel.phase) (Except.ok.inj accepted).symm
  | cons instructions rest ih =>
    cases transition : runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [runFiles, transition] at accepted
    | ok next =>
      exact (ih (file + 1) (by simpa only [runFiles, transition] using accepted)).trans
        (runInstrs_phase instructions 0 transition)

theorem runInstrs_tracked {ε : Type} {capability : Capability ε} (instructions : List Instr)
    {before after : ObservedState} (index : Nat) {goal : Term} (tracked : Tracked before.kernel goal)
    (accepted : runInstrs capability before index instructions = .ok after) : Tracked after.kernel goal := by
  induction instructions generalizing before index with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instruction rest ih =>
    cases transition : step capability before instruction with
    | error error => simp [runInstrs, transition] at accepted
    | ok next =>
      exact ih (index + 1) (step_tracked instruction tracked transition)
        (by simpa only [runInstrs, transition] using accepted)

theorem runFiles_tracked {ε : Type} {capability : Capability ε} (files : List (List Instr))
    {before after : ObservedState} (file : Nat) {goal : Term} (tracked : Tracked before.kernel goal)
    (accepted : runFiles capability before file files = .ok after) : Tracked after.kernel goal := by
  induction files generalizing before file with
  | nil =>
    have same : before = after := Except.ok.inj accepted
    rwa [← same]
  | cons instructions rest ih =>
    cases transition : runInstrs capability before 0 instructions with
    | error error => rcases error with ⟨index, error⟩; simp [runFiles, transition] at accepted
    | ok next =>
      exact ih (file + 1) (runInstrs_tracked instructions 0 tracked transition)
        (by simpa only [runFiles, transition] using accepted)

inductive CheckResult (ε : Type) where
  | malformed (file : Nat) (error : DecodeError)
  | rejected (file index : Nat) (error : Fault ε)
  | completed (verdict : Verdict) (state : ObservedState)

def checkRun {ε : Type} (capability : Capability ε) (setup proofs : List (List UInt8)) : CheckResult ε :=
  match decodeFiles 0 (setup ++ proofs) with
  | .error (file, error) => .malformed file error
  | .ok decoded =>
    match runFiles capability initial 0 (decoded.take setup.length) with
    | .error (file, index, error) => .rejected file index error
    | .ok prepared =>
      if proofs.isEmpty then .completed (.setupOnly prepared.kernel.openChallenges) prepared
      else match runFiles capability (proofBoundary prepared) setup.length (decoded.drop setup.length) with
      | .error (file, index, error) => .rejected file index error
      | .ok final => .completed (.proofs final.kernel.setupChallenges final.kernel.proofChallenges
          final.kernel.openChallenges) final

theorem reached_closed_goal {ε : Type} {capability : Capability ε} {contract : ExecutionContract}
    (realizes : Realizes capability contract) {state : ObservedState}
    (reached : Reached capability state) {goal : Term} (tracked : Tracked state.kernel goal)
    (closed : state.kernel.openChallenges = 0) :
    DerivesWithExecution state.kernel.theory state.observations goal := by
  have valid := reached_valid realizes reached
  exact closed_tracked_is_derived valid.logical valid.challenges closed tracked

end Mettapedia.Languages.VibeITP.Spec.ProtocolRuns
