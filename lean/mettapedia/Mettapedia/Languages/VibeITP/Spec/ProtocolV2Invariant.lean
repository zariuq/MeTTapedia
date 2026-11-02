import Mettapedia.Languages.VibeITP.Spec.ProtocolV2
import Mettapedia.Languages.VibeITP.Spec.ProtocolChallengePreservation
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousExtension

/-!
# Logical preservation by the versioned protocol

All legacy instruction proofs use the shared calculus interface. The new case
reads formation evidence for every replacement and constructs one simultaneous
derivation. Challenge accounting and tracking reuse the original owners; only
the theorem-slot frame is new. These are reference-protocol results, not native
storage refinement or a denotational interpretation of the source calculus.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Spec.ProtocolV2Invariant

open ProtocolV2 ProtocolExecution ProtocolInvariant ProtocolSuccess ProtocolStorage
open ProtocolFrame ProtocolChallenges ProtocolChallengePreservation
open Mettapedia.Languages.VibeITP.Presentation

abbrev Invariant (state : State) (observations : List ExecutionObservation) : Prop :=
  LogicalInvariantFor DerivesWithExecutionV2 ⟨state, observations⟩

theorem enterProofs_preserves (before : State) {observations : List ExecutionObservation}
    (invariant : Invariant before observations) : Invariant (enterProofs before) observations :=
  ProtocolMaintenance.enterProofs_invariant ⟨before, observations⟩ invariant

theorem allocate_derivation (before : State) (info : SymInfo)
    {observations : List ExecutionObservation} {statement : Term}
    (invariant : Invariant before observations)
    (derived : DerivesWithExecutionV2 before.theory observations statement) :
    DerivesWithExecutionV2 (before.allocate info).2.theory observations statement :=
  SimultaneousExtension.theory_extension invariant.theory
    (ProtocolAdmission.allocate_theory_extension before info invariant.theory)
    (fun _ member => member) derived

theorem legacy_machineBounded (instruction : Instr) (bounded : instruction.Bounded) :
    instruction.MachineBounded := (instruction.bounded_iff_machineBounded).mp bounded

theorem executeMany_preserves {before after : State} {observations : List ExecutionObservation}
    (source destination : Nat) (assignments : List (Nat × Nat))
    (invariant : Invariant before observations)
    (accepted : executeMany before source assignments destination = .ok after) :
    Invariant after observations := by
  obtain ⟨statement, symbols, values, heads, result, _, theoremRead, _, valuesRead,
    _, computed, placed⟩ := executeMany_success source destination assignments accepted
  have valuesFormed : ∀ value ∈ values, WellFormed before.sig value = true :=
    (mapM_success (fun pair : Nat × Nat => need .term (before.terms pair.2))
      (fun value => WellFormed before.sig value = true)
      (fun pair value found => invariant.terms pair.2 value ((need_ok_iff _ _ _).mp found))
      assignments values valuesRead).2
  have derived : DerivesWithExecutionV2 before.theory observations result :=
    .instantiateMany (invariant.theorems source statement theoremRead)
      (fun pair member => valuesFormed pair.2 (List.of_mem_zip member).2) computed
  exact place_theorem_invariant invariant derived placed

theorem execute_preserves {before after : State} {observations : List ExecutionObservation}
    (instruction : Instruction) (invariant : Invariant before observations)
    (bounded : instruction.Bounded)
    (accepted : ProtocolV2.execute before instruction = some (.ok after)) :
    Invariant after observations := by
  cases instruction with
  | legacy instruction =>
      exact ProtocolStaticPreservation.execute_preserves instruction invariant
        (legacy_machineBounded instruction bounded) accepted
  | instantiateMany source assignments destination =>
      exact executeMany_preserves source destination assignments invariant (Option.some.inj accepted)

theorem executeMany_challenge_frame {before after : State} {source destination : Nat}
    {assignments : List (Nat × Nat)}
    (accepted : executeMany before source assignments destination = .ok after) :
    ChallengeFrame before after := by
  obtain ⟨_, _, shape⟩ := executeMany_updates_only_theorem source destination assignments accepted
  rw [shape]
  constructor <;> rfl

theorem execute_accounting {before after : State} (instruction : Instruction)
    (accounted : Accounting before)
    (accepted : ProtocolV2.execute before instruction = some (.ok after)) : Accounting after := by
  cases instruction with
  | legacy instruction => exact ProtocolChallengePreservation.execute_accounting instruction accounted accepted
  | instantiateMany source assignments destination =>
      exact frame_accounting accounted (executeMany_challenge_frame (Option.some.inj accepted))

theorem execute_tracked {before after : State} (instruction : Instruction) {goal : Term}
    (tracked : Tracked before goal)
    (accepted : ProtocolV2.execute before instruction = some (.ok after)) : Tracked after goal := by
  cases instruction with
  | legacy instruction => exact ProtocolChallengePreservation.execute_tracked instruction tracked accepted
  | instantiateMany source assignments destination =>
      exact frame_tracked (executeMany_challenge_frame (Option.some.inj accepted)) tracked

theorem execute_phase {before after : State} (instruction : Instruction)
    (accepted : ProtocolV2.execute before instruction = some (.ok after)) : after.phase = before.phase := by
  cases instruction with
  | legacy instruction => exact execute_preserves_phase instruction accepted
  | instantiateMany source assignments destination =>
      exact (executeMany_challenge_frame (Option.some.inj accepted)).phase

theorem runInstrs_preserves (instructions : List Instruction) (index : Nat)
    {before after : State} {observations : List ExecutionObservation}
    (invariant : Invariant before observations)
    (bounded : ∀ instruction ∈ instructions, instruction.Bounded)
    (accepted : ProtocolV2.runInstrs before index instructions = .ok after) :
    Invariant after observations := by
  induction instructions generalizing before index with
  | nil =>
      have same : before = after := by cases accepted; rfl
      simpa [same] using invariant
  | cons instruction rest ih =>
      simp only [ProtocolV2.runInstrs] at accepted
      cases step : ProtocolV2.execute before instruction with
      | none => simp [step] at accepted
      | some result =>
          cases result with
          | error error => simp [step] at accepted
          | ok next =>
              simp only [step] at accepted
              exact ih (index + 1)
                (execute_preserves instruction invariant (bounded instruction (by simp)) step)
                (fun child member => bounded child (List.mem_cons_of_mem _ member)) accepted

/-- Accounting, phase and registered-goal tracking hold independently of the
derivability predicate. They are carried through the same actual run. -/
theorem runInstrs_tracks (instructions : List Instruction) (index : Nat)
    {before after : State} (accounted : Accounting before)
    (accepted : ProtocolV2.runInstrs before index instructions = .ok after) :
    Accounting after ∧ after.phase = before.phase ∧
      ∀ goal, Tracked before goal → Tracked after goal := by
  induction instructions generalizing before index with
  | nil => cases accepted; exact ⟨accounted, rfl, fun _ h => h⟩
  | cons instruction rest ih =>
      simp only [ProtocolV2.runInstrs] at accepted
      cases step : ProtocolV2.execute before instruction with
      | none => simp [step] at accepted
      | some result =>
          cases result with
          | error error => simp [step] at accepted
          | ok next =>
              simp only [step] at accepted
              obtain ⟨finalAccounting, phase, tracked⟩ :=
                ih (index + 1) (execute_accounting instruction accounted step) accepted
              exact ⟨finalAccounting, phase.trans (execute_phase instruction step),
                fun goal present => tracked goal (execute_tracked instruction present step)⟩

theorem closed_run_derives_registered_goal (instructions : List Instruction) (index : Nat)
    {before after : State} {observations : List ExecutionObservation} {goal : Term}
    (invariant : Invariant before observations) (accounted : Accounting before)
    (tracked : Tracked before goal)
    (bounded : ∀ instruction ∈ instructions, instruction.Bounded)
    (accepted : ProtocolV2.runInstrs before index instructions = .ok after)
    (closed : after.openChallenges = 0) :
    DerivesWithExecutionV2 after.theory observations goal := by
  have final := runInstrs_preserves instructions index invariant bounded accepted
  obtain ⟨finalAccounting, _, retained⟩ := runInstrs_tracks instructions index accounted accepted
  exact closed_tracked_is_derived final finalAccounting closed (retained goal tracked)

theorem runFiles_preserves (files : List (List Instruction)) (index : Nat)
    {before after : State} {observations : List ExecutionObservation}
    (invariant : Invariant before observations)
    (bounded : ∀ instructions ∈ files, ∀ instruction ∈ instructions, instruction.Bounded)
    (accepted : ProtocolV2.runFiles before index files = .ok after) :
    Invariant after observations := by
  induction files generalizing before index with
  | nil => cases accepted; exact invariant
  | cons instructions rest ih =>
      simp only [ProtocolV2.runFiles] at accepted
      cases first : ProtocolV2.runInstrs before 0 instructions with
      | error position error => simp [first] at accepted
      | unsupported position => simp [first] at accepted
      | ok next =>
          simp only [first] at accepted
          exact ih (index + 1)
            (runInstrs_preserves instructions 0 invariant (bounded instructions (by simp)) first)
            (fun batch member => bounded batch (List.mem_cons_of_mem _ member)) accepted

theorem runFiles_tracks (files : List (List Instruction)) (index : Nat)
    {before after : State} (accounted : Accounting before)
    (accepted : ProtocolV2.runFiles before index files = .ok after) :
    Accounting after ∧ after.phase = before.phase ∧
      ∀ goal, Tracked before goal → Tracked after goal := by
  induction files generalizing before index with
  | nil => cases accepted; exact ⟨accounted, rfl, fun _ h => h⟩
  | cons instructions rest ih =>
      simp only [ProtocolV2.runFiles] at accepted
      cases first : ProtocolV2.runInstrs before 0 instructions with
      | error position error => simp [first] at accepted
      | unsupported position => simp [first] at accepted
      | ok next =>
          simp only [first] at accepted
          obtain ⟨middleAccounting, phase, tracked⟩ := runInstrs_tracks instructions 0 accounted first
          obtain ⟨finalAccounting, finalPhase, finalTracked⟩ :=
            ih (index + 1) middleAccounting accepted
          exact ⟨finalAccounting, finalPhase.trans phase,
            fun goal present => finalTracked goal (tracked goal present)⟩

#print axioms executeMany_preserves
#print axioms runInstrs_preserves
#print axioms closed_run_derives_registered_goal

end Mettapedia.Languages.VibeITP.Spec.ProtocolV2Invariant
