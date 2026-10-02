import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mettapedia.Languages.VibeITP.Spec.Execution

/-!
# Observation-bearing kernel protocol

The static protocol remains unchanged. Its JIT extension checks an occupied
safe-code theorem, the original four-literal guard, the observation's request
and its output length before publishing the execution theorem and output term.
The observation ledger records successful publication. Physical realization
is a separate condition on observations supplied by the execution capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolExecution

structure ObservedState where
  kernel : State
  observations : List ExecutionObservation

def initial : ObservedState := ⟨initialState, []⟩

def jitGuard? (state : State) (source : Nat) (observation : ExecutionObservation) : Option Term :=
  if state.phase = .proofs then
    match state.theorems source with
    | none => none
    | some safe =>
      match executionRequest? safe with
      | none => none
      | some request =>
        if request = observation.request ∧ observation.output.length = request.outputLength then
          some safe
        else none
  else none

theorem jitGuard?_iff (state : State) (source : Nat)
    (observation : ExecutionObservation) (safe : Term) :
    jitGuard? state source observation = some safe ↔
      state.phase = .proofs ∧ state.theorems source = some safe ∧
        GuardedExecution safe observation := by
  constructor
  · intro accepted
    cases phase : state.phase with
    | setup => simp [jitGuard?, phase] at accepted
    | proofs =>
      cases slot : state.theorems source with
      | none => simp [jitGuard?, phase, slot] at accepted
      | some premise =>
        cases request : executionRequest? premise with
        | none => simp [jitGuard?, phase, slot, request] at accepted
        | some decoded =>
          by_cases output : decoded = observation.request ∧
              observation.output.length = decoded.outputLength
          · simp only [jitGuard?, phase, slot, request, ↓reduceIte] at accepted
            rw [if_pos output] at accepted
            have same : premise = safe := Option.some.inj accepted
            subst safe
            exact ⟨rfl, rfl, by simpa [output.1] using request,
              by simpa [output.1] using output.2⟩
          · simp [jitGuard?, phase, slot, request, output] at accepted
  · rintro ⟨phase, slot, request, output⟩
    rw [jitGuard?, if_pos phase, slot]
    change (match executionRequest? safe with
      | none => none
      | some decoded =>
        if decoded = observation.request ∧ observation.output.length = decoded.outputLength then
          some safe else none) = some safe
    rw [request]
    exact if_pos ⟨rfl, output⟩


def jit (state : ObservedState) (source theoremDestination termDestination : Nat)
    (observation : ExecutionObservation) : StepM ObservedState :=
  if state.kernel.phase = .setup then .error (.inferenceInSetup .jit)
  else match jitGuard? state.kernel source observation with
  | none =>
    match state.kernel.theorems source with
    | none => .error (.missing .theorem)
    | some _ => .error .theoremFailed
  | some _ =>
    match state.kernel.placeTheorem theoremDestination observation.statement with
    | .error error => .error error
    | .ok placed =>
      match placed.placeTerm termDestination (.lit observation.output) with
      | .error error => .error error
      | .ok output => .ok ⟨output, state.observations ++ [observation]⟩

theorem placeTheorem_result {before after : State} {destination : Nat} {statement : Term}
    (accepted : before.placeTheorem destination statement = .ok after) :
    after = { before with theorems := setSlot before.theorems destination (some statement) } := by
  unfold State.placeTheorem at accepted
  split at accepted
  · cases accepted
  · exact (Except.ok.inj accepted).symm

theorem placeTerm_result {before after : State} {destination : Nat} {term : Term}
    (accepted : before.placeTerm destination term = .ok after) :
    after = { before with terms := setSlot before.terms destination (some term) } := by
  unfold State.placeTerm at accepted
  split at accepted
  · cases accepted
  · exact (Except.ok.inj accepted).symm

theorem jit_success_shape {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    ∃ safe placed,
      jitGuard? before.kernel source observation = some safe ∧
      before.kernel.placeTheorem theoremDestination observation.statement = .ok placed ∧
      placed.placeTerm termDestination (.lit observation.output) = .ok after.kernel ∧
      after.observations = before.observations ++ [observation] := by
  have proofs : before.kernel.phase ≠ .setup := by
    intro setup
    simp [jit, setup] at accepted
  simp only [jit, if_neg proofs] at accepted
  cases guard : jitGuard? before.kernel source observation with
  | none =>
    cases missing : before.kernel.theorems source <;> simp [guard, missing] at accepted
  | some safe =>
    cases first : before.kernel.placeTheorem theoremDestination observation.statement with
    | error error => simp [guard, first] at accepted
    | ok placed =>
      cases second : placed.placeTerm termDestination (.lit observation.output) with
      | error error => simp [guard, first, second] at accepted
      | ok output =>
        have same : (⟨output, before.observations ++ [observation]⟩ : ObservedState) = after := by
          simpa [jit, guard, first, second] using accepted
        subst after
        exact ⟨safe, placed, rfl, rfl, second, rfl⟩

theorem jit_preserves_theory {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    after.kernel.theory = before.kernel.theory := by
  obtain ⟨safe, placed, _, first, second, _⟩ := jit_success_shape accepted
  rw [placeTerm_result second, placeTheorem_result first]
  rfl

theorem jit_publishes_results {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    after.kernel.theorems theoremDestination = some observation.statement ∧
      after.kernel.terms termDestination = some (.lit observation.output) := by
  obtain ⟨safe, placed, _, first, second, _⟩ := jit_success_shape accepted
  rw [placeTerm_result second, placeTheorem_result first]
  simp [setSlot]

theorem jit_preserves_challenges {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    after.kernel.challenges = before.kernel.challenges ∧
      after.kernel.satisfied = before.kernel.satisfied ∧
      after.kernel.openChallenges = before.kernel.openChallenges := by
  obtain ⟨safe, placed, _, first, second, _⟩ := jit_success_shape accepted
  rw [placeTerm_result second, placeTheorem_result first]
  exact ⟨rfl, rfl, rfl⟩

theorem jit_new_theorem_derived {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (stored : ∀ slot statement, before.kernel.theorems slot = some statement →
      DerivesWithExecution before.kernel.theory before.observations statement)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    DerivesWithExecution after.kernel.theory after.observations observation.statement := by
  obtain ⟨safe, placed, guard, _, _, ledger⟩ := jit_success_shape accepted
  obtain ⟨_, premise, guarded⟩ := (jitGuard?_iff _ _ _ _).mp guard
  rw [jit_preserves_theory accepted, ledger]
  exact .jit
    (derives_with_execution_observation_extension
      (fun _ member => List.mem_append_left _ member) (stored source safe premise))
    (by simp) guarded

theorem jit_preserves_realized {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (contract : ExecutionContract)
    (prior : ∀ entry ∈ before.observations, entry.realized contract)
    (physical : observation.realized contract)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    ∀ entry ∈ after.observations, entry.realized contract := by
  obtain ⟨_, _, _, _, _, ledger⟩ := jit_success_shape accepted
  rw [ledger]
  intro entry member
  rcases List.mem_append.mp member with previous | current
  · exact prior _ previous
  · have same : entry = observation := by simpa using current
    subst entry
    exact physical

theorem jit_preserves_derived_theorems {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (stored : ∀ slot statement, before.kernel.theorems slot = some statement →
      DerivesWithExecution before.kernel.theory before.observations statement)
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    ∀ slot statement, after.kernel.theorems slot = some statement →
      DerivesWithExecution after.kernel.theory after.observations statement := by
  obtain ⟨_, placed, _, first, second, ledger⟩ := jit_success_shape accepted
  intro slot statement found
  by_cases destination : slot = theoremDestination
  · subst slot
    have same : observation.statement = statement :=
      Option.some.inj ((jit_publishes_results accepted).1.symm.trans found)
    rw [← same]
    exact jit_new_theorem_derived stored accepted
  · have old : before.kernel.theorems slot = some statement := by
      rw [placeTerm_result second, placeTheorem_result first] at found
      simpa [setSlot, destination] using found
    rw [jit_preserves_theory accepted, ledger]
    exact derives_with_execution_observation_extension
      (fun _ member => List.mem_append_left _ member) (stored slot statement old)

theorem jit_output_wellFormed {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    WellFormed after.kernel.sig (.lit observation.output) = true := by
  obtain ⟨safe, _, guard, _, _, _⟩ := jit_success_shape accepted
  have guarded := ((jitGuard?_iff _ _ _ _).mp guard).2.2
  have bound := guarded_execution_output_bound guarded
  have allocation := guarded_execution_allocation_no_wrap guarded
  simp [WellFormed, allocation]

theorem jit_in_setup_refused (state : ObservedState)
    (setup : state.kernel.phase = .setup) (source theoremDestination termDestination : Nat)
    (observation : ExecutionObservation) :
    jit state source theoremDestination termDestination observation =
      .error (.inferenceInSetup .jit) := by simp [jit, setup]

theorem jit_missing_theorem_refused (state : ObservedState)
    (proofs : state.kernel.phase = .proofs) (source theoremDestination termDestination : Nat)
    (missing : state.kernel.theorems source = none) (observation : ExecutionObservation) :
    jit state source theoremDestination termDestination observation =
      .error (.missing .theorem) := by simp [jit, jitGuard?, proofs, missing]

end Mettapedia.Languages.VibeITP.Spec.ProtocolExecution
