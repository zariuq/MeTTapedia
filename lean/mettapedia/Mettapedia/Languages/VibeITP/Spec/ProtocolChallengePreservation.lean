import Mettapedia.Languages.VibeITP.Spec.ProtocolChallenges
import Mettapedia.Languages.VibeITP.Spec.ProtocolObserved

/-! Successful transitions preserve exact challenge accounting and registered goals. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolChallengePreservation

open ProtocolExecution ProtocolInvariant ProtocolFrame ProtocolChallenges ProtocolObserved
open ProtocolSuccess ProtocolStaticPreservation

theorem challengeAdd_success {before after : State} {source destination : Nat}
    (accepted : execute before (.challengeAdd source destination) = some (.ok after)) :
    ∃ statement, before.terms source = some statement ∧ before.challenges destination = none ∧
      after = { before with
        challenges := setSlot before.challenges destination (some statement)
        openChallenges := before.openChallenges + 1
        proofChallenges := match before.phase with
          | .proofs => before.proofChallenges + 1
          | .setup => before.proofChallenges } := by
  have run := Option.some.inj accepted
  obtain ⟨statement, read, following⟩ := (bind_ok_iff _ _ _).mp run
  obtain ⟨placed, placement, complete⟩ := (bind_ok_iff _ _ _).mp following
  have empty : before.challenges destination = none := by
    cases occupied : before.challenges destination with
    | none => rfl
    | some goal => simp [State.placeChallenge, occupied] at placement
  have final : ({ placed with
      openChallenges := placed.openChallenges + 1
      proofChallenges := match before.phase with
        | .proofs => placed.proofChallenges + 1
        | .setup => placed.proofChallenges } : State) = after := Except.ok.inj complete
  rw [placeChallenge_result placement] at final
  exact ⟨statement, (need_ok_iff _ _ _).mp read, empty, final.symm⟩

theorem challengeSatisfy_success {before after : State} {source theoremSlot : Nat}
    (accepted : execute before (.challengeSatisfy source theoremSlot) = some (.ok after)) :
    ∃ statement, before.phase = .proofs ∧ before.theorems theoremSlot = some statement ∧
      before.challenges source = some statement ∧ after = { before with
        challenges := setSlot before.challenges source none
        openChallenges := before.openChallenges - 1
        satisfied := before.satisfied ++ [statement] } := by
  simp only [execute, Option.some.injEq] at accepted
  cases phase : before.phase with
  | setup => simp [phase] at accepted
  | proofs =>
    simp only [phase] at accepted
    obtain ⟨statement, read, matched⟩ := (bind_ok_iff _ _ _).mp accepted
    cases challenge : before.challenges source with
    | none => simp [challenge] at matched
    | some goal =>
      simp only [challenge] at matched
      split at matched
      · rename_i same
        have final : ({ before with
            challenges := setSlot before.challenges source none
            openChallenges := before.openChallenges - 1
            satisfied := before.satisfied ++ [statement] } : State) = after := by
          simpa only [phase] using Except.ok.inj matched
        exact ⟨statement, rfl, (need_ok_iff _ _ _).mp read, by simp [same],
          by simpa only [phase] using final.symm⟩
      · cases matched

theorem execute_accounting {before after : State} (instruction : Instr)
    (accounted : Accounting before)
    (accepted : execute before instruction = some (.ok after)) : Accounting after := by
  cases instruction
  case challengeAdd source destination =>
    obtain ⟨statement, _, empty, shape⟩ := challengeAdd_success accepted
    rw [shape]
    cases phase : before.phase <;>
      simpa only [phase] using register_accounting before destination statement accounted empty
  case challengeSatisfy source theoremSlot =>
    obtain ⟨statement, proofs, _, challenge, shape⟩ := challengeSatisfy_success accepted
    rw [shape]
    exact satisfy_accounting before source statement accounted proofs challenge
  all_goals exact frame_accounting accounted (execute_challenge_frame _ rfl accepted)

theorem jit_challenge_frame {before after : ObservedState}
    {source theoremDestination termDestination : Nat} {observation : ExecutionObservation}
    (accepted : jit before source theoremDestination termDestination observation = .ok after) :
    ChallengeFrame before.kernel after.kernel := by
  rw [jit_kernel_shape accepted]
  constructor <;> rfl

theorem step_accounting {ε : Type} {capability : Capability ε} {before after : ObservedState}
    (instruction : Instr) (accounted : Accounting before.kernel)
    (accepted : step capability before instruction = .ok after) : Accounting after.kernel := by
  cases instruction <;> simp only [step] at accepted
  case jit source theoremDestination termDestination =>
    obtain ⟨_, _, _, _, _, _, published⟩ := jitStep_success accepted
    exact frame_accounting accounted (jit_challenge_frame published)
  all_goals
    obtain ⟨transition, _⟩ := staticStep_success accepted
    exact execute_accounting _ accounted transition

def Tracked (state : State) (goal : Term) : Prop :=
  goal ∈ state.satisfied ∨ ∃ slot, state.challenges slot = some goal

theorem frame_tracked {before after : State} (frame : ChallengeFrame before after)
    {goal : Term} (tracked : Tracked before goal) : Tracked after goal := by
  simpa [Tracked, frame.slots, frame.satisfied] using tracked

theorem register_tracked (before : State) (destination : Nat) (statement : Term)
    (empty : before.challenges destination = none) {goal : Term} (tracked : Tracked before goal) :
    Tracked { before with challenges := setSlot before.challenges destination (some statement) } goal := by
  rcases tracked with completed | ⟨slot, pending⟩
  · exact Or.inl completed
  · right
    refine ⟨slot, ?_⟩
    by_cases newest : slot = destination
    · simp [newest, empty] at pending
    · simpa [setSlot, newest] using pending

theorem satisfy_tracked (before : State) (source : Nat) (statement : Term)
    (challenge : before.challenges source = some statement)
    {goal : Term} (tracked : Tracked before goal) :
    Tracked { before with
      challenges := setSlot before.challenges source none
      satisfied := before.satisfied ++ [statement] } goal := by
  rcases tracked with completed | ⟨slot, pending⟩
  · exact Or.inl (List.mem_append_left _ completed)
  · by_cases finished : slot = source
    · have same : statement = goal := Option.some.inj (challenge.symm.trans (finished ▸ pending))
      exact Or.inl (by simp [← same])
    · exact Or.inr ⟨slot, by simpa [setSlot, finished] using pending⟩

theorem execute_tracked {before after : State} (instruction : Instr) {goal : Term}
    (tracked : Tracked before goal)
    (accepted : execute before instruction = some (.ok after)) : Tracked after goal := by
  cases instruction
  case challengeAdd source destination =>
    obtain ⟨statement, _, empty, shape⟩ := challengeAdd_success accepted
    rw [shape]
    exact register_tracked before destination statement empty tracked
  case challengeSatisfy source theoremSlot =>
    obtain ⟨statement, _, _, challenge, shape⟩ := challengeSatisfy_success accepted
    rw [shape]
    exact satisfy_tracked before source statement challenge tracked
  all_goals exact frame_tracked (execute_challenge_frame _ rfl accepted) tracked

theorem step_tracked {ε : Type} {capability : Capability ε} {before after : ObservedState}
    (instruction : Instr) {goal : Term} (tracked : Tracked before.kernel goal)
    (accepted : step capability before instruction = .ok after) : Tracked after.kernel goal := by
  cases instruction <;> simp only [step] at accepted
  case jit source theoremDestination termDestination =>
    obtain ⟨_, _, _, _, _, _, published⟩ := jitStep_success accepted
    exact frame_tracked (jit_challenge_frame published) tracked
  all_goals
    obtain ⟨transition, _⟩ := staticStep_success accepted
    exact execute_tracked _ tracked transition

theorem closed_tracked_is_satisfied {state : State} {goal : Term} (accounted : Accounting state)
    (closed : state.openChallenges = 0) (tracked : Tracked state goal) : goal ∈ state.satisfied := by
  rcases tracked with completed | ⟨slot, pending⟩
  · exact completed
  · rw [no_open_slots accounted closed slot] at pending
    cases pending

theorem closed_tracked_is_derived {state : ObservedState} {goal : Term}
    (invariant : LogicalInvariant state) (accounted : Accounting state.kernel)
    (closed : state.kernel.openChallenges = 0) (tracked : Tracked state.kernel goal) :
    DerivesWithExecution state.kernel.theory state.observations goal :=
  invariant.satisfied goal (closed_tracked_is_satisfied accounted closed tracked)

end Mettapedia.Languages.VibeITP.Spec.ProtocolChallengePreservation
