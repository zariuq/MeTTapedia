import Mettapedia.Machines.OccurrenceMachine

/-!
# Hereditary admission on actual occurrence machines

The restricted machine filters the existing ordered successor list and answer
observer. A backwards-closed admission predicate permits early rejection:
once a state is refused, no later state on that branch can be admitted.
The proved finite observation is exactly the original ordered answer list
filtered by answer admission, including duplicate answer occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OccurrenceMachineCore

variable {Term State Answer : Type}

def restrict (machine : OccurrenceMachineCore Term State Answer)
    (acceptedState : State → Bool) (accept : Answer → Bool) : OccurrenceMachineCore Term State Answer where
  load := machine.load
  next state := (machine.next state).filter acceptedState
  answer state := (machine.answer state).filter accept
  answer_final state answer returned := by
    have original := (Option.filter_eq_some_iff.mp returned).1
    rw [machine.answer_final state answer original]
    rfl

theorem accepted_answer_requires_admitted_state
    (machine : OccurrenceMachineCore Term State Answer)
    (acceptedState : State → Bool) (accept : Answer → Bool)
    (backwards : ∀ state next, next ∈ machine.next state → acceptedState next = true → acceptedState state = true)
    (answerLaw : ∀ state answer, machine.answer state = some answer → accept answer = acceptedState state)
    (fuel : Nat) (state : State) {answer : Answer}
    (present : answer ∈ machine.answerOccurrences fuel state) (accepted : accept answer = true) :
    acceptedState state = true := by
  induction fuel generalizing state with
  | zero =>
    have returned : machine.answer state = some answer := by
      simpa only [answerOccurrences, Option.mem_toList] using present
    exact (answerLaw state answer returned).symm.trans accepted
  | succ fuel ih =>
    cases returned : machine.answer state with
    | some value =>
      simp only [answerOccurrences, returned, List.mem_singleton] at present
      subst answer
      exact (answerLaw state value returned).symm.trans accepted
    | none =>
      simp only [answerOccurrences, returned, List.mem_flatMap] at present
      obtain ⟨next, successor, later⟩ := present
      exact backwards state next successor (ih next later)

/-- Filtering transitions preserves exactly all accepted answer occurrences,
in order. It does not reorder or deduplicate surviving alternatives. -/
theorem restrict_answerOccurrences
    (machine : OccurrenceMachineCore Term State Answer)
    (acceptedState : State → Bool) (accept : Answer → Bool)
    (backwards : ∀ state next, next ∈ machine.next state → acceptedState next = true → acceptedState state = true)
    (answerLaw : ∀ state answer, machine.answer state = some answer → accept answer = acceptedState state)
    (fuel : Nat) (state : State) :
    (machine.restrict acceptedState accept).answerOccurrences fuel state =
      (machine.answerOccurrences fuel state).filter accept := by
  induction fuel generalizing state with
  | zero =>
    cases returned : machine.answer state with
    | none => simp [answerOccurrences, restrict, returned]
    | some answer => cases accepted : accept answer <;>
        simp [answerOccurrences, restrict, returned, accepted, Option.filter]
  | succ fuel ih =>
    cases returned : machine.answer state with
    | some answer =>
      have terminal := machine.answer_final state answer returned
      cases accepted : accept answer <;>
        simp [answerOccurrences, restrict, returned, accepted, terminal, Option.filter]
    | none =>
      simp only [answerOccurrences, restrict, returned, Option.filter_none]
      have lists : ∀ states : List State,
          ((states.filter acceptedState).flatMap
            ((machine.restrict acceptedState accept).answerOccurrences fuel)) =
          (states.flatMap (machine.answerOccurrences fuel)).filter accept := by
        intro states
        induction states with
        | nil => rfl
        | cons next rest restIH =>
          cases admitted : acceptedState next with
          | true => simp [admitted, List.filter_append, ih next, restIH]
          | false =>
            have empty : (machine.answerOccurrences fuel next).filter accept = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro answer member
              cases accepted : accept answer with
              | false => simp
              | true =>
                have necessary := accepted_answer_requires_admitted_state machine acceptedState accept
                  backwards answerLaw fuel next member accepted
                rw [admitted] at necessary
                cases necessary
            simp [admitted, List.filter_append, empty, restIH]
      exact lists _

end Mettapedia.Machines.OccurrenceMachineCore
