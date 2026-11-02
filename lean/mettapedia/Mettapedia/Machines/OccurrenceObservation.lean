import Mettapedia.Machines.OccurrenceMachine

/-!
# Chronological observations of actual occurrence transitions

The underlying successor list is computed unchanged. Each selected transition
appends the observation of its input state to a separate chronological log.
No observation is emitted merely by loading or inspecting a halted state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OccurrenceObservation

variable {Term State Answer Event : Type}

def machine (base : OccurrenceMachineCore Term State Answer) (emit : State → List Event) :
    OccurrenceMachineCore Term (State × List Event) (Answer × List Event) where
  load term := (base.load term, [])
  next state := (base.next state.1).map fun next => (next, state.2 ++ emit state.1)
  answer state := (base.answer state.1).map fun answer => (answer, state.2)
  answer_final state answer returned := by
    obtain ⟨original, returned, _⟩ := Option.map_eq_some_iff.mp returned
    simp only [base.answer_final _ _ returned, List.map_nil]

inductive Steps (base : OccurrenceMachineCore Term State Answer) (emit : State → List Event) :
    Nat → List Event → State → State → Prop where
  | refl (state) : Steps base emit 0 [] state state
  | cons {length : Nat} {events : List Event} {before next final : State} (index : Nat)
      (selected : (base.next before)[index]? = some next)
      (rest : Steps base emit length events next final) :
      Steps base emit (length + 1) (emit before ++ events) before final

namespace Steps

theorem trans {base : OccurrenceMachineCore Term State Answer} {emit : State → List Event}
    {n k : Nat} {first second : List Event} {before middle final : State}
    (earlier : Steps base emit n first before middle)
    (later : Steps base emit k second middle final) :
    Steps base emit (n + k) (first ++ second) before final := by
  induction earlier with
  | refl => simpa using later
  | cons index selected rest ih =>
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.cons index selected (ih later)

theorem realized {base : OccurrenceMachineCore Term State Answer} {emit : State → List Event}
    {length : Nat} {events : List Event} {before final : State}
    (execution : Steps base emit length events before final) (prior : List Event) :
    ∃ trace, trace.length = length ∧
      (machine base emit).follow (before, prior) trace = some (final, prior ++ events) := by
  induction execution generalizing prior with
  | refl => exact ⟨[], rfl, by simp [OccurrenceMachineCore.follow]⟩
  | cons index selected rest ih =>
      obtain ⟨trace, length, followed⟩ := ih (prior ++ emit _)
      refine ⟨index :: trace, by simp [length], ?_⟩
      simpa [OccurrenceMachineCore.follow, machine, List.getElem?_map,
        selected, List.append_assoc] using followed

end Steps

theorem follow_reflects (base : OccurrenceMachineCore Term State Answer) (emit : State → List Event)
    (trace : List Nat) (before final : State) (prior observed : List Event)
    (followed : (machine base emit).follow (before, prior) trace = some (final, observed)) :
    ∃ events, observed = prior ++ events ∧ Steps base emit trace.length events before final := by
  induction trace generalizing before prior with
  | nil =>
      simp only [OccurrenceMachineCore.follow, Option.some.injEq, Prod.mk.injEq] at followed
      obtain ⟨rfl, rfl⟩ := followed
      exact ⟨[], by simp, .refl _⟩
  | cons index trace ih =>
      change (((base.next before).map fun next => (next, prior ++ emit before))[index]? >>= fun next =>
        (machine base emit).follow next trace) = some (final, observed) at followed
      rw [List.getElem?_map] at followed
      cases selected : (base.next before)[index]? with
      | none => simp [selected] at followed
      | some next =>
          simp only [selected, Option.map_some] at followed
          obtain ⟨events, equation, path⟩ := ih next (prior ++ emit before) followed
          exact ⟨emit before ++ events, by simpa [List.append_assoc] using equation,
            .cons index selected path⟩

end Mettapedia.Machines.OccurrenceObservation
