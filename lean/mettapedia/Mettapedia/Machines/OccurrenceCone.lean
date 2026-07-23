import Mettapedia.Machines.ConeDuality
import Mettapedia.Machines.OccurrenceMachine

/-!
# Occurrence traces and reachability cones

Transition-index traces retain occurrence identity; reachability cones retain
only the existence of a path. This module proves that forgetting occurrence
identity from an executable trace gives exactly the ordinary reflexive-
transitive reachability relation, and conversely that every reachable state has
at least one executable occurrence trace.
-/

namespace Mettapedia.Machines

namespace OccurrenceMachineCore

variable {Term State Answer : Type}

/-- The proposition-valued transition relation obtained by forgetting which
successor-list position witnessed a transition. -/
def StepRel (M : OccurrenceMachineCore Term State Answer)
    (state next : State) : Prop :=
  next ∈ M.next state

/-- Zero-or-more occurrence-machine transitions after forgetting edge index. -/
abbrev Steps (M : OccurrenceMachineCore Term State Answer) :
    State → State → Prop :=
  Reaches M.StepRel

/-- Executing a transition-index trace yields ordinary reachability after the
indices are forgotten. -/
theorem follow_to_steps (M : OccurrenceMachineCore Term State Answer)
    {state final : State} {trace : List Nat}
    (followed : M.follow state trace = some final) :
    M.Steps state final := by
  induction trace generalizing state with
  | nil =>
      have stateFinal : state = final := by
        simpa [follow] using Option.some.inj followed
      subst final
      exact .refl
  | cons edge rest ih =>
      cases edgeLookup : (M.next state)[edge]? with
      | none => simp [follow, edgeLookup] at followed
      | some target =>
          have tailFollow : M.follow target rest = some final := by
            simpa [follow, edgeLookup] using followed
          have first : M.StepRel state target :=
            List.mem_iff_getElem?.mpr ⟨edge, edgeLookup⟩
          exact Relation.ReflTransGen.head first (ih tailFollow)

/-- Every ordinary reachable endpoint has at least one executable
transition-index trace. If duplicate edges exist, this deliberately chooses a
witness rather than claiming uniqueness. -/
theorem steps_to_follow (M : OccurrenceMachineCore Term State Answer)
    {state final : State} (steps : M.Steps state final) :
    ∃ trace, M.follow state trace = some final := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | @head state next first tail ih =>
      obtain ⟨rest, restFollow⟩ := ih
      obtain ⟨edge, edgeLookup⟩ :=
        List.mem_iff_getElem?.mp (show next ∈ M.next state from first)
      exact ⟨edge :: rest, by simp [follow, edgeLookup, restFollow]⟩

/-- Reachability and existence of an occurrence trace agree exactly. -/
theorem steps_iff_exists_follow
    (M : OccurrenceMachineCore Term State Answer)
    {state final : State} :
    M.Steps state final ↔
      ∃ trace, M.follow state trace = some final :=
  ⟨M.steps_to_follow, fun ⟨_, followed⟩ => M.follow_to_steps followed⟩

/-- The forward lightcone from one machine state is exactly the set of
endpoints having an executable occurrence trace. -/
theorem mem_forwardCone_singleton_iff_exists_follow
    (M : OccurrenceMachineCore Term State Answer)
    {state final : State} :
    final ∈ forwardCone M.StepRel ({state} : Set State) ↔
      ∃ trace, M.follow state trace = some final := by
  rw [mem_forwardCone]
  simpa using M.steps_iff_exists_follow (state := state) (final := final)

/-- Every emitted answer occurrence has an endpoint in the start state's
forward cone; its transition trace is the reachability witness. -/
theorem answerTrace_endpoint_mem_forwardCone
    (M : OccurrenceMachineCore Term State Answer)
    {depth : Nat} {state : State} {answer : Answer} {trace : List Nat}
    (emitted : (answer, trace) ∈ M.answerTraces depth state) :
    ∃ final,
      final ∈ forwardCone M.StepRel ({state} : Set State) ∧
      M.answer final = some answer := by
  obtain ⟨final, followed, observed⟩ := M.answerTraces_sound emitted
  exact ⟨final,
    M.mem_forwardCone_singleton_iff_exists_follow.mpr ⟨trace, followed⟩,
    observed⟩

/-- Every pending occurrence also lies in the same forward cone, but its
endpoint is a live non-answer rather than a completed answer. -/
theorem pendingTrace_endpoint_mem_forwardCone
    (M : OccurrenceMachineCore Term State Answer)
    {depth : Nat} {state pending : State} {trace : List Nat}
    (emitted : (pending, trace) ∈ M.pendingTraces depth state) :
    pending ∈ forwardCone M.StepRel ({state} : Set State) ∧
      M.answer pending = none ∧ M.next pending ≠ [] := by
  obtain ⟨followed, unobserved, live⟩ := M.pendingTraces_sound emitted
  exact ⟨M.mem_forwardCone_singleton_iff_exists_follow.mpr
      ⟨trace, followed⟩,
    unobserved, live⟩

/-! ## Occurrence identity is finer than cone reachability -/

/-- Both duplicate transition occurrences witness the same cone endpoint. -/
example : duplicateExample.follow .root [0] = some .done ∧
    duplicateExample.follow .root [1] = some .done := by
  decide

/-- The endpoint therefore lies in the ordinary forward cone. -/
example : DuplicateExampleState.done ∈
    forwardCone duplicateExample.StepRel
      ({DuplicateExampleState.root} : Set DuplicateExampleState) := by
  rw [duplicateExample.mem_forwardCone_singleton_iff_exists_follow]
  exact ⟨[0], rfl⟩

/-- A non-existent successor occurrence is rejected rather than becoming a
spurious cone edge. -/
example : duplicateExample.follow .root [2] = none := rfl

end OccurrenceMachineCore

end Mettapedia.Machines
