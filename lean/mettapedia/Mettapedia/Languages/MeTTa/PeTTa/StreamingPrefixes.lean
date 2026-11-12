import Mettapedia.Languages.MeTTa.PeTTa.StreamingSpec

/-!
# Source reachability and retained streaming prefixes

Every bounded endpoint is reached by the independent controller rules, and
every finite rule path is realized by the runner. Resumption retains the
entire agenda, collection markers, binding packets and reached shared world.
Logical allocations, scope markers and completed answers never go backwards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

open Mettapedia.Machines

theorem Delivery.answers_prefix {registry : SpaceSemantics.Program} {state target : State}
    {answer : Unifying.Answer} {frames : List Frame} {older : List Job}
    (delivery : Delivery registry state answer frames older target) :
    ∃ added, target.answers = state.answers ++ added := by
  cases delivery with
  | root => exact ⟨_,rfl⟩
  | source _ placed => exact ⟨[],by rw [placed.answers,List.append_nil]⟩
  | _ => exact ⟨[],(List.append_nil _).symm⟩

theorem Transition.answers_prefix {registry : SpaceSemantics.Program} {before after : State}
    (taken : Transition registry before after) :
    ∃ added, after.answers = before.answers ++ added := by
  cases taken with
  | answer _ delivered => exact delivered.answers_prefix
  | phase _ _ _ placed => exact ⟨[],by rw [placed.answers,List.append_nil]⟩
  | _ => exact ⟨[],(List.append_nil _).symm⟩

theorem Transition.uses_mono {registry : SpaceSemantics.Program} {before after : State}
    (taken : Transition registry before after) : before.world.uses ≤ after.world.uses := by
  cases taken with
  | collection_done => exact Nat.le_add_right _ _
  | answer _ delivered => exact delivered.uses_mono
  | phase _ _ source placed =>
      rw [placed.world]
      exact ScopedSource.transition_uses_mono source
  | _ => exact Nat.le_refl _

theorem Transition.boundary_mono {registry : SpaceSemantics.Program} {before after : State}
    (taken : Transition registry before after) : before.nextBoundary ≤ after.nextBoundary := by
  cases taken with
  | collection_enter | first_enter => exact Nat.le_succ _
  | answer _ delivered => exact delivered.boundary_mono
  | phase _ _ _ placed => exact placed.boundary_mono
  | _ => exact Nat.le_refl _

theorem advance_reachable (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) :
    Relation.ReflTransGen (Transition registry) state (advance registry fuel state) :=
  Relation.ReflTransGen.mono (fun _ _ computed => transition_of_computed registry _ _ computed)
    state (advance registry fuel state) (BoundedDeterministicRun.run_reachable (step registry) fuel state)

theorem path_iff_advance (registry : SpaceSemantics.Program) (before after : State) :
    Relation.ReflTransGen (Transition registry) before after ↔
      ∃ fuel, advance registry fuel before = after := by
  change Relation.ReflTransGen (Transition registry) before after ↔
    ∃ fuel, BoundedDeterministicRun.run (step registry) fuel before = after
  rw [← BoundedDeterministicRun.reachable_iff_run]
  constructor
  · exact Relation.ReflTransGen.mono (fun _ _ => Transition.computed) before after
  · exact Relation.ReflTransGen.mono (fun _ _ => transition_of_computed registry _ _) before after

/-- This equality resumes the paid residual, rather than restarting syntax
against its newer world or reconstructing its pending alternatives. -/
theorem advance_add (registry : SpaceSemantics.Program) (first second : Nat) (state : State) :
    advance registry (first + second) state = advance registry second (advance registry first state) :=
  BoundedDeterministicRun.run_add (step registry) first second state

theorem path_answers_prefix {registry : SpaceSemantics.Program} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) :
    ∃ added, after.answers = before.answers ++ added := by
  induction path with
  | refl => exact ⟨[],(List.append_nil _).symm⟩
  | tail _ taken ih =>
      obtain ⟨before,earlier⟩ := ih
      obtain ⟨later,following⟩ := taken.answers_prefix
      exact ⟨before ++ later,by rw [following,earlier,List.append_assoc]⟩

theorem path_uses_mono {registry : SpaceSemantics.Program} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) :
    before.world.uses ≤ after.world.uses := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ taken ih => exact ih.trans taken.uses_mono

theorem path_boundary_mono {registry : SpaceSemantics.Program} {before after : State}
    (path : Relation.ReflTransGen (Transition registry) before after) :
    before.nextBoundary ≤ after.nextBoundary := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ taken ih => exact ih.trans taken.boundary_mono

theorem advance_answers_prefix (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) :
    ∃ added, (advance registry fuel state).answers = state.answers ++ added :=
  path_answers_prefix (advance_reachable registry fuel state)

theorem advance_uses_mono (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) :
    state.world.uses ≤ (advance registry fuel state).world.uses :=
  path_uses_mono (advance_reachable registry fuel state)

theorem advance_boundary_mono (registry : SpaceSemantics.Program) (fuel : Nat) (state : State) :
    state.nextBoundary ≤ (advance registry fuel state).nextBoundary :=
  path_boundary_mono (advance_reachable registry fuel state)

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
