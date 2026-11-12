import Mettapedia.Languages.MeTTa.PeTTa.StreamingPhases

/-!
# Streaming delivery with explicit caller and collection boundaries

One packet runs its saved continuation. An enclosing collection records it;
first demand removes only its own producer prefix; returning from a runtime
call leaves the caller outside the callee's exception boundary. Each actual
source-return phase is justified by Unifying.Transition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

open Unifying (Answer)
open List.FirstSelection (After Change)

inductive Delivery (registry : SpaceSemantics.Program) (state : State) (answer : Answer) :
    List Frame → List Job → State → Prop where
  | root (older) : Delivery registry state answer [] older
      {state with agenda := older,answers := state.answers ++ [answer]}
  | source {frame caller older after target} :
      Unifying.Transition registry (state.world.configuration (.returned [answer]) [frame]) after →
      Placement state after caller older target →
      Delivery registry state answer (.source frame :: caller) older target
  | collection {key caller older changed} :
      Change (collectionChange key answer) older changed →
      Delivery registry state answer (.collection key :: caller) older {state with agenda := changed}
  | handler (key caller older) : Delivery registry state answer (.handler key :: caller) older
      {state with agenda := .execute ⟨.returned [answer],caller⟩ :: older}
  | first {key caller older remaining} :
      After (firstMarker key) older remaining →
      Delivery registry state answer (.first key :: caller) older
        {state with agenda := .execute ⟨.returned [answer],caller⟩ :: remaining}

theorem Delivery.computed {registry : SpaceSemantics.Program} {state : State} {answer : Answer}
    {frames : List Frame} {older : List Job} {target : State}
    (delivery : Delivery registry state answer frames older target) :
    returnAnswer registry state answer frames older = some target := by
  cases delivery with
  | root => rfl
  | source source placement =>
      simp only [returnAnswer,Unifying.transition_step source,bind,Option.bind_some,placement.computed]
  | collection changed =>
      simp only [returnAnswer,collectAnswer,changed.computed,Option.map_some]
  | handler => rfl
  | first after => simp only [returnAnswer,after.computed,Option.map_some]

theorem delivery_of_computed (registry : SpaceSemantics.Program) (state : State) (answer : Answer)
    (frames : List Frame) (older : List Job) (target : State)
    (computed : returnAnswer registry state answer frames older = some target) :
    Delivery registry state answer frames older target := by
  cases frames with
  | nil =>
      simp only [returnAnswer,Option.some.injEq] at computed
      subst target
      exact .root older
  | cons frame caller =>
      cases frame with
      | source frame =>
          simp only [returnAnswer,bind,Option.bind_eq_some_iff] at computed
          obtain ⟨after,source,placed⟩ := computed
          exact .source (Unifying.step_transition source)
            (placement_of_computed state after caller older target placed)
      | collection key =>
          simp only [returnAnswer,Option.map_eq_some_iff] at computed
          obtain ⟨changed,found,rfl⟩ := computed
          exact .collection ((List.FirstSelection.change_iff _ _ _).mp found)
      | handler key =>
          simp only [returnAnswer,Option.some.injEq] at computed
          subst target
          exact .handler key caller older
      | first key =>
          simp only [returnAnswer,Option.map_eq_some_iff] at computed
          obtain ⟨remaining,found,rfl⟩ := computed
          exact .first ((List.FirstSelection.after_iff _ _ _).mp found)

theorem delivery_iff (registry : SpaceSemantics.Program) (state : State) (answer : Answer)
    (frames : List Frame) (older : List Job) (target : State) :
    returnAnswer registry state answer frames older = some target ↔
      Delivery registry state answer frames older target :=
  ⟨delivery_of_computed registry state answer frames older target,Delivery.computed⟩

theorem Delivery.uses_mono {registry : SpaceSemantics.Program} {state : State} {answer : Answer}
    {frames : List Frame} {older : List Job} {target : State}
    (delivery : Delivery registry state answer frames older target) :
    state.world.uses ≤ target.world.uses := by
  cases delivery with
  | source source placed =>
      rw [placed.world]
      exact ScopedSource.transition_uses_mono source
  | _ => exact Nat.le_refl _

theorem Delivery.boundary_mono {registry : SpaceSemantics.Program} {state : State} {answer : Answer}
    {frames : List Frame} {older : List Job} {target : State}
    (delivery : Delivery registry state answer frames older target) :
    state.nextBoundary ≤ target.nextBoundary := by
  cases delivery with
  | source _ placed => exact placed.boundary_mono
  | _ => exact Nat.le_refl _

inductive Handles : List Frame → Nat → Prop where
  | here (key caller) : Handles (.handler key :: caller) key
  | source {frame caller key} : Handles caller key → Handles (.source frame :: caller) key
  | collection {frame caller key} : Handles caller key → Handles (.collection frame :: caller) key
  | first {frame caller key} : Handles caller key → Handles (.first frame :: caller) key

theorem Handles.computed {frames : List Frame} {key : Nat} (handler : Handles frames key) :
    nearestHandler frames = some key := by
  induction handler with
  | here => rfl
  | source _ ih | collection _ ih | first _ ih => exact ih

theorem handles_of_computed (frames : List Frame) (key : Nat)
    (found : nearestHandler frames = some key) : Handles frames key := by
  induction frames with
  | nil => cases found
  | cons frame caller ih =>
      cases frame with
      | handler actual =>
          simp only [nearestHandler,Option.some.injEq] at found
          subst key
          exact .here actual caller
      | source frame => exact .source (ih found)
      | collection frame => exact .collection (ih found)
      | first frame => exact .first (ih found)

theorem handles_iff (frames : List Frame) (key : Nat) :
    nearestHandler frames = some key ↔ Handles frames key :=
  ⟨handles_of_computed frames key,Handles.computed⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
