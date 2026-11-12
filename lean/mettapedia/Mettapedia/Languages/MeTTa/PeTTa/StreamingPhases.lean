import Mettapedia.Languages.MeTTa.PeTTa.Streaming

/-!
# Independent placement rules for existing unifying phases

The rules specify which return continuation is installed after one actual
source phase. They retain the reached world, put older alternatives on the
agenda once, and allocate distinct collection or runtime-call delimiters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming

def ordinaryFrame : Unifying.Frame → Bool
  | .collect _ | .dynamicCall | .sequence _ _ => false
  | _ => true

inductive Placement (state : State) (after : Unifying.Configuration)
    (caller : List Frame) (older : List Job) : State → Prop where
  | plain (frames : after.frames = []) :
      Placement state after caller older
        {state with
          world := World.fromConfiguration after
          agenda := .execute ⟨after.control,caller⟩ :: older}
  | collection {bindings} (frames : after.frames = [.collect bindings]) :
      Placement state after caller older
        (openCollection {state with world := World.fromConfiguration after} bindings after.control caller older)
  | handler (frames : after.frames = [.dynamicCall]) :
      Placement state after caller older
        (openHandler {state with world := World.fromConfiguration after} after.control caller older)
  | waiting {frame} (frames : after.frames = [frame]) (ordinary : ordinaryFrame frame = true) :
      Placement state after caller older
        {state with
          world := World.fromConfiguration after
          agenda := .execute ⟨after.control,.source frame :: caller⟩ :: older}

theorem Placement.computed {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target) :
    enqueuePhase state after caller older = some target := by
  cases placement with
  | plain frames => simp only [enqueuePhase,frames]
  | collection frames => simp only [enqueuePhase,frames]
  | handler frames => simp only [enqueuePhase,frames]
  | @waiting frame frames ordinary =>
      cases frame <;> simp_all only [ordinaryFrame,Bool.false_eq_true,enqueuePhase]

theorem placement_of_computed (state : State) (after : Unifying.Configuration)
    (caller : List Frame) (older : List Job) (target : State)
    (computed : enqueuePhase state after caller older = some target) :
    Placement state after caller older target := by
  cases frames : after.frames with
  | nil =>
      simp only [enqueuePhase,frames,Option.some.injEq] at computed
      subst target
      exact .plain frames
  | cons frame rest =>
      cases rest with
      | cons second more => simp only [enqueuePhase,frames] at computed; cases computed
      | nil =>
          cases frame
          case collect bindings =>
            simp only [enqueuePhase,frames,Option.some.injEq] at computed
            subst target
            exact .collection frames
          case dynamicCall =>
            simp only [enqueuePhase,frames,Option.some.injEq] at computed
            subst target
            exact .handler frames
          case sequence pending completed => simp only [enqueuePhase,frames] at computed; cases computed
          all_goals
            simp only [enqueuePhase,frames,Option.some.injEq] at computed
            subst target
            exact .waiting frames rfl

theorem placement_iff (state : State) (after : Unifying.Configuration)
    (caller : List Frame) (older : List Job) (target : State) :
    enqueuePhase state after caller older = some target ↔ Placement state after caller older target :=
  ⟨placement_of_computed state after caller older target,Placement.computed⟩

theorem Placement.world {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target) :
    target.world = World.fromConfiguration after := by cases placement <;> rfl

theorem Placement.answers {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target) : target.answers = state.answers := by
  cases placement <;> rfl

theorem Placement.boundary_mono {state : State} {after : Unifying.Configuration}
    {caller : List Frame} {older : List Job} {target : State}
    (placement : Placement state after caller older target) : state.nextBoundary ≤ target.nextBoundary := by
  cases placement with
  | plain | waiting => exact Nat.le_refl _
  | collection | handler => exact Nat.le_succ _

theorem world_roundtrip (world : World) (control : Unifying.Control) (frames : List Unifying.Frame) :
    World.fromConfiguration (world.configuration control frames) = world := by cases world; rfl

end Mettapedia.Languages.MeTTa.PeTTa.Streaming
