import Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch

/-!
# Native dispatch beneath arbitrary retained context callers

The path describes holes in the existing contextual control, not a new
evaluator. Every stored context identity and inner continuation stays in its
original position. The primitive operation runs in the active leaf context;
its reached world is shared by all enclosing callers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual

inductive CallPath (Context : Type) where
  | here
  | under (child : Context) (inner : List Continuation) (rest : CallPath Context)

def CallPath.fill {Context : Type} : CallPath Context → Control Context → Control Context
  | .here, control => control
  | .under child inner rest, control => .context child (rest.fill control) inner

def CallPath.active {Context : Type} : CallPath Context → Context → Context
  | .here, root => root
  | .under child _ rest, _ => rest.active child

theorem CallPath.lift_local {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} (path : CallPath Context) (root : Context) (stack : List Continuation)
    {world reached : World} {before after : Control Context}
    (edge : ∀ inner, WorldLocalStep (admission := environment.arguments) environment.view environment.services
      environment.dispatch environment.lookup policy world (path.active root) (before, inner) reached (after, inner)) :
    WorldLocalStep (admission := environment.arguments) environment.view environment.services environment.dispatch
      environment.lookup policy world root (path.fill before, stack) reached (path.fill after, stack) := by
  induction path generalizing root stack with
  | here => exact edge stack
  | under child inner rest ih => exact .context (ih child inner edge)

def resumeAt {Context World : Type} (dispatch : Spec.Eval.GroundedDispatch)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (operator : Atom) (arguments : List Atom) (reached : World) (plan : NativeReplyPlan) :
    WorldConfiguration Context World :=
  let leaf := RetainedNativeDispatch.resumeNative dispatch before live scope value expected operator arguments reached plan
  {before with world := reached, control := path.fill leaf.control}

theorem focused_step {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (outcome : GroundedResult Entry.Value) (reached : World) (plan : NativeReplyPlan)
    (atCall : before.control = path.fill (.work (.call live scope value expected activation)))
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase)
    (produced : environment.services.groundedAt (path.active before.context) before.world live scope activation value outcome reached)
    (prepared : NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan) :
    WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      before (resumeAt environment.dispatch path before live scope value expected operator arguments reached plan) := by
  cases before with
  | mk world root control stack emitted =>
    dsimp only at atCall produced ⊢
    subst control
    cases plan with
    | done rows => exact .internal (path.lift_local root stack fun inner =>
        .callGroundedDone shape executable notError produced prepared)
    | resume rows => exact .internal (path.lift_local root stack fun inner =>
        .callGroundedResume shape executable notError produced prepared)

theorem focused_source_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (answers : List Result) (finalWorld : World)
    (atCall : before.control = path.fill (.work (.call live scope value expected activation)))
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase) :
    before.SourceRel environment policy answers finalWorld ↔
      ∃ outcome reached plan,
        environment.services.groundedAt (path.active before.context) before.world live scope activation value outcome reached ∧
        NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan ∧
        (resumeAt environment.dispatch path before live scope value expected operator arguments reached plan).SourceRel
          environment policy answers finalWorld := by
  constructor
  · intro source
    induction path generalizing before answers finalWorld with
    | here =>
      simpa only [CallPath.fill, CallPath.active, resumeAt, RetainedNativeDispatch.resumeNative] using
        (RetainedNativeDispatch.retained_source_iff environment policy before live scope value expected activation operator arguments
          answers finalWorld atCall shape executable notError).mp source
    | under child inner rest ih =>
      obtain ⟨current, pending, callerWorld, controlled, continued, emitted⟩ := source
      rw [atCall] at controlled
      cases controlled with
      | context childSource innerContinued =>
        let childBefore : WorldConfiguration Context World :=
          ⟨before.world, child, rest.fill (.work (.call live scope value expected activation)), inner, []⟩
        have childCompleted : childBefore.SourceRel environment policy current callerWorld :=
          ⟨_, current, _, childSource, innerContinued, rfl⟩
        obtain ⟨outcome, reached, plan, produced, prepared, remaining⟩ := ih childBefore current callerWorld rfl childCompleted
        refine ⟨outcome, reached, plan, produced, prepared, ?_⟩
        obtain ⟨raw, restRows, childWorld, next, innerTail, same⟩ := remaining
        have rowsEq : current = restRows := by simpa only [resumeAt, childBefore, List.nil_append] using same
        subst restRows
        refine ⟨current, pending, callerWorld, ?_, continued, emitted⟩
        exact .context next innerTail
  · rintro ⟨outcome, reached, plan, produced, prepared, remaining⟩
    exact RecursiveExecution.Contextual.Stateful.retained_prefix
      (.single (focused_step environment policy path before live scope value expected activation operator arguments
        outcome reached plan atCall shape executable notError produced prepared)) remaining

end Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus
