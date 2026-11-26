import Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# The active scope of a live HE step

Separate the one current local task or returned batch from its enclosing
contexts. A parent retains its context identity and its continuation, not a
snapshot of the world. The resulting presentation distinguishes a local
step, returning to a parent, and publishing to the observer. It is an exact
reorganization of the contextual source judgment, including steps that
change the world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup Frame Policy Result WorldServices)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual
  (Task Control Continuation WorldConfiguration UnscopedControl)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual
  (WorldLocalStepWith WorldStepWith)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

inductive Leaf where
  | work (task : Task)
  | returning (answers : List Result)

def Leaf.control {Context : Type} : Leaf → Control Context
  | .work task => .work task
  | .returning answers => .returning answers

structure Parent (Context : Type) where
  scope : Context
  stack : List Continuation

structure Focus (Context World : Type) where
  world : World
  scope : Context
  leaf : Leaf
  stack : List Continuation
  parents : List (Parent Context)
  emitted : List Result

variable {Context World : Type}

/-- The nearest parent is first. No world is saved at a parent. -/
def locate (world : World) (scope : Context) (control : Control Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    Focus Context World :=
  match control with
  | .work task => ⟨world, scope, .work task, stack, parents, emitted⟩
  | .returning answers => ⟨world, scope, .returning answers, stack, parents, emitted⟩
  | .context child next inner =>
      locate world child next inner (⟨scope, stack⟩ :: parents) emitted

def enclose (world : World) (scope : Context) (control : Control Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    WorldConfiguration Context World :=
  match parents with
  | [] => ⟨world, scope, control, stack, emitted⟩
  | parent :: outer =>
      enclose world parent.scope (.context scope control stack) parent.stack outer emitted

def focus (state : WorldConfiguration Context World) : Focus Context World :=
  locate state.world state.context state.control state.stack [] state.emitted

def restore (state : Focus Context World) : WorldConfiguration Context World :=
  enclose state.world state.scope state.leaf.control state.stack state.parents state.emitted

@[simp] theorem locate_leaf (world : World) (scope : Context) (leaf : Leaf)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    locate world scope leaf.control stack parents emitted = ⟨world, scope, leaf, stack, parents, emitted⟩ := by
  cases leaf <;> rfl

theorem restore_locate (world : World) (scope : Context) (control : Control Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    restore (locate world scope control stack parents emitted) =
      enclose world scope control stack parents emitted := by
  induction control generalizing scope stack parents with
  | work | returning => rfl
  | context child control inner ih => exact ih child inner (⟨scope, stack⟩ :: parents)

theorem focus_enclose (world : World) (scope : Context) (control : Control Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    focus (enclose world scope control stack parents emitted) = locate world scope control stack parents emitted := by
  induction parents generalizing scope control stack with
  | nil => rfl
  | cons parent outer ih => exact ih parent.scope (.context scope control stack) parent.stack

@[simp] theorem restore_focus (state : WorldConfiguration Context World) : restore (focus state) = state := by
  cases state
  exact restore_locate _ _ _ _ [] _

@[simp] theorem focus_restore (state : Focus Context World) : focus (restore state) = state := by
  cases state
  simp only [restore, focus_enclose, locate_leaf]

def focusing : WorldConfiguration Context World ≃ Focus Context World where
  toFun := focus
  invFun := restore
  left_inv := restore_focus
  right_inv := focus_restore

section Steps

variable {admission : ArgumentService} {view : World → Context → Space}
  {services : WorldServices Context World} {dispatch : GroundedDispatch}
  {lookup : CastLookup} {policy : Policy}

/-- Only the first case asks the dialect for a local step. Its input is a
leaf, so its proof cannot use the context recursion or context return
rules. This does not make a recursive evaluator reply a primitive. -/
inductive Move (admission : ArgumentService) (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) : Focus Context World → Focus Context World → Prop where
  | perform {before : Focus Context World} {world : World} {control : Control Context}
      {stack : List Continuation} :
      WorldLocalStepWith admission view services dispatch lookup policy before.world before.scope
        (before.leaf.control, before.stack) world (control, stack) →
      Move admission view services dispatch lookup policy before
        (locate world before.scope control stack before.parents before.emitted)
  | resume {world : World} {child : Context} {parent : Parent Context} {outer : List (Parent Context)}
      {answers emitted : List Result} :
      Move admission view services dispatch lookup policy
        ⟨world, child, .returning answers, [], parent :: outer, emitted⟩
        ⟨world, parent.scope, .returning answers, parent.stack, outer, emitted⟩
  | publish {world : World} {scope : Context} {first : Result} {rest emitted : List Result} :
      Move admission view services dispatch lookup policy
        ⟨world, scope, .returning (first :: rest), [], [], emitted⟩
        ⟨world, scope, .returning rest, [], [], emitted ++ [first]⟩

theorem locate_local_step
    {world afterWorld : World} {scope : Context} {before after : Control Context × List Continuation}
    (step : WorldLocalStepWith admission view services dispatch lookup policy world scope
      before afterWorld after)
    (parents : List (Parent Context)) (emitted : List Result) :
    Move admission view services dispatch lookup policy
      (locate world scope before.1 before.2 parents emitted)
      (locate afterWorld scope after.1 after.2 parents emitted) := by
  induction step generalizing parents with
  | core incoming unmanaged stepped outgoing =>
    cases incoming <;> exact .perform (.core (by constructor) unmanaged stepped outgoing)
  | context stepped ih => exact ih (_ :: parents)
  | contextReturn => exact .resume
  | evalc => exact .perform .evalc
  | metta => exact .perform .metta
  | contextSpace => exact .perform .contextSpace
  | native authorized => exact .perform (.native authorized)
  | callGroundedDone shape exec ordinary ran returned =>
    exact .perform (.callGroundedDone shape exec ordinary ran returned)
  | callGroundedResume shape exec ordinary ran returned =>
    exact .perform (.callGroundedResume shape exec ordinary ran returned)
  | invocationGroundedDone shape exec ran returned =>
    exact .perform (.invocationGroundedDone shape exec ran returned)
  | invocationGroundedResume shape exec ran returned =>
    exact .perform (.invocationGroundedResume shape exec ran returned)
  | collapseEnter provided => exact .perform (.collapseEnter provided)
  | collectEnter provided => exact .perform (.collectEnter provided)
  | captureNil provided => exact .perform (.captureNil provided)
  | captureEmpty provided empty => exact .perform (.captureEmpty provided empty)
  | captureOne provided nonempty captured => exact .perform (.captureOne provided nonempty captured)
  | superposeEnter provided => exact .perform (.superposeEnter provided)
  | restoreNil provided => exact .perform (.restoreNil provided)
  | restoreOne provided restored merged => exact .perform (.restoreOne provided restored merged)
  | restoreRejected provided restored conflict => exact .perform (.restoreRejected provided restored conflict)

theorem enclose_local_step
    {world afterWorld : World} {scope : Context} {before after : Control Context}
    {stack remaining : List Continuation}
    (step : WorldLocalStepWith admission view services dispatch lookup policy world scope
      (before, stack) afterWorld (after, remaining))
    (parents : List (Parent Context)) (emitted : List Result) :
    WorldStepWith admission view services dispatch lookup policy
      (enclose world scope before stack parents emitted) (enclose afterWorld scope after remaining parents emitted) := by
  induction parents generalizing scope before after stack remaining with
  | nil => exact .internal step
  | cons parent outer ih => exact ih (.context step)

theorem focus_step {before after : WorldConfiguration Context World}
    (step : WorldStepWith admission view services dispatch lookup policy before after) :
    Move admission view services dispatch lookup policy (focus before) (focus after) := by
  cases step with
  | internal step => exact locate_local_step step [] _
  | publish => exact .publish

theorem restore_step {before after : Focus Context World}
    (step : Move admission view services dispatch lookup policy before after) :
    WorldStepWith admission view services dispatch lookup policy (restore before) (restore after) := by
  cases step with
  | perform step =>
    rw [restore_locate]
    exact enclose_local_step step _ _
  | resume => exact enclose_local_step .contextReturn _ _
  | publish => exact .publish

theorem focus_step_iff (before after : WorldConfiguration Context World) :
    Move admission view services dispatch lookup policy (focus before) (focus after) ↔
      WorldStepWith admission view services dispatch lookup policy before after :=
  ⟨fun step => by simpa only [restore_focus] using restore_step step, focus_step⟩

def theory (admission : ArgumentService) (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) : GSLT :=
  equalityGSLT (Focus Context World) (Move admission view services dispatch lookup policy)

private theorem locate_retains_history (world : World) (scope : Context) (control : Control Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result) :
    (locate world scope control stack parents emitted).emitted = emitted := by
  induction control generalizing scope stack parents with
  | work | returning => rfl
  | context child next inner ih => exact ih child inner (_ :: parents)

/-- Returning from a nested context never publishes to the outer observer.
This includes a local effect that changes the world in that context. -/
theorem no_inner_publication {before after : Focus Context World}
    (step : Move admission view services dispatch lookup policy before after) (nested : before.parents ≠ []) :
    after.emitted = before.emitted := by
  cases step with
  | perform => exact locate_retains_history _ _ _ _ _ _
  | resume => rfl
  | publish => exact False.elim (nested rfl)

/-- A focused step does not ask for the space contents of any of its
inactive ancestors. It still uses the actual world at all effect ports.
This is a one-step theorem, not a license to reuse the old parent view
after returning to it. -/
theorem current_view_iff {other : World → Context → Space} (before after : Focus Context World)
    (same : view before.world before.scope = other before.world before.scope) :
    Move admission view services dispatch lookup policy before after ↔
      Move admission other services dispatch lookup policy before after := by
  have carry : ∀ {a b : World → Context → Space},
      a before.world before.scope = b before.world before.scope →
      Move admission a services dispatch lookup policy before after →
      Move admission b services dispatch lookup policy before after := by
    intro a b agrees step
    cases step with
    | perform localStep =>
      apply Move.perform
      apply HEExecution.local_rewrite_of_same_snapshot localStep
      have noChildren : (before.leaf.control : Control Context).contexts = [] := by
        cases before.leaf <;> rfl
      intro scope present
      rw [noChildren] at present
      exact (List.mem_singleton.mp present).symm ▸ agrees
    | resume => exact .resume
    | publish => exact .publish
  exact ⟨carry same, carry same.symm⟩

theorem source_step_current_view_iff {other : World → Context → Space}
    (before after : WorldConfiguration Context World)
    (same : view before.world (focus before).scope = other before.world (focus before).scope) :
    WorldStepWith admission view services dispatch lookup policy before after ↔
      WorldStepWith admission other services dispatch lookup policy before after := by
  have world_eq : (focus before).world = before.world := by
    have aux : ∀ (scope : Context) (control : Control Context) (stack : List Continuation)
        (parents : List (Parent Context)),
        (locate before.world scope control stack parents before.emitted).world = before.world := by
      intro scope control stack parents
      induction control generalizing scope stack parents with
      | work | returning => rfl
      | context child control inner ih => exact ih child inner (_ :: parents)
    exact aux _ _ _ _
  have sameCurrent : view (focus before).world (focus before).scope =
      other (focus before).world (focus before).scope := by simpa only [world_eq] using same
  exact (focus_step_iff before after).symm.trans
    ((current_view_iff (focus before) (focus after) sameCurrent).trans (focus_step_iff before after))

/-- The unique administrative action on a returned batch whose local
continuation is empty. An inner batch is transferred as a whole; at
the root, publication transfers one occurrence. -/
def returnNext (world : World) (scope : Context) (answers : List Result)
    (parents : List (Parent Context)) (emitted : List Result) : Option (Focus Context World) :=
  match parents with
  | parent :: outer => some ⟨world, parent.scope, .returning answers, parent.stack, outer, emitted⟩
  | [] => match answers with
    | [] => none
    | first :: rest => some ⟨world, scope, .returning rest, [], [], emitted ++ [first]⟩

private theorem no_local_return_without_continuation (world : World) (scope : Context)
    (answers : List Result) {next : World} {output : Control Context × List Continuation}
    (step : WorldLocalStepWith admission view services dispatch lookup policy world scope
      (.returning answers, []) next output) : False := by
  cases step with
  | core incoming _ stepped _ =>
    cases incoming
    cases stepped

theorem return_step_iff (world : World) (scope : Context) (answers : List Result)
    (parents : List (Parent Context)) (emitted : List Result) (after : Focus Context World) :
    Move admission view services dispatch lookup policy
      ⟨world, scope, .returning answers, [], parents, emitted⟩ after ↔
        returnNext world scope answers parents emitted = some after := by
  constructor
  · intro step
    cases step with
    | perform stepped => exact (no_local_return_without_continuation world scope answers stepped).elim
    | resume => rfl
    | publish => rfl
  · intro next
    cases parents with
    | cons parent outer =>
      change some ⟨world, parent.scope, .returning answers, parent.stack, outer, emitted⟩ = some after at next
      cases next
      exact .resume
    | nil =>
      cases answers with
      | nil => cases next
      | cons first rest =>
        change some ⟨world, scope, .returning rest, [], [], emitted ++ [first]⟩ = some after at next
        cases next
        exact .publish

end Steps

/-! ## Primitive native invocation -/

/-- The actual minimal-language call-native shape. The host receives the
active identity and shared world, not the stack or parent identities. -/
structure NativeRequest where
  live : List Atom
  scope : List String
  caller : Option Atom
  status : Entry.Status
  name : Entry.Value
  operation : Entry.Value
  argument : Entry.Value
  frame : Frame

def NativeRequest.task (request : NativeRequest) : Task :=
  .minimal request.live request.scope request.caller
    (.expression request.status [.symbol "call-native", request.name, request.operation, request.argument])
    request.frame

/-- Recognition is purely syntactic and retains all request fields. It
does not ask the native service or authorize an effect. -/
def NativeRequest.recognize : Task → Option NativeRequest
  | .minimal live scope caller (.expression status [.symbol "call-native", name, operation, argument]) frame =>
    some ⟨live, scope, caller, status, name, operation, argument, frame⟩
  | _ => none

@[simp] theorem NativeRequest.recognize_task (request : NativeRequest) :
    recognize request.task = some request := by
  cases request
  rfl

theorem NativeRequest.recognize_exact {task : Task} {request : NativeRequest}
    (recognized : recognize task = some request) : request.task = task := by
  unfold recognize at recognized
  split at recognized
  · cases recognized
    rfl
  · cases recognized

section Native

variable {admission : ArgumentService} {view : World → Context → Space}
  {services : WorldServices Context World} {dispatch : GroundedDispatch}
  {lookup : CastLookup} {policy : Policy}

/-- Inverting the real source rules: the native port is exactly what may
complete this already focused request. Failure to have service evidence
does not produce a recursive evaluator reply or a publication. -/
theorem native_step_iff (request : NativeRequest) (world : World) (scope : Context)
    (stack : List Continuation) (parents : List (Parent Context)) (emitted : List Result)
    (after : Focus Context World) :
    Move admission view services dispatch lookup policy
        ⟨world, scope, .work request.task, stack, parents, emitted⟩ after ↔
      ∃ results updated,
        services.nativeCall scope world request.name.erase request.operation.erase request.argument.erase
          request.frame results updated ∧
        after = ⟨updated, scope, .returning results, stack, parents, emitted⟩ := by
  rcases request with ⟨live, names, caller, status, name, operation, argument, frame⟩
  constructor
  · intro step
    cases step with
    | perform call =>
      change WorldLocalStepWith admission view services dispatch lookup policy world scope
        (Control.work (.minimal live names caller (.expression status [.symbol "call-native", name, operation, argument])
          frame), stack) _ _ at call
      generalize shape : (Control.work (.minimal live names caller
        (.expression status [.symbol "call-native", name, operation, argument]) frame), stack) = input at call
      cases call with
      | core unscoped unmanaged stepped outgoing =>
        cases unscoped
        all_goals
          cases stepped <;> simp at shape
        obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := shape
        exact False.elim (by
          have noninstruction : Minimal.embeddedInstruction
              (Entry.Value.expression status [.symbol "call-native", name, operation, argument]).erase = false :=
            by assumption
          simp [Entry.Value.erase, Minimal.embeddedInstruction] at noninstruction)
      | native authorized =>
        simp only [Prod.mk.injEq, Control.work.injEq, Task.minimal.injEq,
          Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩, rfl⟩ := shape
        exact ⟨_, _, authorized, rfl⟩
      | _ => simp at shape
  · rintro ⟨results, updated, authorized, rfl⟩
    exact Move.perform
      (before := ⟨world, scope, .work (NativeRequest.mk live names caller status name operation argument frame).task,
        stack, parents, emitted⟩)
      (.native authorized)

end Native

end Mettapedia.Languages.MeTTa.SpaceTheory.HEFocused
