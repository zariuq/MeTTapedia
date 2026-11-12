import Mettapedia.Languages.MeTTa.HE.RecursiveExecution

/-!
# Native dispatch in a retained stateful HE caller

Applicability and argument production precede this boundary. An executable
native call is factored into its primitive host outcome, the reached world,
and its remaining language boundary. The caller stack and publication prefix
are retained. Completed host outcomes are not arguments to be evaluated again.

The source equivalence includes both finished and resumable native plans.
It is independent of a particular native implementation or prepared worker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual

theorem native_call_iff {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (results : List Result) (finalWorld : World)
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase) :
    Stateful.CallRel environment label world live scope value expected activation results finalWorld (policy := policy) ↔
      ∃ outcome reached plan,
        environment.services.groundedAt label world live scope activation value outcome reached ∧
        NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan ∧
        match plan with
        | .done rows => results = rows ∧ finalWorld = reached
        | .resume rows => Stateful.BoundaryBatchRel environment label reached live scope none
            (.native value (some expected) (environment.dispatch.valueProvenance operator arguments))
            rows results finalWorld (policy := policy) := by
  have host : Minimal.HostCall environment.dispatch value.erase := ⟨operator, arguments, shape, executable⟩
  constructor
  · intro source
    cases source with
    | error failed => exact False.elim (notError failed)
    | embedded _ notHost _ _ _ => exact False.elim (notHost host)
    | absent _ notGrounded _ => exact False.elim (notGrounded.1 host)
    | equations _ notGrounded _ _ _ => exact False.elim (notGrounded.1 host)
    | groundedDone shaped _ _ produced prepared =>
      have same := Atom.expression.inj (shaped.symm.trans shape)
      rcases List.cons.inj same with ⟨rfl, rfl⟩
      exact ⟨_, _, .done _, produced, prepared, rfl, rfl⟩
    | groundedResume shaped _ _ produced prepared boundary =>
      have same := Atom.expression.inj (shaped.symm.trans shape)
      rcases List.cons.inj same with ⟨rfl, rfl⟩
      exact ⟨_, _, .resume _, produced, prepared, boundary⟩
  · rintro ⟨outcome, reached, plan, produced, prepared, remaining⟩
    cases plan with
    | done rows =>
      obtain ⟨rfl, rfl⟩ := remaining
      exact .groundedDone shape executable notError produced prepared
    | resume rows => exact .groundedResume shape executable notError produced prepared remaining

def resumeNative {Context World : Type} (dispatch : Spec.Eval.GroundedDispatch)
    (before : WorldConfiguration Context World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (operator : Atom) (arguments : List Atom)
    (reached : World) (plan : NativeReplyPlan) : WorldConfiguration Context World :=
  {before with world := reached, control := match plan with
    | .done rows => .returning rows
    | .resume rows => .work (.boundaryBatch live scope none
        (.native value (some expected) (dispatch.valueProvenance operator arguments)) rows)}

theorem native_step {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (before : WorldConfiguration Context World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (outcome : GroundedResult Entry.Value) (reached : World)
    (plan : NativeReplyPlan)
    (atCall : before.control = .work (.call live scope value expected activation))
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase)
    (produced : environment.services.groundedAt before.context before.world live scope activation value outcome reached)
    (prepared : NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan) :
    WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      before (resumeNative environment.dispatch before live scope value expected operator arguments reached plan) := by
  cases before with
  | mk world label control stack emitted =>
    dsimp only at atCall produced ⊢
    subst control
    cases plan with
    | done rows => exact .internal (.callGroundedDone shape executable notError produced prepared)
    | resume rows => exact .internal (.callGroundedResume shape executable notError produced prepared)

/-- Every complete continuation from this dispatch point is represented by
one native outcome and a continuation in its reached world, and conversely.
This retains all source possibilities rather than selecting a convenient
producer result. The reverse direction follows an actual world transition. -/
theorem retained_source_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (before : WorldConfiguration Context World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (answers : List Result) (finalWorld : World)
    (atCall : before.control = .work (.call live scope value expected activation))
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase) :
    before.SourceRel environment policy answers finalWorld ↔
      ∃ outcome reached plan,
        environment.services.groundedAt before.context before.world live scope activation value outcome reached ∧
        NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan ∧
        (resumeNative environment.dispatch before live scope value expected operator arguments reached plan).SourceRel
          environment policy answers finalWorld := by
  constructor
  · rintro ⟨current, pending, childWorld, controlled, continued, emitted⟩
    rw [atCall] at controlled
    cases controlled with
    | work called =>
      obtain ⟨outcome, reached, plan, produced, prepared, remaining⟩ :=
        (native_call_iff environment policy before.context before.world live scope value expected activation
          operator arguments current childWorld shape executable notError).mp called
      refine ⟨outcome, reached, plan, produced, prepared, ?_⟩
      cases plan with
      | done rows =>
        obtain ⟨rfl, rfl⟩ := remaining
        exact ⟨_, pending, _, .returning _, continued, emitted⟩
      | resume rows => exact ⟨current, pending, childWorld, .work remaining, continued, emitted⟩
  · rintro ⟨outcome, reached, plan, produced, prepared, remaining⟩
    exact RecursiveExecution.Contextual.Stateful.retained_prefix
      (.single (native_step environment policy before live scope value expected activation operator arguments
        outcome reached plan atCall shape executable notError produced prepared)) remaining

theorem retained_caller {Context World : Type} (dispatch : Spec.Eval.GroundedDispatch)
    (before : WorldConfiguration Context World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (operator : Atom) (arguments : List Atom)
    (reached : World) (plan : NativeReplyPlan) :
    let after := resumeNative dispatch before live scope value expected operator arguments reached plan
    after.world = reached ∧ after.context = before.context ∧ after.stack = before.stack ∧ after.emitted = before.emitted := by
  cases plan <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The continuation is an actual path of the existing world machine, not
an assumed evaluator answer. All host outcomes remain under the existential. -/
theorem retained_observed_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (before : WorldConfiguration Context World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (answers : List Result) (finalWorld : World)
    (atCall : before.control = .work (.call live scope value expected activation))
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase) :
    before.SourceRel environment policy answers finalWorld ↔
      ∃ outcome reached plan final,
        environment.services.groundedAt before.context before.world live scope activation value outcome reached ∧
        NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan ∧
        WorldSteps (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
          (resumeNative environment.dispatch before live scope value expected operator arguments reached plan) final ∧
        worldObserve final = some answers ∧ final.world = finalWorld := by
  rw [retained_source_iff environment policy before live scope value expected activation operator arguments
    answers finalWorld atCall shape executable notError]
  constructor
  · rintro ⟨outcome, reached, plan, produced, prepared, remaining⟩
    obtain ⟨final, path, observed, world⟩ := RecursiveExecution.Contextual.Stateful.source_iff_observed _ _ _ |>.mp remaining
    exact ⟨outcome, reached, plan, final, produced, prepared, path, observed, world⟩
  · rintro ⟨outcome, reached, plan, final, produced, prepared, path, observed, world⟩
    exact ⟨outcome, reached, plan, produced, prepared,
      RecursiveExecution.Contextual.Stateful.source_iff_observed _ _ _ |>.mpr ⟨final, path, observed, world⟩⟩

def resumeNested {Context World : Type} (dispatch : Spec.Eval.GroundedDispatch)
    (before : WorldConfiguration Context World) (child : Context) (inner : List Continuation)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (operator : Atom) (arguments : List Atom) (reached : World) (plan : NativeReplyPlan) :
    WorldConfiguration Context World :=
  let leaf := resumeNative dispatch before live scope value expected operator arguments reached plan
  {before with world := reached, control := .context child leaf.control inner}

theorem nested_native_step {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (before : WorldConfiguration Context World) (child : Context) (inner : List Continuation)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (outcome : GroundedResult Entry.Value) (reached : World)
    (plan : NativeReplyPlan)
    (atCall : before.control = .context child (.work (.call live scope value expected activation)) inner)
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase)
    (produced : environment.services.groundedAt child before.world live scope activation value outcome reached)
    (prepared : NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan) :
    WorldStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
      before (resumeNested environment.dispatch before child inner live scope value expected operator arguments reached plan) := by
  cases before with
  | mk world label control stack emitted =>
    dsimp only at atCall produced ⊢
    subst control
    cases plan with
    | done rows => exact .internal (.context (.callGroundedDone shape executable notError produced prepared))
    | resume rows => exact .internal (.context (.callGroundedResume shape executable notError produced prepared))

/-- A suspended child keeps its own context identity and inner caller, while
the enclosing caller keeps the same root identity, stack and publication
prefix. Only the world and the child's native continuation advance. -/
theorem nested_source_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (before : WorldConfiguration Context World) (child : Context) (inner : List Continuation)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (answers : List Result) (finalWorld : World)
    (atCall : before.control = .context child (.work (.call live scope value expected activation)) inner)
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase) :
    before.SourceRel environment policy answers finalWorld ↔
      ∃ outcome reached plan,
        environment.services.groundedAt child before.world live scope activation value outcome reached ∧
        NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) activation outcome plan ∧
        (resumeNested environment.dispatch before child inner live scope value expected operator arguments reached plan).SourceRel
          environment policy answers finalWorld := by
  constructor
  · rintro ⟨current, pending, callerWorld, controlled, continued, emitted⟩
    rw [atCall] at controlled
    cases controlled with
    | context childSource innerContinued =>
      cases childSource with
      | work called =>
        obtain ⟨outcome, reached, plan, produced, prepared, remaining⟩ :=
          (native_call_iff environment policy child before.world live scope value expected activation
            operator arguments _ _ shape executable notError).mp called
        refine ⟨outcome, reached, plan, produced, prepared, ?_⟩
        cases plan with
        | done rows =>
          obtain ⟨rfl, rfl⟩ := remaining
          exact ⟨current, pending, callerWorld, .context (.returning _) innerContinued, continued, emitted⟩
        | resume rows =>
          exact ⟨current, pending, callerWorld, .context (.work remaining) innerContinued, continued, emitted⟩
  · rintro ⟨outcome, reached, plan, produced, prepared, remaining⟩
    exact RecursiveExecution.Contextual.Stateful.retained_prefix
      (.single (nested_native_step environment policy before child inner live scope value expected activation operator arguments
        outcome reached plan atCall shape executable notError produced prepared)) remaining

/-- Returning producer-completed data may check its type but cannot execute
it as new code or change the host world. -/
theorem completed_boundary_world {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller original expected value activation results}
    (source : Stateful.BoundaryRel environment label world live scope caller
      (.native original (some expected) .completed) value activation results finalWorld (policy := policy)) :
    finalWorld = world := by
  cases source
  rfl

private theorem completed_batch_world_at {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller site rows results}
    (source : Stateful.BoundaryBatchRel environment label world live scope caller site rows results finalWorld (policy := policy))
    (completed : ∃ original expected, site = .native original (some expected) .completed) : finalWorld = world :=
  match source with
  | .nil => rfl
  | .cons child tail =>
    have same := by
      obtain ⟨original, expected, rfl⟩ := completed
      exact completed_boundary_world child
    (completed_batch_world_at tail completed).trans same
termination_by structural source

theorem completed_batch_world {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller original expected rows results}
    (source : Stateful.BoundaryBatchRel environment label world live scope caller
      (.native original (some expected) .completed) rows results finalWorld (policy := policy)) :
    finalWorld = world := completed_batch_world_at source ⟨_, _, rfl⟩

/-- At completed provenance, the call's final world is precisely a world
produced by its one host operation, even if return checks reject its values.
No successful answer, pure host operation or ground input is assumed. -/
theorem completed_call_world {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (expected : Atom) (activation : Completed.Frame)
    (operator : Atom) (arguments : List Atom) (results : List Result) (finalWorld : World)
    (shape : value.erase = .expression (operator :: arguments))
    (executable : environment.dispatch.executable operator) (notError : ¬IsErrorRel value.erase)
    (provenance : environment.dispatch.valueProvenance operator arguments = .completed)
    (source : Stateful.CallRel environment label world live scope value expected activation results finalWorld (policy := policy)) :
    ∃ outcome, environment.services.groundedAt label world live scope activation value outcome finalWorld := by
  obtain ⟨outcome, reached, plan, produced, prepared, remaining⟩ :=
    (native_call_iff environment policy label world live scope value expected activation operator arguments
      results finalWorld shape executable notError).mp source
  refine ⟨outcome, ?_⟩
  cases plan with
  | done rows => simpa only [remaining.2] using produced
  | resume rows =>
    have same : finalWorld = reached := completed_batch_world (by simpa only [provenance] using remaining)
    simpa only [same] using produced

end Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatch
