import Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus

/-!
# A source-derived shortcut for completed native returns

An Atom or Undefined demand keeps every producer-completed occurrence exactly.
The batch return queue may therefore be replaced by the existing returning
control, under arbitrary retained context callers. Other provenance or demand
declines to the canonical post-primitive cursor; operands and effects are not
replayed. The equivalence observes complete ordered results and the final world,
not the number of administrative transitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcut

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual NativeDispatchFocus

def PassDemand (expected : Atom) : Prop :=
  expected = Atom.atomType ∨ expected = Atom.undefinedType

instance (expected : Atom) : Decidable (PassDemand expected) := inferInstanceAs
  (Decidable (expected = Atom.atomType ∨ expected = Atom.undefinedType))

theorem pass_keeps (value expected : Atom) (pass : PassDemand expected) :
    CompletedNativeKeepRel value expected := by
  rcases pass with atom | undefined
  · exact Or.inr (Or.inr (Or.inl atom))
  · exact Or.inr (Or.inl undefined)

theorem completed_return_iff {space lookup policy value expected activation results}
    (keep : CompletedNativeKeepRel value.erase expected) :
    NativeCompletedReturnRel space lookup policy value expected activation results ↔ results = [(value, activation)] := by
  constructor
  · intro source
    cases source with
    | keep => rfl
    | cast rejected _ _ => exact False.elim (rejected keep)
  · rintro rfl
    exact .keep keep

theorem boundary_iff {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller original expected value activation results}
    (pass : PassDemand expected) :
    Stateful.BoundaryRel environment label world live scope caller
      (.native original (some expected) .completed) value activation results finalWorld (policy := policy) ↔
      results = [(value, activation)] ∧ finalWorld = world := by
  constructor
  · intro source
    cases source with
    | nativeCompletedReturn returned =>
      exact ⟨(completed_return_iff (pass_keeps value.erase expected pass)).mp returned, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nativeCompletedReturn (.keep (pass_keeps value.erase expected pass))

private theorem batch_exact_at {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller site rows results}
    (source : Stateful.BoundaryBatchRel environment label world live scope caller site rows results finalWorld (policy := policy))
    (accepted : ∃ original expected, site = .native original (some expected) .completed ∧ PassDemand expected) :
    results = rows ∧ finalWorld = world :=
  match source with
  | .nil => ⟨rfl, rfl⟩
  | .cons (world1 := middle) (head := head) (children := children) child tail =>
    have first : children = [head] ∧ middle = world := by
      obtain ⟨original, expected, rfl, pass⟩ := accepted
      exact (boundary_iff pass).mp child
    have rest := batch_exact_at tail accepted
    ⟨by rw [first.1, rest.1]; rfl, rest.2.trans first.2⟩
termination_by structural source

theorem batch_iff {Context World : Type} {environment : WorldEnvironment Context World}
    {policy : Policy} {label : Context} {world finalWorld : World} {live scope caller original expected rows results}
    (pass : PassDemand expected) :
    Stateful.BoundaryBatchRel environment label world live scope caller
      (.native original (some expected) .completed) rows results finalWorld (policy := policy) ↔
      results = rows ∧ finalWorld = world := by
  constructor
  · intro source
    exact batch_exact_at source ⟨_, _, rfl, pass⟩
  · rintro ⟨sameRows, sameWorld⟩
    subst results
    subst finalWorld
    induction rows with
    | nil => exact .nil
    | cons head tail ih =>
      simpa only [List.singleton_append] using
        (Stateful.BoundaryBatchRel.cons (head := head)
          (.nativeCompletedReturn (.keep (pass_keeps head.1.erase expected pass))) ih)

/-- Plugging the queue shortcut into an existing control preserves all inner
caller computations as well as the root caller. -/
theorem control_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (path : CallPath Context) (root : Context) (world : World) (live : List Atom) (scope : List String)
    (caller : Option Atom) (original : Entry.Value) (expected : Atom) (rows results : List Result) (finalWorld : World)
    (pass : PassDemand expected) :
    (path.fill (.work (.boundaryBatch live scope caller (.native original (some expected) .completed) rows))).WorldSourceRel
      environment policy root world results finalWorld ↔
    (path.fill (.returning rows)).WorldSourceRel environment policy root world results finalWorld := by
  induction path generalizing root world results finalWorld with
  | here =>
    constructor
    · intro source
      cases source with
      | work batch =>
        obtain ⟨rfl, rfl⟩ := (batch_iff pass).mp batch
        exact .returning _
    · intro source
      cases source
      exact .work ((batch_iff pass).mpr ⟨rfl, rfl⟩)
  | under child inner rest ih =>
    constructor
    · intro source
      cases source with
      | context childSource continued => exact .context ((ih _ _ _ _).mp childSource) continued
    · intro source
      cases source with
      | context childSource continued => exact .context ((ih _ _ _ _).mpr childSource) continued

theorem retained_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (caller : Option Atom) (original : Entry.Value)
    (expected : Atom) (rows answers : List Result) (finalWorld : World) (pass : PassDemand expected) :
    ({before with control := path.fill (.work (.boundaryBatch live scope caller
      (.native original (some expected) .completed) rows))} : WorldConfiguration Context World).SourceRel
      environment policy answers finalWorld ↔
    ({before with control := path.fill (.returning rows)} : WorldConfiguration Context World).SourceRel
      environment policy answers finalWorld := by
  constructor
  · rintro ⟨current, pending, childWorld, source, continued, emitted⟩
    exact ⟨current, pending, childWorld,
      (control_iff environment policy path before.context before.world live scope caller original expected
        rows current childWorld pass).mp source, continued, emitted⟩
  · rintro ⟨current, pending, childWorld, source, continued, emitted⟩
    exact ⟨current, pending, childWorld,
      (control_iff environment policy path before.context before.world live scope caller original expected
        rows current childWorld pass).mpr source, continued, emitted⟩

def eligible (dispatch : Spec.Eval.GroundedDispatch) (operator : Atom) (arguments : List Atom) (expected : Atom) : Bool :=
  match dispatch.valueProvenance operator arguments with
  | .emitted => false
  | .completed => decide (PassDemand expected)

/-- This executable choice changes the control only after a primitive reply.
Decline keeps that exact post-primitive cursor, not the original source call. -/
def resumeChecked {Context World : Type} (dispatch : Spec.Eval.GroundedDispatch)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (operator : Atom) (arguments : List Atom) (reached : World) (plan : NativeReplyPlan) :
    WorldConfiguration Context World :=
  match plan with
  | .done _ => resumeAt dispatch path before live scope value expected operator arguments reached plan
  | .resume rows =>
    if eligible dispatch operator arguments expected then
      {before with world := reached, control := path.fill (.returning rows)}
    else resumeAt dispatch path before live scope value expected operator arguments reached plan

theorem resume_source_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
    (path : CallPath Context) (before : WorldConfiguration Context World)
    (live : List Atom) (scope : List String) (value : Entry.Value) (expected : Atom)
    (operator : Atom) (arguments : List Atom) (reached : World) (plan : NativeReplyPlan)
    (answers : List Result) (finalWorld : World) :
    (resumeAt environment.dispatch path before live scope value expected operator arguments reached plan).SourceRel
      environment policy answers finalWorld ↔
    (resumeChecked environment.dispatch path before live scope value expected operator arguments reached plan).SourceRel
      environment policy answers finalWorld := by
  cases plan with
  | done rows => rfl
  | resume rows =>
    cases provenance : environment.dispatch.valueProvenance operator arguments with
    | emitted => simp [resumeChecked, eligible, provenance]
    | completed =>
      by_cases pass : PassDemand expected
      · simpa only [resumeAt, RetainedNativeDispatch.resumeNative, provenance, resumeChecked, eligible,
          decide_eq_true pass, Bool.true_eq, ite_true] using
          retained_iff environment policy path {before with world := reached} live scope none value expected rows answers finalWorld pass
      · simp [resumeChecked, eligible, provenance, pass]

/-- Source preservation and reflection over all local primitive observations.
The checked path does not assume the answer of the surrounding computation. -/
theorem call_source_iff {Context World : Type} (environment : WorldEnvironment Context World) (policy : Policy)
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
        (resumeChecked environment.dispatch path before live scope value expected operator arguments reached plan).SourceRel
          environment policy answers finalWorld := by
  rw [focused_source_iff environment policy path before live scope value expected activation operator arguments
    answers finalWorld atCall shape executable notError]
  exact exists_congr fun _ => exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => and_congr_right fun _ =>
      resume_source_iff environment policy path before live scope value expected operator arguments _ _ answers finalWorld

end Mettapedia.Languages.MeTTa.HE.CompletedNativeShortcut
