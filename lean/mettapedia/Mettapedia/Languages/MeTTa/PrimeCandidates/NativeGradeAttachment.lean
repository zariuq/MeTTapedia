import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeDerivationGrades
import Mettapedia.GSLT.Core.AdvisoryAttachment
import Mettapedia.Machines.RevisionDependencySet

/-!
# Attaching native grades at every equation admission

The evaluator retains the new candidate world before forcing the RHS and
attaches a pure scoring job at that edge. This also grades nested and
recursive calls, without pre-enumerating their eventual answers. The source
transition relation and the existing controller remain the authorities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeAttachment

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl (Controller WorkOccurrence)
open NativeEquationNeed NativeCandidateGrades NativeDerivationGrades

/-- The variable bindings of the actually captured authored row, including
names not bound there. Registry bindings and pointed-to resources have their
own read views; this view names the captured local cells. -/
def capturedCellView (capture : Captured) :
    Mettapedia.Machines.CapturedReadView String (Option CellId) :=
  Mettapedia.Machines.CapturedReadView.admit
    ⟨NativeEquationNeed.lookup capture.row.environment⟩

/-- Native score evaluation dispatches a variable using the captured local
cell view. A newer environment is not a source of replacement bindings. -/
theorem score_variable_uses_captured_cell (program : Program) (capture : Captured)
    (live : Mettapedia.Machines.RevisionEnvironment String (Option CellId))
    (name : String) :
    NativeEquationNeed.start program (.var name) capture.row.environment =
      match ((capturedCellView capture).read live name).1 with
      | some cell => .forward cell
      | none => NativeEquationNeed.failure "unbound variable" := rfl

def captureNext (before after : NativeMachine) : Option Captured :=
  match newRow before after, after.control with
  | some row, .run _ stack => some ⟨row, after.world, stack, after.work⟩
  | _, _ => none

theorem new_row_control (before after : NativeMachine) (row : Row)
    (chosen : newRow before after = some row) :
    ∃ stack, after.control = .run (.evaluate row.body row.environment) stack := by
  unfold newRow at chosen
  split at chosen
  · split at chosen
    · split at chosen
      · cases chosen
        exact ⟨_, by assumption⟩
      · contradiction
    · contradiction
  · contradiction

theorem captured_next_exact (before after : NativeMachine) (capture : Captured)
    (captured : captureNext before after = some capture) :
    capture.body = after ∧ newRow before after = some capture.row := by
  cases chosen : newRow before after with
  | none => simp [captureNext, chosen] at captured
  | some row =>
      obtain ⟨returns, localState⟩ := new_row_control before after row chosen
      simp only [captureNext, chosen, localState, Option.some.injEq] at captured
      subst capture
      constructor
      · cases after
        simp_all [Captured.body]
      · rfl

def attach (grade : Row → Atom) (before after : NativeOccurrence) : List Score :=
  (captureNext before.state after.state).toList.map
    (fun capture => capture.score (grade capture.row))

/-- Every attached score starts from the complete candidate world and its
actual bound cells, before any instruction of that RHS. -/
theorem attached_origin (grade : Row → Atom) (before after : NativeOccurrence)
    (score : Score) (member : score ∈ attach grade before after) :
    score.origin.body = after.state ∧
    score.machine.world = after.state.world ∧
    score.machine.control = .run (.evaluate (grade score.origin.row)
      score.origin.row.environment) [] ∧ scoreResult score = none := by
  obtain ⟨capture, captured, rfl⟩ := List.mem_map.mp member
  have value : captureNext before.state after.state = some capture :=
    Option.mem_toList.mp captured
  obtain ⟨body, _⟩ := captured_next_exact before.state after.state capture value
  refine ⟨body, ?_, rfl, rfl⟩
  simpa only [Captured.score, Captured.body] using
    congrArg (fun machine : NativeMachine => machine.world) body

/-- Each physical admitted row receives its own score. A second identical
equation is not merged into the first equation's job. -/
theorem attach_application_capture (program : Program) (head : String)
    (arguments : List CellId) (machine : NativeMachine) (cell : CellId)
    (stack : List (Frame Resume)) (capture : Captured)
    (member : capture ∈ captureApplication program head arguments machine cell stack)
    (grade : Row → Atom) (beforeTrace afterTrace : List Nat) :
    attach grade ⟨machine, beforeTrace⟩ ⟨capture.body, afterTrace⟩ =
      [capture.score (grade capture.row)] := by
  have chosen := application_capture_choice program head arguments machine cell stack capture member
  have captured : captureNext machine capture.body = some capture := by
    unfold captureNext
    rw [chosen]
    rfl
  change (captureNext machine capture.body).toList.map _ = _
  rw [captured]
  rfl

def nativeSystem (program : Program) (grade : Row → Atom) :
    BranchingSystem NativeCandidateGrades.Task NativeCandidateGrades.Answer :=
  AdvisoryAttachment.system (occurrenceSystem program) (scoreStep program) (attach grade)

def roots (term : Atom) : List NativeCandidateGrades.Task :=
  AdvisoryWork.admit [WorkOccurrence.root (initial term)] []

def execute {Memory : Type} (program : Program) (grade : Row → Atom)
    (controller : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory)
    (goal : List NativeCandidateGrades.Answer → Bool) (allowance : Nat)
    (state : InferenceControl.Snapshot NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory) :=
  DemandExecution.run (nativeSystem program grade) controller goal allowance state

theorem successor_bodies_exact (program : Program) (grade : Row → Atom) (node : NativeOccurrence) :
    AdvisoryWork.bodies ((nativeSystem program grade).successors (.body node)) =
      (occurrenceSystem program).successors node :=
  AdvisoryAttachment.successor_projection _ _ _ _

theorem source_paths_iff (program : Program) (grade : Row → Atom) (term : Atom)
    (node : NativeOccurrence) :
    Generated (nativeSystem program grade) (roots term) (.body node) ↔
      Generated (occurrenceSystem program) [WorkOccurrence.root (initial term)] node := by
  simpa only [nativeSystem, roots, AdvisoryWork.bodies_admit] using
    AdvisoryAttachment.generated_body_iff (occurrenceSystem program) (scoreStep program)
      (attach grade) (roots term) node

/-- Every finite source answer path remains live under a fair controller,
even if some or all advisory expressions fail to terminate. -/
theorem fair_source_answer {Memory : Type} (program : Program) (grade : Row → Atom)
    (controller : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory)
    (term : Atom)
    (fair : InferenceControl.Snapshot.FairFrom (nativeSystem program grade) controller (roots term))
    (node : NativeOccurrence) (answer : NativeCandidateGrades.Answer)
    (generated : Generated (occurrenceSystem program) [WorkOccurrence.root (initial term)] node)
    (emits : (occurrenceSystem program).emit node = some answer) :
    ∃ allowance, (⟨.body node, answer⟩ : Emission NativeCandidateGrades.Task NativeCandidateGrades.Answer) ∈
      (InferenceControl.Snapshot.run (nativeSystem program grade) controller allowance
        (InferenceControl.Snapshot.initial controller (roots term))).search.events :=
  InferenceControl.Snapshot.fair_emits_reachable (nativeSystem program grade) controller
    (roots term) fair ((source_paths_iff program grade term node).mpr generated) emits

/-- Emissions from the attached-advice evaluator carry a genuine native path,
including the branch world, shared cells, returns and physical occurrence trace. -/
theorem emitted_native_path {Memory : Type} (program : Program) (grade : Row → Atom)
    (controller : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory)
    (term : Atom) (allowance : Nat)
    (event : Emission NativeCandidateGrades.Task NativeCandidateGrades.Answer)
    (member : event ∈ (InferenceControl.Snapshot.run (nativeSystem program grade) controller
      allowance (InferenceControl.Snapshot.initial controller (roots term))).search.events) :
    ∃ node, event.origin = .body node ∧
      Steps (specification program) node.trace.length (initial term) node.state ∧
      haltedOutcome node.state = some event.value.1 ∧ event.value.2 = node.trace := by
  have sound := InferenceControl.Snapshot.sound_run (nativeSystem program grade) controller
    (roots := roots term)
    (snapshot := InferenceControl.Snapshot.initial controller (roots term))
    (initial_sound (nativeSystem program grade) (roots term)) allowance
  obtain ⟨generated, emits⟩ := sound.2 event member
  cases origin : event.origin with
  | scoring score => simp [nativeSystem, AdvisoryAttachment.system, origin] at emits
  | body node =>
      rw [origin] at generated emits
      have source := (source_paths_iff program grade term node).mp generated
      have path := NeedInferenceControl.Reference.generated_has_steps (specification program) source
      change (haltedOutcome node.state).map (fun answer => (answer, node.trace)) =
        some event.value at emits
      cases observed : haltedOutcome node.state with
      | none => simp [observed] at emits
      | some answer =>
          have same : event.value = (answer, node.trace) := by
            simpa only [observed, Option.map_some, Option.some.injEq] using emits.symm
          exact ⟨node, rfl, path, by simp [same, observed], by simp [same]⟩

theorem source_closure_complete {Memory : Type} (program : Program) (grade : Row → Atom)
    (controller : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory)
    (term : Atom) (allowance : Nat)
    (closed : (AdvisoryWork.observe (InferenceControl.Snapshot.run (nativeSystem program grade)
      controller allowance (InferenceControl.Snapshot.initial controller (roots term))).search).frontier = [])
    (node : NativeOccurrence) (answer : NativeCandidateGrades.Answer)
    (generated : Generated (occurrenceSystem program) [WorkOccurrence.root (initial term)] node)
    (emits : (occurrenceSystem program).emit node = some answer) :
    (⟨node, answer⟩ : Emission NativeOccurrence NativeCandidateGrades.Answer) ∈
      (AdvisoryWork.observe (InferenceControl.Snapshot.run (nativeSystem program grade) controller
        allowance (InferenceControl.Snapshot.initial controller (roots term))).search).events :=
  AdvisoryAttachment.semantic_closure_complete (occurrenceSystem program) (scoreStep program)
    (attach grade) controller [WorkOccurrence.root (initial term)] [] allowance closed
    node answer generated emits

theorem resume_exact {Memory : Type} (program : Program) (grade : Row → Atom)
    (controller : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory)
    (goal : List NativeCandidateGrades.Answer → Bool) (first second : Nat)
    (state : InferenceControl.Snapshot NativeCandidateGrades.Task NativeCandidateGrades.Answer Memory) :
    execute program grade controller goal (first + second) state =
      execute program grade controller goal second (execute program grade controller goal first state) :=
  DemandExecution.run_add _ _ _ _ _ _

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeAttachment
