import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationWork
import Mettapedia.GSLT.Core.AdvisoryWork
import Mettapedia.Machines.BranchLocalNeed.Representation

/-!
# Native candidate capture and resumable advisory grades

Admission captures a physical authored row, its cell environment, and the
branch world before its right-hand side takes an instruction. Both the body
and its pure score are then live work. A score runs the same Need instruction
semantics in a detached copy of that world; its returns cannot commit into
the body continuation. This module concerns scheduling advice, not semantic
derivation weights or the number of answers demanded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateGrades

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl (Controller WorkOccurrence)
open NativeEquationNeed

abbrev NativeWorld := World Origin Rule Atom Empty String Empty

/-- Row identity and binding information retained by application admission. -/
structure Row where
  index : Nat
  body : Atom
  environment : Environment
  deriving Repr, DecidableEq

def Row.alternative (row : Row) : Rule × Local :=
  (.equation row.index, .evaluate row.body row.environment)

/-- The same finite structural admission as the native equation instance,
retaining its row data rather than starting the body. -/
def rows (program : Program) (head : String) (arguments : List CellId) : List Row :=
  program.zipIdx.filterMap fun (equation, index) =>
    if equation.head = head ∧ equation.parameters.Nodup ∧
        equation.parameters.length = arguments.length then
      some ⟨index, equation.body, equation.parameters.zip arguments⟩
    else none

theorem rows_alternatives (program : Program) (head : String) (arguments : List CellId) :
    (rows program head arguments).map Row.alternative = rowCandidates program head arguments := by
  simp only [rows, rowCandidates, List.map_filterMap]
  congr 1
  funext entry
  rcases entry with ⟨equation, index⟩
  split <;> rfl

theorem row_alternative_injective : Function.Injective Row.alternative := by
  intro left right equal
  cases left
  cases right
  simpa [Row.alternative] using equal

theorem row_admission_iff (program : Program) (head : String) (arguments : List CellId)
    (row : Row) :
    row ∈ rows program head arguments ↔
      Activates program head arguments (.equation row.index)
        (.evaluate row.body row.environment) := by
  rw [← rowCandidates_iff, ← rows_alternatives]
  exact (List.mem_map_of_injective row_alternative_injective).symm

/-- The heap is persistent. Capturing it is not evaluation or a serialization
of an unevaluated argument. The return stack belongs only to the body. -/
structure Captured where
  row : Row
  world : NativeWorld
  returns : List (Frame Resume)
  work : Work

def Captured.body (capture : Captured) : NativeMachine :=
  ⟨capture.world, .run (.evaluate capture.row.body capture.row.environment) capture.returns,
    capture.work⟩

def captureOne (machine : NativeMachine) (base : NativeWorld) (cell : CellId)
    (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (ordinal : Nat) (row : Row) : Captured :=
  let world := (base.fork ordinal).setKnownCache cell record (.evaluating owner)
  let world := recorded world (.evaluate cell owner)
  let world := recorded world (.chooseRule cell (.equation row.index))
  ⟨row, world, .commit cell owner :: stack, machine.work.bump 1 1 2 0⟩

def captureRows (machine : NativeMachine) (base : NativeWorld) (cell : CellId)
    (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) : Nat → List Row → List Captured
  | _, [] => []
  | ordinal, row :: rest =>
      captureOne machine base cell record owner stack ordinal row ::
        captureRows machine base cell record owner stack (ordinal + 1) rest

@[simp] theorem captured_rows (machine : NativeMachine) (base : NativeWorld) (cell : CellId)
    (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (ordinal : Nat) (admitted : List Row) :
    (captureRows machine base cell record owner stack ordinal admitted).map Captured.row =
      admitted := by
  induction admitted generalizing ordinal with
  | nil => rfl
  | cons row rest ih => simp [captureRows, captureOne, ih]

/-- The captured bodies are exactly the existing native branching operation,
with the same order, multiplicity, worlds, return obligations and work count. -/
theorem captured_bodies (machine : NativeMachine) (base : NativeWorld) (cell : CellId)
    (record : CellRecord Origin Atom Empty) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (ordinal : Nat) (admitted : List Row) :
    (captureRows machine base cell record owner stack ordinal admitted).map Captured.body =
      branchAlternatives machine base cell record owner stack ordinal
        (admitted.map Row.alternative) := by
  induction admitted generalizing ordinal with
  | nil => rfl
  | cons row rest ih =>
      simp [captureRows, captureOne, Captured.body, Row.alternative, branchAlternatives,
        finished, ih]

def captureApplication (program : Program) (head : String) (arguments : List CellId)
    (machine : NativeMachine) (cell : CellId) (stack : List (Frame Resume)) : List Captured :=
  captureRows machine { machine.world with nextEvaluator := machine.world.nextEvaluator + 1 }
    cell ⟨.application head arguments, .suspended⟩ machine.world.nextEvaluator stack 0
    (rows program head arguments)

/-- Admission is characterized by independent source activation, including
the captured environment; it makes no premise about finishing the body. -/
theorem captured_admission_iff (program : Program) (head : String) (arguments : List CellId)
    (machine : NativeMachine) (cell : CellId) (stack : List (Frame Resume)) (row : Row) :
    (∃ capture ∈ captureApplication program head arguments machine cell stack,
      capture.row = row) ↔
      Activates program head arguments (.equation row.index)
        (.evaluate row.body row.environment) := by
  rw [← row_admission_iff]
  have mapped := captured_rows machine
    { machine.world with nextEvaluator := machine.world.nextEvaluator + 1 }
    cell ⟨.application head arguments, .suspended⟩ machine.world.nextEvaluator stack 0
    (rows program head arguments)
  rw [← mapped]
  exact List.mem_map.symm

/-- A suspended application with an admitted row takes exactly these captured
bodies as its next native states. Empty admission instead takes the native
retryable no-rule branch, outside the successful-candidate list. -/
theorem captures_are_native_step (program : Program) (head : String) (arguments : List CellId)
    (machine : NativeMachine) (cell : CellId) (stack : List (Frame Resume))
    (forcing : machine.control = .force cell stack)
    (present : machine.world.heap.lookup cell =
      some ⟨.application head arguments, .suspended⟩)
    (nonempty : rowCandidates program head arguments ≠ []) :
    (captureApplication program head arguments machine cell stack).map Captured.body =
      NeedReference.step (specification program) machine := by
  rw [captureApplication, captured_bodies, rows_alternatives]
  simp only [NeedReference.step, forcing, present, specification, alternatives]

/-- A score is a native computation with its own evolving heap and receipts.
The origin, physical row and initial candidate bindings remain retained. -/
structure Score where
  origin : Captured
  expression : Atom
  machine : NativeMachine

def Captured.score (capture : Captured) (expression : Atom) : Score :=
  ⟨capture, expression,
    ⟨capture.world, .run (.evaluate expression capture.row.environment) [], {}⟩⟩

def scoreStep (program : Program) (score : Score) : List Score :=
  (NeedReference.step (specification program) score.machine).map
    (fun next => { score with machine := next })

def scoreResult (score : Score) : Option Outcome := haltedOutcome score.machine

/-- A completed integer score may propose any integer key, including zero.
The proposal does not change admission or supply a semantic cost bound. -/
def priorityProposal (score : Score) : Option Int :=
  match scoreResult score with
  | some (.value (.grounded (.int key))) => some key
  | _ => none

theorem score_captures_before_body (capture : Captured) (expression : Atom) :
    (capture.score expression).origin = capture ∧
    (capture.score expression).machine.world = capture.body.world ∧
    (capture.score expression).machine.control =
      .run (.evaluate expression capture.row.environment) [] ∧
    scoreResult (capture.score expression) = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every scoring quantum is an actual Need step. Captured bindings and the
origin world do not change when scoring forces its own copy of a cell. -/
theorem score_step_iff (program : Program) (score next : Score) :
    next ∈ scoreStep program score ↔
      ∃ machine ∈ NeedReference.step (specification program) score.machine,
        next = { score with machine := machine } := by
  simp only [scoreStep, List.mem_map]
  constructor
  · rintro ⟨machine, member, rfl⟩; exact ⟨machine, member, rfl⟩
  · rintro ⟨machine, member, rfl⟩; exact ⟨machine, member, rfl⟩

theorem score_step_origin (program : Program) (score next : Score)
    (member : next ∈ scoreStep program score) :
    next.origin = score.origin ∧ next.expression = score.expression ∧
      next.machine.work.transitions = score.machine.work.transitions + 1 := by
  obtain ⟨machine, step, rfl⟩ := (score_step_iff program score next).mp member
  exact ⟨rfl, rfl, step_increments_transition (specification program) _ _ step⟩

def scoringSystem (program : Program) : BranchingSystem Score Outcome :=
  ⟨scoreResult, scoreStep program⟩

/-- The scoring service has an independently replayable native path, rather
than a caller-asserted value. It retains the exact candidate origin. -/
theorem score_generated_native (program : Program) (initial next : Score)
    (generated : Generated (scoringSystem program) [initial] next) :
    next.origin = initial.origin ∧ next.expression = initial.expression ∧
      ∃ count, Steps (specification program) count initial.machine next.machine := by
  induction generated with
  | @root node member =>
      have same : node = initial := List.mem_singleton.mp member
      subst node
      exact ⟨rfl, rfl, 0, .refl _⟩
  | @successor parent child _ member ih =>
      obtain ⟨machine, edge, rfl⟩ := (score_step_iff program parent child).mp member
      obtain ⟨origin, expression, count, path⟩ := ih
      obtain ⟨index, bound, located⟩ := List.mem_iff_getElem.mp edge
      have last : Steps (specification program) 1 parent.machine machine :=
        .cons ⟨index, List.getElem?_eq_some_iff.mpr ⟨bound, located⟩⟩ (.refl _)
      exact ⟨origin, expression, count + 1, path.trans _ last⟩

abbrev NativeOccurrence := WorkOccurrence NativeMachine
abbrev Task := AdvisoryWork.Task NativeOccurrence Score
abbrev Answer := Outcome × List Nat

def system (program : Program) : BranchingSystem Task Answer :=
  AdvisoryWork.system (occurrenceSystem program) (scoreStep program)

def admit (captures : List Captured) (grade : Row → Atom) : List Task :=
  AdvisoryWork.admit (captures.map (fun capture => WorkOccurrence.root capture.body))
    (captures.map fun capture => capture.score (grade capture.row))

/-- Demand and allowance act on the retained body-and-score state; neither
is encoded by a special semantic weight. -/
def execute {Memory : Type} (program : Program) (controller : Controller Task Answer Memory)
    (goal : List Answer → Bool) (allowance : Nat)
    (state : InferenceControl.Snapshot Task Answer Memory) :=
  DemandExecution.run (system program) controller goal allowance state

theorem resume_exact {Memory : Type} (program : Program)
    (controller : Controller Task Answer Memory) (goal : List Answer → Bool)
    (first second : Nat) (state : InferenceControl.Snapshot Task Answer Memory) :
    execute program controller goal (first + second) state =
      execute program controller goal second (execute program controller goal first state) :=
  DemandExecution.run_add _ _ _ _ _ _

theorem admission_retains_bodies (captures : List Captured) (grade : Row → Atom) :
    AdvisoryWork.bodies (admit captures grade) =
      captures.map (fun capture => WorkOccurrence.root capture.body) :=
  AdvisoryWork.bodies_admit _ _

theorem grade_cannot_prune (captures : List Captured) (grade : Row → Atom)
    (capture : Captured) (member : capture ∈ captures) :
    AdvisoryWork.Task.body (WorkOccurrence.root capture.body) ∈ admit captures grade :=
  AdvisoryWork.body_admitted _ _ (List.mem_map.mpr ⟨capture, member, rfl⟩)

/-- This equivalence concerns independently generated source executions. It
holds for terminating, divergent and zero-valued scoring expressions alike. -/
theorem authorized_body_paths_iff (program : Program) (captures : List Captured)
    (grade : Row → Atom) (node : NativeOccurrence) :
    Generated (system program) (admit captures grade) (.body node) ↔
      Generated (occurrenceSystem program)
        (captures.map (fun capture => WorkOccurrence.root capture.body)) node := by
  simpa only [system, admission_retains_bodies] using
    AdvisoryWork.generated_body_iff (occurrenceSystem program) (scoreStep program)
      (admit captures grade) node

@[simp] theorem scoring_emits_no_answer (program : Program) (score : Score) :
    (system program).emit (.scoring score) = none := rfl

theorem authorized_emission_iff (program : Program) (captures : List Captured)
    (grade : Row → Atom) (node : NativeOccurrence) (answer : Answer) :
    (Generated (system program) (admit captures grade) (.body node) ∧
      (system program).emit (.body node) = some answer) ↔
    (Generated (occurrenceSystem program)
      (captures.map (fun capture => WorkOccurrence.root capture.body)) node ∧
      (occurrenceSystem program).emit node = some answer) := by
  rw [authorized_body_paths_iff]
  rfl

theorem body_closure_complete {Memory : Type} (program : Program)
    (captures : List Captured) (grade : Row → Atom)
    (controller : Controller Task Answer Memory) (fuel : Nat)
    (closed : (AdvisoryWork.observe (InferenceControl.Snapshot.run (system program) controller
      fuel (InferenceControl.Snapshot.initial controller (admit captures grade))).search).frontier = [])
    (node : NativeOccurrence) (answer : Answer)
    (generated : Generated (occurrenceSystem program)
      (captures.map (fun capture => WorkOccurrence.root capture.body)) node)
    (emits : (occurrenceSystem program).emit node = some answer) :
    (⟨node, answer⟩ : Emission NativeOccurrence Answer) ∈
      (AdvisoryWork.observe (InferenceControl.Snapshot.run (system program) controller fuel
        (InferenceControl.Snapshot.initial controller (admit captures grade))).search).events :=
  AdvisoryWork.semantic_closure_complete (occurrenceSystem program) (scoreStep program)
    controller _ _ fuel closed node answer generated emits


/-! ## Finite capture views

All maps in a live capture are justified by their retained update histories.
The finite views include the original row and the complete suspended control;
the scoring view also includes its evolving machine.
-/

namespace Captured

abbrev RecordedView := Row ×
  World.RecordedView Origin Rule Atom Empty String Empty × List (Frame Resume) × Work

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Row ×
    World.RecordedView Origin Rule Atom Empty String Empty × List (Frame Resume) × Work))

def Recorded (capture : Captured) : Prop := capture.world.heap.Recorded

def recordedView (capture : Captured) : RecordedView :=
  (capture.row, capture.world.recordedView, capture.returns, capture.work)

def ofRecordedView (view : RecordedView) : Captured :=
  ⟨view.1, World.ofRecordedView view.2.1, view.2.2.1, view.2.2.2⟩

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded :=
  World.ofRecordedView_recorded _

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := rfl

theorem ofRecordedView_recordedView (capture : Captured) (valid : capture.Recorded) :
    ofRecordedView capture.recordedView = capture := by
  cases capture with
  | mk row world returns work =>
      simp only [ofRecordedView, recordedView]
      rw [World.ofRecordedView_recordedView world valid]

theorem recordedView_injective (left right : Captured)
    (leftValid : left.Recorded) (rightValid : right.Recorded)
    (same : left.recordedView = right.recordedView) : left = right := by
  rw [← ofRecordedView_recordedView left leftValid,
    ← ofRecordedView_recordedView right rightValid, same]

instance : DecidableEq {capture : Captured // capture.Recorded} := fun left right =>
  if same : left.val.recordedView = right.val.recordedView then
    isTrue (Subtype.ext (recordedView_injective _ _ left.property right.property same))
  else isFalse (fun equal => same (congrArg (fun capture => capture.val.recordedView) equal))

end Captured

namespace Score

abbrev RecordedView := Captured.RecordedView × Atom ×
  Machine.RecordedView Origin Local Resume Rule Atom Empty String Empty

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Captured.RecordedView × Atom ×
    Machine.RecordedView Origin Local Resume Rule Atom Empty String Empty))

def Recorded (score : Score) : Prop :=
  score.origin.Recorded ∧ score.machine.world.heap.Recorded

def recordedView (score : Score) : RecordedView :=
  (score.origin.recordedView, score.expression, score.machine.recordedView)

def ofRecordedView (view : RecordedView) : Score :=
  ⟨Captured.ofRecordedView view.1, view.2.1, Machine.ofRecordedView view.2.2⟩

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded :=
  ⟨Captured.ofRecordedView_recorded _, Machine.ofRecordedView_recorded _⟩

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := rfl

theorem ofRecordedView_recordedView (score : Score) (valid : score.Recorded) :
    ofRecordedView score.recordedView = score := by
  cases score with
  | mk origin expression machine =>
      simp only [ofRecordedView, recordedView]
      rw [Captured.ofRecordedView_recordedView origin valid.1,
        Machine.ofRecordedView_recordedView machine valid.2]

theorem recordedView_injective (left right : Score)
    (leftValid : left.Recorded) (rightValid : right.Recorded)
    (same : left.recordedView = right.recordedView) : left = right := by
  rw [← ofRecordedView_recordedView left leftValid,
    ← ofRecordedView_recordedView right rightValid, same]

instance : DecidableEq {score : Score // score.Recorded} := fun left right =>
  if same : left.val.recordedView = right.val.recordedView then
    isTrue (Subtype.ext (recordedView_injective _ _ left.property right.property same))
  else isFalse (fun equal => same (congrArg (fun score => score.val.recordedView) equal))

end Score

theorem Captured.score_recorded (capture : Captured) (expression : Atom)
    (valid : capture.Recorded) : (capture.score expression).Recorded := ⟨valid, valid⟩

theorem score_step_recorded (program : Program) (before after : Score)
    (valid : before.Recorded) (step : after ∈ scoreStep program before) : after.Recorded := by
  obtain ⟨machine, member, rfl⟩ := (score_step_iff program before after).mp step
  exact ⟨valid.1, NeedReference.step_heap_recorded (specification program) _ _ valid.2 member⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCandidateGrades
