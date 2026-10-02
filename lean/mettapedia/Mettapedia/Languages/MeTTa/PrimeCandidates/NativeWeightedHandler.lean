import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeDerivationGrades
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeAttachment
import Mettapedia.GSLT.Dynamics.ResumptionCategory

/-!
# Native equation weights as a resumption handler

The Prime adapter selects the existing Need specification and binding-local
graded-where interpretation. Free operations, weighted sequencing, retained
worlds and resumption are supplied by their general mathematical modules.

Equation coefficients are charged on actual physical choice receipts, before
executing the right-hand side. The settled and pending adapters share one
handler. A pending coefficient executes with the captured bindings; its body
resumes with the completed coefficient's world, preserving shared lazy choices.
An uninterpreted coefficient result retains that body and the actual score.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.GSLT.Dynamics
open NativeEquationNeed NativeCandidateGrades NativeDerivationGrades

abbrev WorkState := WorkOccurrence NativeMachine

def source {V : Type} [Semiring V] (program : Program) (clause : WeighClause V Row) :
    WeightedBranchingResumption.Coalgebra WorkState WorkState V :=
  NeedWeightedResumption.source (specification program) (edgeGrade clause)

theorem immediate_successors_erase {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (before : WorkState) :
    (NeedWeightedResumption.successors (specification program) (edgeGrade clause) before).map
      Prod.fst = (occurrenceSystem program).successors before :=
  NeedWeightedResumption.successors_erasure _ _ _

/-- Authored physical row admission supplies the coefficient environment. -/
theorem coefficient_of_actual_capture {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (head : String)
    (arguments : List CellId) (machine : NativeMachine) (cell : CellId)
    (stack : List (Frame Resume)) (capture : Captured)
    (member : capture ∈ captureApplication program head arguments machine cell stack) :
    edgeGrade clause machine capture.body = WeighClause.eval capture.row clause := by
  rw [edgeGrade, application_capture_choice program head arguments machine cell stack capture member]

/-- The actual native weighted frontier is the interpretation of its free unfolding. -/
theorem native_handler_agrees {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (source program clause) fuel before) =
      WeightedBranchingResumption.contributions (source program clause) fuel before :=
  NeedWeightedResumption.handler_agrees _ _ _ _

/-- Native execution is interpreted by the actual Mathlib writer/list handler. -/
theorem native_kleisli_handler_agrees {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    (ResumptionCategory.handle WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (source program clause) fuel before)).run =
      WeightedBranchingResumption.contributions (source program clause) fuel before :=
  native_handler_agrees program clause fuel before

/-- Both the ordered coefficient and the complete residual world survive a split run. -/
theorem native_resume_exact {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (first second : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions (source program clause) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions (source program clause) first before)
        (fun leaf => match leaf with
          | .inl done => [(.inl done, (1 : V))]
          | .inr pending =>
              WeightedBranchingResumption.contributions (source program clause) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions (source program clause) first before))
    funext leaf
    cases leaf <;> rfl

/-- Declared coefficient erasure recovers the separately implemented native
frontier. It preserves physical zero contributions; it is not a support filter. -/
theorem native_frontier_erasure {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    (WeightedBranchingResumption.contributions (source program clause) fuel before).map
      (fun leaf => (NeedWeightedResumption.retained leaf.1).state) =
      runFrontier (specification program) fuel [before.state] :=
  NeedWeightedResumption.batch_frontier_erasure _ _ _ _

/-- Observing halted values after erasure agrees with ordinary native answers. -/
theorem native_answers_erasure {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat) (before : WorkState) :
    ((WeightedBranchingResumption.contributions (source program clause) fuel before).map
      (fun leaf => (NeedWeightedResumption.retained leaf.1).state)).filterMap haltedOutcome =
      answers (specification program) fuel before.state := by
  rw [native_frontier_erasure]
  rfl

theorem native_returned_is_halted {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (fuel : Nat)
    (before after : WorkState) (value : V)
    (member : (.inl after, value) ∈
      WeightedBranchingResumption.contributions (source program clause) fuel before) :
    isHalted after.state = true :=
  NeedWeightedResumption.returned_is_halted _ _ _ _ _ _ member

/-- The handler's retained evidence carries the original machine's exact cost. -/
theorem native_retained_transition_cost {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    (NeedWeightedResumption.retained leaf.1).state.work.transitions =
      initial.work.transitions + (NeedWeightedResumption.retained leaf.1).trace.length :=
  NeedWeightedResumption.retained_transition_cost _ _ _ _ member

/-! ## Prepared native operations with parent-controlled publication -/

/-- The native machine's executable path interpreter, used only to validate
captured occurrence inputs. It uses the actual Need step and outcome functions. -/
def capturePathMachine (program : Program) (initialMachine : NativeMachine) :
    Mettapedia.Machines.OccurrenceMachineCore Unit NativeMachine Outcome where
  load _ := initialMachine
  next := NeedReference.step (specification program)
  answer := haltedOutcome
  answer_final machine answer returned := by
    cases control : machine.control <;>
      simp [haltedOutcome, control, NeedReference.step] at returned ⊢

def captureDomain (program : Program) (initialMachine : NativeMachine)
    (node : WorkState) : Prop :=
  WorkOccurrence.ValidFrom (capturePathMachine program initialMachine) initialMachine node

/-- The initial machine and source program belong to the capture scope. Within
that scope an executable occurrence path identifies the whole machine input. -/
def captureInput (before after : WorkState) : Bool := decide (before.trace = after.trace)

theorem captureInput_sound (program : Program) (initialMachine : NativeMachine) :
    Preparation.SoundMatch (occurrenceSystem program) (captureDomain program initialMachine)
      captureInput := by
  intro before after beforeValid afterValid accepted
  have traces : before.trace = after.trace := by simpa [captureInput] using accepted
  have same := WorkOccurrence.eq_of_valid_trace
    (capturePathMachine program initialMachine) beforeValid afterValid traces
  subst after
  exact ⟨rfl, rfl⟩

theorem captureDomain_closed (program : Program) (initialMachine : NativeMachine)
    (before : WorkState) (valid : captureDomain program initialMachine before)
    (after : WorkState) (member : after ∈ (occurrenceSystem program).successors before) :
    captureDomain program initialMachine after :=
  WorkOccurrence.successor_valid (capturePathMachine program initialMachine) valid member

abbrev PreparedSession (Memory : Type*) :=
  Preparation.Session (List Nat) WorkState (Outcome × List Nat) Memory

def preparedInitial {Memory : Type*}
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) : PreparedSession Memory :=
  ⟨Snapshot.initial controller [WorkOccurrence.root initialMachine], fun _ => none⟩

theorem preparedInitial_valid {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) :
    (preparedInitial controller initialMachine).Valid (occurrenceSystem program)
      (captureDomain program initialMachine) := by
  constructor
  · exact Preparation.empty_valid _ _
  · intro node member
    have root : node = WorkOccurrence.root initialMachine := by
      simpa [preparedInitial, Snapshot.initial, Mettapedia.GSLT.Core.BranchingTemporal.initial]
        using member
    subst node
    exact WorkOccurrence.root_valid (capturePathMachine program initialMachine) initialMachine

/-- Arbitrary preparation/publication slices preserve the actual native
ordered prefix and complete residual worlds. Preparation may spend speculative
work; this statement does not identify that expenditure with serial cost. -/
theorem native_prepared_prefix_exact {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState))
    (admitted : ∀ action ∈ actions, ∀ node ∈ action.inputs,
      captureDomain program initialMachine node) :
    (Preparation.execute (occurrenceSystem program) controller WorkOccurrence.trace captureInput
      actions (preparedInitial controller initialMachine)).state =
      Snapshot.run (occurrenceSystem program) controller (Preparation.publications actions)
        (Snapshot.initial controller [WorkOccurrence.root initialMachine]) :=
  Preparation.execute_agrees _ _ _ _ _ (captureInput_sound program initialMachine)
    (captureDomain_closed program initialMachine) actions _
    (preparedInitial_valid program controller initialMachine) admitted

/-- A bounded physical executor owns the still-unexecuted transcript together
with its prepared captures and original native snapshot. -/
def preparedCheckpoint {Memory : Type*}
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState)) :
    Preparation.Checkpoint (List Nat) WorkState (Outcome × List Nat) Memory :=
  ⟨preparedInitial controller initialMachine, actions, 0⟩

/-- Strict input refusal and exhausted executor budget preserve the actual
native prefix at its accepted parent-tick count. The whole checkpoint retains
private captures and every unfinished physical action, including a refused
publication. Its tick counter is not a speculative cost receipt. -/
theorem native_prepared_checked_prefix {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (initialMachine : NativeMachine) (actions : List (Preparation.Action WorkState))
    (admitted : ∀ action ∈ actions, ∀ node ∈ action.inputs,
      captureDomain program initialMachine node) (fuel : Nat) :
    let result := Preparation.Checkpoint.run (occurrenceSystem program) controller
      WorkOccurrence.trace captureInput fuel (preparedCheckpoint controller initialMachine actions)
    result.session.state = Snapshot.run (occurrenceSystem program) controller result.ticks
      (Snapshot.initial controller [WorkOccurrence.root initialMachine]) := by
  apply Preparation.Checkpoint.run_agrees (occurrenceSystem program) controller
    WorkOccurrence.trace (captureDomain program initialMachine) captureInput
    (captureInput_sound program initialMachine) (captureDomain_closed program initialMachine)
  · exact ⟨preparedInitial_valid program controller initialMachine, admitted⟩
  · rfl

/-- Cumulative accepted ticks, unfinished actions and captured native worlds
are transported together on a bounded resume, without replaying the prefix. -/
theorem native_checked_resume_exact {Memory : Type*} (program : Program)
    (controller : Controller WorkState (Outcome × List Nat) Memory)
    (point : Preparation.Checkpoint (List Nat) WorkState (Outcome × List Nat) Memory)
    (first second : Nat) :
    Preparation.Checkpoint.run (occurrenceSystem program) controller WorkOccurrence.trace
      captureInput (first + second) point =
      Preparation.Checkpoint.run (occurrenceSystem program) controller WorkOccurrence.trace
        captureInput second (Preparation.Checkpoint.run (occurrenceSystem program) controller
          WorkOccurrence.trace captureInput first point) :=
  Preparation.Checkpoint.run_add _ _ _ _ _ _ _

/-- Root paths coincide across different goals. The program/initial-machine
scope in the input authority is therefore necessary. -/
theorem captureInput_root_scopes_collide (before after : NativeMachine) :
    captureInput (WorkOccurrence.root before) (WorkOccurrence.root after) = true := by
  simp [captureInput, WorkOccurrence.root]

/-- The scope check refuses a root belonging to a different authored goal,
even though its successor-index key is the same empty path. -/
theorem different_goal_capture_refused (program : Program) :
    ¬ captureDomain program (initial (.symbol "left"))
      (WorkOccurrence.root (initial (.symbol "right"))) := by
  intro valid
  have equality : initial (.symbol "left") = initial (.symbol "right") := by
    simpa [captureDomain, WorkOccurrence.ValidFrom, WorkOccurrence.root,
      Mettapedia.Machines.OccurrenceMachineCore.follow] using valid
  have lookupEquality := congrArg (fun machine => machine.world.heap.lookup rootCell) equality
  simp [initial, Heap.lookup] at lookupEquality

section PendingCoefficients

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- An absent annotation follows the original successor directly. An authored
annotation starts an actual coefficient computation at the captured row. -/
def coefficientJob {V : Type} [One V] (annotation : Row → Option Atom)
    (before after : NativeMachine) : V ⊕ Score :=
  match NativeGradeAttachment.captureNext before after with
  | none => .inl 1
  | some capture =>
      match annotation capture.row with
      | none => .inl 1
      | some expression => .inr (capture.score expression)

/-- Only an actually halted scoring machine has returned its result. Each
other quantum is an ordinary Need transition, retaining the capture. -/
def coefficientSource (program : Program) : Score → Score ⊕ List Score :=
  fun score => if isHalted score.machine then .inl score else .inr (scoreStep program score)

def coefficientReadout {V : Type} (interpretation : Outcome → Option V)
    (score : Score) : Option V := (scoreResult score).bind interpretation

/-- Semantic scoring shares the captured lazy world with its continuation.
It restores the retained body control and adds actual scoring work once.
Scheduling advice deliberately uses a different, detached continuation. -/
def resumeCoefficientMachine (machine : NativeMachine) (score : Score) : NativeMachine :=
  { machine with world := score.machine.world, work := machine.work.add score.machine.work }

def resumeCoefficient (body : WorkState) (score : Score) : WorkState :=
  { body with state := resumeCoefficientMachine body.state score }

/-- Nested scoring restores a parent's exact instruction and origin while
retaining the child's completed lazy world and expenditure. -/
def resumeCoefficientScore (parent child : Score) : Score :=
  { parent with machine := resumeCoefficientMachine parent.machine child }

/-- Scoring follows actual Need instructions and may evaluate a captured
child coefficient before restoring its parent. The return is permitted only
for a halted child belonging to that exact suspended machine. This relation
does not identify a nested return with an ordinary Need instruction. -/
inductive ScoreEvaluation (program : Program) : Score → Score → Prop where
  | root (score : Score) : ScoreEvaluation program score score
  | step {initial before after : Score} :
      ScoreEvaluation program initial before → after ∈ scoreStep program before →
      ScoreEvaluation program initial after
  | resume {initial parent child : Score} :
      ScoreEvaluation program initial parent →
      ScoreEvaluation program (child.origin.score child.expression) child →
      child.origin.body = parent.machine → isHalted child.machine = true →
      ScoreEvaluation program initial (resumeCoefficientScore parent child)

theorem score_evaluation_keeps_capture (program : Program) (initial next : Score)
    (evaluated : ScoreEvaluation program initial next) :
    next.origin = initial.origin ∧ next.expression = initial.expression := by
  induction evaluated with
  | root => exact ⟨rfl, rfl⟩
  | step _ member ih =>
      obtain ⟨origin, expression, _⟩ := score_step_origin program _ _ member
      exact ⟨origin.trans ih.1, expression.trans ih.2⟩
  | resume _ _ _ _ parentIH _ => exact parentIH

/-- Every actual equation admission encountered while scoring belongs to
the same coefficient account. In particular, an argument forced by a score
does not lose its own annotation when its cell is subsequently reused. -/
def gradedCoefficientSource {V : Type} [One V] (program : Program)
    (annotation : Row → Option Atom) :
    WeightedBranchingResumption.Coalgebra Score Score (V ⊕ Score) :=
  fun score => if isHalted score.machine then .inl score else
    .inr ((scoreStep program score).map fun next =>
      (next, coefficientJob annotation score.machine next.machine))

abbrev NestedWork := WeightedBranchingResumption.NestedPendingState WorkState Score
abbrev NestedResult :=
  WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState Score Score

/-- A completed value observation reads the retained native control.
Retryable and stable faults remain full returns in the contribution list;
this selected value readout does not count them as successful values. -/
def completedValue (body : WorkState) : Option Atom :=
  match body.state.control with
  | .halted (.value value) => some value
  | _ => none

/-- The same completed value observation works for flat and nested pending
work. Parked grades and cut states are never emitted as body values. -/
def completedValues {V Retained Work : Type}
    (leaves : WeightedResumption.Contributions ((WorkState ⊕ Retained) ⊕ Work) V) :
    WeightedResumption.Contributions Atom V :=
  WeightedBranchingResumption.nestedSelected completedValue leaves

/-- Satisfying a value request may coexist with retained work. Claiming a
shortage requires absence of both parked grade results and pending states. -/
def nestedValueOutcome {V : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions (NestedResult ⊕ NestedWork) V) :
    Mettapedia.GSLT.Core.BoundedSelection.SelectOutcome :=
  WeightedBranchingResumption.nestedSelectionOutcome completedValue requested leaves

theorem native_nested_value_saturation_iff {V : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions (NestedResult ⊕ NestedWork) V) :
    nestedValueOutcome requested leaves = .saturated ↔
      (completedValues leaves).length < requested ∧
        WeightedBranchingResumption.parkedGrades
          (WeightedBranchingResumption.nestedObligations leaves) = [] ∧
        WeightedBranchingResumption.pendingInstructions
          (WeightedBranchingResumption.nestedObligations leaves) = [] :=
  WeightedBranchingResumption.nested_selection_saturated_iff completedValue requested leaves

/-- The nested adapter uses the shared pending-coefficient stack. Both body
and score instructions run through the original Need step relation. -/
def nestedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra NestedWork NestedResult V :=
  WeightedBranchingResumption.nestedPendingSource
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (gradedCoefficientSource program annotation) (coefficientReadout interpretation)
    resumeCoefficient resumeCoefficientScore

def nestedAdmittedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) :
    WeightedBranchingResumption.Coalgebra NestedWork NestedResult V :=
  WeightedBranchingResumption.admittingSourceAt
    (nestedSource program annotation interpretation)
    (fun pending => match pending with
      | .inl _ => false
      | .inr (_, score, _) => isHalted score.machine) admit

/-- Nested admission preserves whole surviving occurrences, including all
parent frames. It cannot manufacture a contribution or replace its residual. -/
theorem native_nested_admitted_occurrences_sublist {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : NestedWork) :
    List.Sublist
      (WeightedBranchingResumption.contributions
        (nestedAdmittedSource program annotation interpretation admit) fuel before)
      (WeightedBranchingResumption.contributions
        (nestedSource program annotation interpretation) fuel before) :=
  WeightedBranchingResumption.admittingAt_contributions_sublist _ _ _ _ _

/-- A returned unknown grade is already parked, so later slices do not
poll it or repeat its scoring work. Its original factor and owned stack
remain a physical occurrence while other pending instructions continue. -/
theorem native_nested_parked_persists {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (first second : Nat) (before : NestedWork) :
    (WeightedBranchingResumption.parkedGrades
      (WeightedBranchingResumption.nestedObligations
        (WeightedBranchingResumption.contributions
          (nestedAdmittedSource program annotation interpretation admit) first before))).Sublist
    (WeightedBranchingResumption.parkedGrades
      (WeightedBranchingResumption.nestedObligations
        (WeightedBranchingResumption.contributions
          (nestedAdmittedSource program annotation interpretation admit)
          (first + second) before))) :=
  WeightedBranchingResumption.nested_parked_sublist_add _ _ _ _

/-- Refusing a completed inner coefficient exposes no executable parent
continuation. The parent and body have not run past this admission boundary. -/
theorem native_nested_parent_refused {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (child parent : Score) (parents : List Score) (value : V)
    (halted : isHalted child.machine = true)
    (decoded : coefficientReadout interpretation child = some value)
    (refused : admit value = false) :
    nestedAdmittedSource program annotation interpretation admit
      (.inr (body, child, parent :: parents)) = .inr [] := by
  simp [nestedAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    nestedSource, WeightedBranchingResumption.nestedPendingSource,
    gradedCoefficientSource, halted, decoded, refused]

/-- An uninterpreted inner coefficient remains a retained result with its
entire stack, regardless of the test on interpreted coefficients. -/
theorem native_nested_unknown_retains_stack {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (parents : List Score)
    (halted : isHalted score.machine = true)
    (unknown : coefficientReadout interpretation score = none) :
    nestedAdmittedSource program annotation interpretation admit (.inr (body, score, parents)) =
      .inl (.inr (body, score, parents)) := by
  simp [nestedAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    nestedSource, WeightedBranchingResumption.nestedPendingSource,
    gradedCoefficientSource, halted, unknown]

theorem nested_resume_preserves_parent (parent child : Score) :
    (resumeCoefficientScore parent child).origin = parent.origin ∧
    (resumeCoefficientScore parent child).expression = parent.expression ∧
    (resumeCoefficientScore parent child).machine.control = parent.machine.control ∧
    (resumeCoefficientScore parent child).machine.world = child.machine.world ∧
    (resumeCoefficientScore parent child).machine.work =
      parent.machine.work.add child.machine.work := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A split preserves all parent coefficient frames together with the body,
worlds and ordered product. No completed inner factor is charged again. -/
theorem native_nested_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (first second : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (nestedSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (nestedSource program annotation interpretation) second pending) := by
  rw [WeightedBranchingResumption.contributions_add]
  apply congrArg (WeightedResumption.sequence
    (WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) first before))
  funext leaf
  cases leaf <;> rfl

abbrev PendingWork := WeightedBranchingResumption.PendingState WorkState Score
abbrev PendingResult := WeightedBranchingResumption.PendingAnswer WorkState WorkState Score

/-- This one-level interpretation executes scoring steps without further
annotations. The nested interpretation above is required when a score forces
graded argument work; the distinction has an executable negative control. -/
def pendingSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra PendingWork PendingResult V :=
  WeightedBranchingResumption.pendingSource
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (coefficientSource program) (coefficientReadout interpretation) resumeCoefficient

/-- Candidate admission uses the same captured coefficient computation as
attachment. The declared test runs at its returned coefficient, before the
retained body has an executable successor. It is not a scheduling priority.
The test must already be resolved; a comparison computation belongs in the
pending coefficient job rather than an invented Boolean answer here. -/
def pendingAdmittedSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) :
    WeightedBranchingResumption.Coalgebra PendingWork PendingResult V :=
  WeightedBranchingResumption.admittingSourceAt
    (pendingSource program annotation interpretation)
    (fun pending => match pending with
      | .inl _ => false
      | .inr (_, score) => isHalted score.machine) admit

/-- Admission cannot invent a result, duplicate it, change its coefficient,
or replace its open world. This compares complete occurrence lists, before
any aggregation or support readout. -/
theorem native_admitted_occurrences_sublist {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : PendingWork) :
    List.Sublist
      (WeightedBranchingResumption.contributions
        (pendingAdmittedSource program annotation interpretation admit) fuel before)
      (WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) fuel before) :=
  WeightedBranchingResumption.admittingAt_contributions_sublist _ _ _ _ _

/-- A rejected coefficient exposes no body successor. Filtering an already
executed body at the answer read would not satisfy this boundary. -/
theorem native_admitted_body_refused {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (value : V)
    (halted : isHalted score.machine = true)
    (decoded : coefficientReadout interpretation score = some value)
    (refused : admit value = false) :
    pendingAdmittedSource program annotation interpretation admit (.inr (body, score)) =
      .inr [] := by
  simp [pendingAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    pendingSource, WeightedBranchingResumption.pendingSource, coefficientSource,
    halted, decoded, refused]

/-- An admitted coefficient resumes the exact retained control with the
score's completed lazy world, and contributes its value once. -/
theorem native_admitted_body_resumes {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (body : WorkState) (score : Score) (value : V)
    (halted : isHalted score.machine = true)
    (decoded : coefficientReadout interpretation score = some value)
    (accepted : admit value = true) :
    pendingAdmittedSource program annotation interpretation admit (.inr (body, score)) =
      .inr [(.inl (resumeCoefficient body score), value)] := by
  simp [pendingAdmittedSource, WeightedBranchingResumption.admittingSourceAt,
    WeightedBranchingResumption.admittingSource,
    pendingSource, WeightedBranchingResumption.pendingSource, coefficientSource,
    halted, decoded, accepted]

@[simp] theorem coefficient_job_unannotated {V : Type} [One V]
    (before after : NativeMachine) :
    coefficientJob (V := V) (fun _ => none) before after = .inl 1 := by
  cases inspected : NativeGradeAttachment.captureNext before after <;>
    simp [coefficientJob, inspected]

theorem unannotated_body_is_settled {V : Type} [One V] (program : Program) :
    NeedWeightedResumption.source (specification program)
      (coefficientJob (V := V) (fun _ => none)) =
    WeightedBranchingResumption.settledBody
      (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V))) := by
  funext state
  cases control : state.state.control <;>
    simp only [NeedWeightedResumption.source, control,
      WeightedBranchingResumption.settledBody, NeedWeightedResumption.successors,
      List.map_map, coefficient_job_unannotated] <;> rfl

/-- An unannotated native program has the exact original contributions at
the same budget. It creates no scoring job or administrative scoring step. -/
theorem native_pending_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (pendingSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (WeightedBranchingResumption.settledLeaf leaf.1, leaf.2)) := by
  unfold pendingSource
  rw [unannotated_body_is_settled]
  exact WeightedBranchingResumption.pending_settled_agrees _ _ _ _ _ _

/-- Extending the coefficient stack does not change an unannotated program,
including its exact finite budget, occurrence order and full residuals. -/
theorem native_nested_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (nestedSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold nestedSource
  rw [unannotated_body_is_settled]
  exact WeightedBranchingResumption.nested_pending_settled_agrees _ _ _ _ _ _ _

/-- An authored guard does not test plain or administrative unit edges.
Unannotated programs keep their exact ordinary frontier, for any predicate. -/
theorem native_admitted_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (pendingAdmittedSource program (fun _ => none) interpretation admit) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (WeightedBranchingResumption.settledLeaf leaf.1, leaf.2)) := by
  unfold pendingAdmittedSource pendingSource
  rw [unannotated_body_is_settled]
  apply WeightedBranchingResumption.contributions_reindex
    (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
    _ Sum.inl Sum.inl ?_ fuel before
  intro state
  cases inspected : NeedWeightedResumption.source (specification program)
      (fun _ _ => (1 : V)) state <;>
    simp [WeightedBranchingResumption.admittingSourceAt,
      WeightedBranchingResumption.pendingSource, WeightedBranchingResumption.settledBody,
      inspected, List.map_map]

/-- Nested authored admission also preserves unannotated execution even
when the predicate would reject the unit coefficient of an ordinary step. -/
theorem native_nested_admitted_unannotated_exact {V : Type} [Monoid V]
    (program : Program) (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (nestedAdmittedSource program (fun _ => none) interpretation admit) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold nestedAdmittedSource nestedSource
  rw [unannotated_body_is_settled]
  apply WeightedBranchingResumption.contributions_reindex
    (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
    _ Sum.inl Sum.inl ?_ fuel before
  intro state
  cases inspected : NeedWeightedResumption.source (specification program)
      (fun _ _ => (1 : V)) state <;>
    simp [WeightedBranchingResumption.admittingSourceAt,
      WeightedBranchingResumption.nestedPendingSource, WeightedBranchingResumption.settledBody,
      inspected, List.map_map]

/-- The physical admission, world and variable cells supply the coefficient;
neither a later environment nor a second enumeration supplies its bindings. -/
theorem coefficient_job_actual_capture {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine)
    (capture : Captured) (expression : Atom)
    (captured : NativeGradeAttachment.captureNext before after = some capture)
    (authored : annotation capture.row = some expression) :
    coefficientJob (V := V) annotation before after = .inr (capture.score expression) ∧
    (capture.score expression).machine.world = after.world ∧
    (capture.score expression).machine.control =
      .run (.evaluate expression capture.row.environment) [] := by
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact before after capture captured
  refine ⟨by simp [coefficientJob, captured, authored], ?_, rfl⟩
  simpa only [Captured.score, Captured.body] using
    congrArg (fun machine : NativeMachine => machine.world) same

/-- A coefficient job retains the actual selected row and its authored
expression. The witness comes from capture, before scoring or body execution. -/
theorem coefficient_job_capture {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    ∃ capture expression,
      NativeGradeAttachment.captureNext before after = some capture ∧
      annotation capture.row = some expression ∧ score = capture.score expression := by
  cases captured : NativeGradeAttachment.captureNext before after with
  | none => simp [coefficientJob, captured] at chosen
  | some capture =>
      cases authored : annotation capture.row with
      | none => simp [coefficientJob, captured, authored] at chosen
      | some expression =>
          simp only [coefficientJob, captured, authored, Sum.inr.injEq] at chosen
          exact ⟨capture, expression, rfl, authored, chosen.symm⟩

theorem coefficient_job_starts_at_zero {V : Type} [One V]
    (annotation : Row → Option Atom) (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    score.machine.work.transitions = 0 := by
  obtain ⟨_, _, _, _, rfl⟩ := coefficient_job_capture annotation before after score chosen
  rfl

theorem coefficient_running_uses_need (program : Program) (score next : Score)
    (running : isHalted score.machine = false)
    (member : next ∈ scoreStep program score) :
    coefficientSource program score = .inr (scoreStep program score) ∧
    next.origin = score.origin ∧ next.expression = score.expression ∧
    next.machine.work.transitions = score.machine.work.transitions + 1 := by
  exact ⟨by simp [coefficientSource, running], score_step_origin program score next member⟩

theorem resume_coefficient_preserves_continuation (body : WorkState) (score : Score) :
    (resumeCoefficient body score).state.control = body.state.control ∧
    (resumeCoefficient body score).trace = body.trace ∧
    (resumeCoefficient body score).state.world = score.machine.world ∧
    (resumeCoefficient body score).state.work.transitions =
      body.state.work.transitions + score.machine.work.transitions := ⟨rfl, rfl, rfl, rfl⟩

/-- A pending score belongs to this physical body's capture and has an actual
native scoring derivation from that capture, including its evolving world. -/
def CapturedCoefficient (program : Program) (body : WorkState) (score : Score) : Prop :=
  score.origin.body = body.state ∧
    Mettapedia.GSLT.Core.BranchingTemporal.Generated (scoringSystem program)
      [score.origin.score score.expression] score

theorem coefficient_job_has_captured_derivation {V : Type} [One V]
    (program : Program) (annotation : Row → Option Atom)
    (before body : WorkState) (score : Score)
    (chosen : coefficientJob (V := V) annotation before.state body.state = .inr score) :
    CapturedCoefficient program body score := by
  obtain ⟨capture, expression, captured, _, rfl⟩ :=
    coefficient_job_capture annotation before.state body.state score chosen
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact
    before.state body.state capture captured
  exact ⟨same, .root (by simp [Captured.score])⟩

theorem captured_coefficient_step (program : Program) (body : WorkState) (score next : Score)
    (valid : CapturedCoefficient program body score) (member : next ∈ scoreStep program score) :
    CapturedCoefficient program body next := by
  obtain ⟨origin, expression, _⟩ := score_step_origin program score next member
  refine ⟨(congrArg Captured.body origin).trans valid.1, ?_⟩
  rw [origin, expression]
  exact .successor valid.2 member

def pendingValid (program : Program) : PendingWork → Prop :=
  Sum.elim (fun _ => True) (fun held => CapturedCoefficient program held.1 held.2)

def pendingResultValid (program : Program) : PendingResult → Prop :=
  Sum.elim (fun body => isHalted body.state = true)
    (fun held => CapturedCoefficient program held.1 held.2 ∧ isHalted held.2.machine = true)

/-- Every pending coefficient has a native derivation from the correct
captured body. Completed body answers and uninterpreted coefficient results
have distinct, actual halt obligations. -/
theorem native_pending_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) (valid : pendingValid program before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel before,
      Sum.elim (pendingResultValid program) (pendingValid program) leaf.1 := by
  apply WeightedBranchingResumption.contributions_invariant
    (pendingSource program annotation interpretation) (pendingValid program)
    (pendingResultValid program) ?_ ?_ fuel before valid
  · intro state answer inherited returned
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              inspected, Sum.inl.injEq] at returned
            subst answer
            obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff
              (specification program) (coefficientJob annotation) body done).mp inspected
            exact halted
        | inr children =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨body, score⟩
        cases halted : isHalted score.machine with
        | false =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource,
              coefficientSource, halted] at returned
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | some value =>
                simp [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, decoded] at returned
            | none =>
                simp only [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inl.injEq] at returned
                subst answer
                exact ⟨inherited, halted⟩
  · intro state alternatives inherited requested next member
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp [pendingSource, WeightedBranchingResumption.pendingSource, inspected] at requested
        | inr children =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            cases coefficient with
            | inl value => cases same; exact True.intro
            | inr score =>
                cases same
                have located : (child, Sum.inr score) ∈ NeedWeightedResumption.successors
                    (specification program) (coefficientJob (V := V) annotation) body := by
                  cases control : body.state.control <;>
                    simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr,
                      Sum.inr.injEq]
                obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
                  (specification program) (coefficientJob annotation) body child (.inr score)).mp located
                exact coefficient_job_has_captured_derivation
                  program annotation body child score caused.symm
    | inr held =>
        rcases held with ⟨body, score⟩
        cases halted : isHalted score.machine with
        | false =>
            simp only [pendingSource, WeightedBranchingResumption.pendingSource,
              coefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
              Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
            exact captured_coefficient_step program body score child inherited present
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | none =>
                simp [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, decoded] at requested
            | some value =>
                simp only [pendingSource, WeightedBranchingResumption.pendingSource,
                  coefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inr.injEq] at requested
                subst alternatives
                have same := List.mem_singleton.mp member
                subst next
                exact True.intro

/-- Each nested frame keeps its authored expression and an evaluation from
its captured bindings. Its origin belongs to the exact suspended caller;
the outermost caller is the retained body. -/
def NestedCapturedCoefficient (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) : Score → List Score → Prop
  | score, [] =>
      annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = body.state
  | score, parent :: parents =>
      annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = parent.machine ∧
      NestedCapturedCoefficient program annotation body parent parents

theorem nested_capture_head (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents) :
    annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score := by
  cases parents <;> exact ⟨valid.1, valid.2.1⟩

private theorem nested_capture_replace (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (before after : Score) (parents : List Score)
    (same : after.origin = before.origin)
    (evaluated : annotation after.origin.row = some after.expression ∧
      ScoreEvaluation program (after.origin.score after.expression) after)
    (valid : NestedCapturedCoefficient program annotation body before parents) :
    NestedCapturedCoefficient program annotation body after parents := by
  cases parents with
  | nil =>
      exact ⟨evaluated.1, evaluated.2, (congrArg Captured.body same).trans valid.2.2⟩
  | cons parent rest =>
      exact ⟨evaluated.1, evaluated.2,
        (congrArg Captured.body same).trans valid.2.2.1, valid.2.2.2⟩

theorem coefficient_job_nested_capture {V : Type} [One V]
    (program : Program) (annotation : Row → Option Atom)
    (before after : NativeMachine) (score : Score)
    (chosen : coefficientJob (V := V) annotation before after = .inr score) :
    annotation score.origin.row = some score.expression ∧
      ScoreEvaluation program (score.origin.score score.expression) score ∧
      score.origin.body = after := by
  obtain ⟨capture, expression, captured, authored, rfl⟩ :=
    coefficient_job_capture annotation before after score chosen
  obtain ⟨same, _⟩ := NativeGradeAttachment.captured_next_exact before after capture captured
  exact ⟨authored, .root _, same⟩

theorem nested_capture_step (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score next : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents)
    (member : next ∈ scoreStep program score) :
    NestedCapturedCoefficient program annotation body next parents := by
  obtain ⟨origin, expression, _⟩ := score_step_origin program score next member
  obtain ⟨authored, evaluated⟩ := nested_capture_head program annotation body score parents valid
  apply nested_capture_replace program annotation body score next parents origin ?_ valid
  rw [origin, expression]
  exact ⟨authored, .step evaluated member⟩

theorem nested_capture_resumes (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (child parent : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body child (parent :: parents))
    (halted : isHalted child.machine = true) :
    NestedCapturedCoefficient program annotation body
      (resumeCoefficientScore parent child) parents := by
  obtain ⟨_, childEvaluation, captured, parentValid⟩ := valid
  obtain ⟨authored, parentEvaluation⟩ :=
    nested_capture_head program annotation body parent parents parentValid
  apply nested_capture_replace program annotation body parent
    (resumeCoefficientScore parent child) parents rfl ?_ parentValid
  exact ⟨authored, .resume parentEvaluation childEvaluation captured halted⟩

/-- A child cannot restore a different caller, even when the callers came
from the same authored equation or their coefficient values coincide. -/
theorem nested_capture_wrong_parent_refused (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (child parent : Score) (parents : List Score)
    (different : child.origin.body.control ≠ parent.machine.control) :
    ¬ NestedCapturedCoefficient program annotation body child (parent :: parents) := by
  intro valid
  exact different (congrArg (fun machine : NativeMachine => machine.control) valid.2.2.1)

def nestedValid (program : Program) (annotation : Row → Option Atom) : NestedWork → Prop :=
  Sum.elim (fun _ => True)
    (fun held => NestedCapturedCoefficient program annotation held.1 held.2.1 held.2.2)

def nestedResultValid (program : Program) (annotation : Row → Option Atom) :
    NestedResult → Prop :=
  Sum.elim (fun body => isHalted body.state = true)
    (fun held => NestedCapturedCoefficient program annotation held.1 held.2.1 held.2.2 ∧
      isHalted held.2.1.machine = true)

/-- Every active or retained parent score belongs to its captured caller.
Actual Need transitions and completed child returns establish its evaluation;
unknown readouts retain this evidence and the complete parent stack. -/
theorem native_nested_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : NestedWork) (valid : nestedValid program annotation before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) fuel before,
      Sum.elim (nestedResultValid program annotation) (nestedValid program annotation) leaf.1 := by
  apply WeightedBranchingResumption.contributions_invariant
    (nestedSource program annotation interpretation) (nestedValid program annotation)
    (nestedResultValid program annotation) ?_ ?_ fuel before valid
  · intro state answer inherited returned
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected, Sum.inl.injEq] at returned
            subst answer
            obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff
              (specification program) (coefficientJob annotation) body done).mp inspected
            exact halted
        | inr children =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected] at returned
    | inr held =>
        rcases held with ⟨body, score, parents⟩
        cases halted : isHalted score.machine with
        | false =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              gradedCoefficientSource, halted] at returned
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | some value =>
                cases parents <;>
                  simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                    gradedCoefficientSource, halted, decoded] at returned
            | none =>
                simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                  gradedCoefficientSource, halted, ↓reduceIte, decoded,
                  Sum.inl.injEq] at returned
                subst answer
                exact ⟨inherited, halted⟩
  · intro state alternatives inherited requested next member
    cases state with
    | inl body =>
        cases inspected : NeedWeightedResumption.source (specification program)
            (coefficientJob (V := V) annotation) body with
        | inl done =>
            simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected] at requested
        | inr children =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            cases coefficient with
            | inl value => cases same; exact True.intro
            | inr score =>
                cases same
                have located : (child, Sum.inr score) ∈ NeedWeightedResumption.successors
                    (specification program) (coefficientJob (V := V) annotation) body := by
                  cases control : body.state.control <;>
                    simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr,
                      Sum.inr.injEq]
                obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
                  (specification program) (coefficientJob annotation) body child (.inr score)).mp located
                exact coefficient_job_nested_capture program annotation body.state child.state
                  score caused.symm
    | inr held =>
        rcases held with ⟨body, score, parents⟩
        cases halted : isHalted score.machine with
        | false =>
            simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
              gradedCoefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
              List.map_map, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨child, present, same⟩ := List.mem_map.mp member
            dsimp only [Function.comp_apply] at same
            have childValid := nested_capture_step program annotation body score child parents
              inherited present
            cases chosen : coefficientJob (V := V) annotation score.machine child.machine with
            | inl value =>
                cases same
                simp only [chosen, nestedValid]
                exact childValid
            | inr inner =>
                cases same
                simp only [chosen, nestedValid]
                obtain ⟨authored, evaluated, captured⟩ := coefficient_job_nested_capture
                  program annotation score.machine child.machine inner chosen
                exact ⟨authored, evaluated, captured, childValid⟩
        | true =>
            cases decoded : coefficientReadout interpretation score with
            | none =>
                simp [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                  gradedCoefficientSource, halted, decoded] at requested
            | some value =>
                cases parents with
                | nil =>
                    simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                      gradedCoefficientSource, halted, ↓reduceIte, decoded,
                      Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    exact True.intro
                | cons parent rest =>
                    simp only [nestedSource, WeightedBranchingResumption.nestedPendingSource,
                      gradedCoefficientSource, halted, ↓reduceIte, decoded,
                      Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    exact nested_capture_resumes program annotation body score parent rest
                      inherited halted

/-- The same capture obligations hold after declared filtering; the sublist
comparison transports surviving occurrences without replacing their worlds. -/
theorem native_nested_admitted_valid {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) (fuel : Nat) (before : NestedWork)
    (valid : nestedValid program annotation before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation interpretation admit) fuel before,
      Sum.elim (nestedResultValid program annotation) (nestedValid program annotation) leaf.1 := by
  intro leaf member
  apply native_nested_valid program annotation interpretation fuel before valid leaf
  exact (native_nested_admitted_occurrences_sublist program annotation interpretation
    admit fuel before).subset member

/-- This metric counts actual Need instructions, including those executed
inside grades. Suspended parents remain in the account. Administrative
coefficient returns are not Need instructions; runtime event costs and
cost-observation charges have their separate declared profiles. -/
def nestedInstructionCount : NestedWork → Nat :=
  WeightedBranchingResumption.nestedStateMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)

/-- This observation forgets the worlds and coefficients, but retains the
instruction account of every owned frame. Construct it only when requested. -/
def nestedInstructionAccounts : NestedWork → List Nat
  | .inl body => [body.state.work.transitions]
  | .inr (body, score, parents) =>
      body.state.work.transitions :: score.machine.work.transitions ::
        parents.map (fun parent => parent.machine.work.transitions)

theorem nested_instruction_accounts_sum (pending : NestedWork) :
    (nestedInstructionAccounts pending).sum = nestedInstructionCount pending := by
  cases pending with
  | inl body => simp [nestedInstructionAccounts, nestedInstructionCount,
      WeightedBranchingResumption.nestedStateMeter]
  | inr pending =>
      rcases pending with ⟨body, score, parents⟩
      simp [nestedInstructionAccounts, nestedInstructionCount,
        WeightedBranchingResumption.nestedStateMeter, Nat.add_assoc]

def nestedResultInstructionCount : NestedResult → Nat :=
  WeightedBranchingResumption.nestedAnswerMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    (fun score : Score => score.machine.work.transitions)

/-- A finite weighted budget bounds actual instruction expenditure across
all owned frames. Returning a child transfers its work once; suspending or
resuming the computation never resets the cumulative instruction meter. -/
theorem native_nested_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : NestedWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedSource program annotation interpretation) fuel before,
      nestedInstructionCount before ≤
        Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ∧
      Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ≤
        nestedInstructionCount before + fuel := by
  unfold nestedSource nestedInstructionCount nestedResultInstructionCount
  apply WeightedBranchingResumption.nested_contributions_meter_bounds
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (gradedCoefficientSource program annotation) (coefficientReadout interpretation)
    resumeCoefficient resumeCoefficientScore
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    (fun score : Score => score.machine.work.transitions)
    ?_ ?_ ?_ ?_ ?_ ?_ fuel before
  · intro body answer returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (coefficientJob annotation) body answer).mp returned
    rfl
  · intro body alternatives requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (coefficientJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (coefficientJob annotation) body child coefficient).mp located
    refine ⟨step_increments_transition (specification program) _ _
      (List.mem_of_getElem? actual), ?_⟩
    cases coefficient with
    | inl value => exact True.intro
    | inr score =>
        exact coefficient_job_starts_at_zero (V := V) annotation body.state child.state
          score caused.symm
  · intro score result returned
    cases halted : isHalted score.machine with
    | false => simp [gradedCoefficientSource, halted] at returned
    | true =>
        simp only [gradedCoefficientSource, halted, ↓reduceIte, Sum.inl.injEq] at returned
        subst result
        rfl
  · intro score alternatives requested next member
    cases halted : isHalted score.machine with
    | true => simp [gradedCoefficientSource, halted] at requested
    | false =>
        simp only [gradedCoefficientSource, halted, Bool.false_eq_true, ↓reduceIte,
          Sum.inr.injEq] at requested
        subst alternatives
        obtain ⟨child, actual, rfl⟩ := List.mem_map.mp member
        refine ⟨(score_step_origin program score child actual).2.2, ?_⟩
        cases chosen : coefficientJob (V := V) annotation score.machine child.machine with
        | inl value => exact True.intro
        | inr inner =>
            exact coefficient_job_starts_at_zero (V := V) annotation score.machine
              child.machine inner chosen
  · intro body result
    rfl
  · intro parent result
    rfl

/-- Declared admission can remove a contribution, but cannot rewrite the
instruction account of a contribution that survives. -/
theorem native_nested_admitted_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (admit : V → Bool) (fuel : Nat) (before : NestedWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation interpretation admit) fuel before,
      nestedInstructionCount before ≤
        Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ∧
      Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1 ≤
        nestedInstructionCount before + fuel := by
  intro leaf member
  exact native_nested_instruction_bounds program annotation interpretation fuel before leaf
    ((native_nested_admitted_occurrences_sublist program annotation interpretation
      admit fuel before).subset member)

theorem native_pending_score_has_native_path {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before body : WorkState) (score : Score) (value : V)
    (member : (.inr (.inr (body, score)), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel (.inl before)) :
    score.origin.body = body.state ∧
      ∃ count, Steps (specification program) count
        (score.origin.score score.expression).machine score.machine := by
  have valid := native_pending_valid program annotation interpretation fuel (.inl before)
    True.intro (.inr (.inr (body, score)), value) member
  change CapturedCoefficient program body score at valid
  exact ⟨valid.1, (score_generated_native program _ _ valid.2).2.2⟩

/-- An uninterpreted completed coefficient preserves the actual native
calculation, its capture and its result; it is not a fabricated weight. -/
theorem native_uninterpreted_score_has_native_path {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before body : WorkState) (score : Score) (value : V)
    (member : (.inl (.inr (body, score)), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel (.inl before)) :
    score.origin.body = body.state ∧ isHalted score.machine = true ∧
      ∃ count, Steps (specification program) count
        (score.origin.score score.expression).machine score.machine := by
  have valid := native_pending_valid program annotation interpretation fuel (.inl before)
    True.intro (.inl (.inr (body, score)), value) member
  change CapturedCoefficient program body score ∧ isHalted score.machine = true at valid
  exact ⟨valid.1.1, valid.2, (score_generated_native program _ _ valid.1.2).2.2⟩

/-- The original handler law also covers unfinished coefficient machines,
their result readout and their complete body continuation. -/
theorem native_pending_handler_agrees {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (pendingSource program annotation interpretation) fuel before) =
      WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) fuel before :=
  WeightedBranchingResumption.interpret_cut _ _ _

theorem native_pending_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (first second : Nat) (before : PendingWork) :
    WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (pendingSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (pendingSource program annotation interpretation) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions
        (pendingSource program annotation interpretation) first before))
    funext leaf
    cases leaf <;> rfl

/-- A completed body answer is actually halted. Coefficient results outside
the declared algebra have their own result constructor and do not certify it. -/
theorem native_pending_returned_is_halted {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : PendingWork) (after : WorkState) (value : V)
    (member : (.inl (.inl after), value) ∈ WeightedBranchingResumption.contributions
      (pendingSource program annotation interpretation) fuel before) :
    isHalted after.state = true := by
  have valid := WeightedBranchingResumption.pending_contributions_invariant
    (NeedWeightedResumption.source (specification program) (coefficientJob annotation))
    (coefficientSource program) (coefficientReadout interpretation) resumeCoefficient
    (fun _ => True) (fun done => isHalted done.state = true)
    (fun state answer _ returned => by
      obtain ⟨rfl, halted⟩ := (NeedWeightedResumption.source_return_iff (specification program)
        (coefficientJob annotation) state answer).mp returned
      exact halted)
    (fun _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro) fuel before True.intro
    (.inl (.inl after), value) member
  exact valid

/-- Admission retains the same whole-state split law, including coefficient
jobs and rejected alternatives. It does not reset a suspended score's world. -/
theorem native_admitted_resume_exact {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (first second : Nat) (before : PendingWork) :
    WeightedBranchingResumption.contributions
      (pendingAdmittedSource program annotation interpretation admit) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (pendingAdmittedSource program annotation interpretation admit) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (pendingAdmittedSource program annotation interpretation admit) second pending) :=
  by
    rw [WeightedBranchingResumption.contributions_add]
    apply congrArg (WeightedResumption.sequence
      (WeightedBranchingResumption.contributions
        (pendingAdmittedSource program annotation interpretation admit) first before))
    funext leaf
    cases leaf <;> rfl

theorem native_admitted_returned_is_halted {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admit : V → Bool)
    (fuel : Nat) (before : PendingWork) (after : WorkState) (value : V)
    (member : (.inl (.inl after), value) ∈ WeightedBranchingResumption.contributions
      (pendingAdmittedSource program annotation interpretation admit) fuel before) :
    isHalted after.state = true :=
  native_pending_returned_is_halted program annotation interpretation fuel before after value
    ((native_admitted_occurrences_sublist program annotation interpretation admit fuel before).subset
      member)

end PendingCoefficients

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
