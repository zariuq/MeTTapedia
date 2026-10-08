import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeDerivationGrades
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeAttachment
import Mettapedia.GSLT.Dynamics.ResumptionCategory
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory
import Mettapedia.GSLT.Core.InferenceRecording
import Mettapedia.GSLT.Core.FiniteSearchCertificate
import Mathlib.Tactic.Convert

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
Authored predicates use the same handler and owned account. Their phase changes
add no Need instruction; completed coefficient work is not counted twice.
Caller agreement is supplied by the common nested handler and actual captures;
it preserves suspended states without identifying equal occurrences.
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
abbrev capturePathMachine (program : Program) (initialMachine : NativeMachine) :
    Mettapedia.Machines.OccurrenceMachineCore Unit NativeMachine Outcome :=
  NeedInferenceControl.Reference.pathMachine (specification program) initialMachine

section AuthoredHistories

open Mettapedia.GSLT.Ultrainfinite.Route

open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding

/-- Read physical authored choices from real machine events. This observation
omits administrative events; the original history still retains them. -/
def authoredRowAccount (program : Program) (initial : NativeMachine) :=
  eventAccount (capturePathMachine program initial)
    (fun before after _ => FreeMonoid.ofList (newRow before after).toList)

/-- Reading a machine history yields the independently defined authored-row
trace, with the exact number of machine transitions. -/
theorem history_row_trace (program : Program) (initial : NativeMachine)
    {before after : RewriteEventHistory.State (system (capturePathMachine program initial))}
    (history : Quiver.Path before after) :
    RowTrace program (indices (capturePathMachine program initial) history).length
      before.term after.term
      (FreeMonoid.toList ((authoredRowAccount program initial).of history)) := by
  exact ObservedTrace.map _ _
    (fun event => ⟨event.val, event.property⟩) (fun _ => rfl)
    (history_observed_trace (capturePathMachine program initial)
      (fun before after _ => (newRow before after).toList) history)

/-- Every trace admitted by the independent row relation has a machine history.
This is coverage at the row observation, not uniqueness of a history after
administrative events or repeated occurrences have been forgotten. -/
theorem row_trace_history (program : Program) (initial : NativeMachine)
    {count : Nat} {before after : NativeMachine} {choices : List Row}
    (trace : RowTrace program count before after choices) :
    ∃ history : History (capturePathMachine program initial) before after,
      (indices (capturePathMachine program initial) history).length = count ∧
      FreeMonoid.toList ((authoredRowAccount program initial).of history) = choices := by
  apply observed_trace_history (capturePathMachine program initial)
    (fun before after _ => (newRow before after).toList)
  exact ObservedTrace.map _ _
    (fun edge => ⟨edge.index, edge.successorAt⟩) (fun _ => rfl) trace

/-- Interpreting authored provenance recovers the native history coefficient.
Multiplication follows the history order; no commutativity is assumed. -/
theorem history_row_interpretation {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (initial : NativeMachine)
    {before after : RewriteEventHistory.State (system (capturePathMachine program initial))}
    (history : Quiver.Path before after) :
    interpret clause (FreeMonoid.toList ((authoredRowAccount program initial).of history)) =
      (NeedWeightedResumption.coefficientAccount (specification program)
        (edgeGrade clause) initial).of history := by
  let change : FreeMonoid Row →* V := FreeMonoid.lift (fun row => WeighClause.eval row clause)
  have accounts := eventAccount_map (capturePathMachine program initial)
    (fun before after _ => FreeMonoid.ofList (newRow before after).toList) change
  have grades :
      (fun (before after : NativeMachine) (_ : Nat) =>
        change (FreeMonoid.ofList (newRow before after).toList)) =
      (fun before after (_ : Nat) => edgeGrade clause before after) := by
    funext before after index
    cases chosen : newRow before after <;>
      simp [change, edgeGrade, chosen]
  rw [grades] at accounts
  have evaluated := congrArg (fun account => account.of history) accounts
  change change ((authoredRowAccount program initial).of history) =
    (NeedWeightedResumption.coefficientAccount (specification program)
      (edgeGrade clause) initial).of history at evaluated
  simpa only [change, FreeMonoid.lift_apply, interpret,
    ProvenanceInterpretation.interpDeriv] using evaluated

/-- Every independently admitted row trace is represented in the weighted
native frontier at its exact transition depth. The complete producing trace
and coefficient remain, including contributions whose coefficient is zero. -/
theorem row_trace_covered {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row) (initial : NativeMachine)
    {count : Nat} {before after : NativeMachine} {choices : List Row}
    (trace : RowTrace program count before after choices) (priorTrace : List Nat) :
    ∃ events : List Nat,
      events.length = count ∧
      (capturePathMachine program initial).follow before events = some after ∧
      (.inr ⟨after, priorTrace ++ events⟩, interpret clause choices) ∈
        WeightedBranchingResumption.contributions (source program clause)
          count ⟨before, priorTrace⟩ := by
  obtain ⟨history, depth, rows⟩ := row_trace_history program initial trace
  refine ⟨indices (capturePathMachine program initial) history, depth,
    follow_indices _ history, ?_⟩
  have present := NeedWeightedResumption.history_pending_contribution
    (specification program) (edgeGrade clause) initial history priorTrace
  have coefficient := history_row_interpretation program clause initial history
  rw [rows] at coefficient
  rw [← coefficient] at present
  simpa only [source, capturePathMachine, depth] using present

/-- Bounded recording of the actual Need controller retains its complete
semantic snapshot after erasure. The observer cannot select work or alter
worlds; this comparison fixes the original controller and tick allowance. -/
theorem recording_erasure {Memory Event : Type}
    (program : Program) (base : Controller WorkState (Outcome × List Nat) Memory)
    (observe : Memory → WorkState → Option (Outcome × List Nat) → List WorkState → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Snapshot WorkState (Outcome × List Nat) Memory) :
    Recording.erase (Snapshot.run (occurrenceSystem program)
      (Recording.controller base observe capacity) fuel (Recording.start snapshot capacity)) =
        Snapshot.run (occurrenceSystem program) base fuel snapshot :=
  Recording.run_erasure _ _ _ _ _ _

/-- Each retained selected Need occurrence has its ordinary replay history
and independently admitted authored-row trace. Recording exhaustion does not
certify search exhaustion, and the trace is relative to this program and root. -/
theorem recorded_authored_history {Memory : Type}
    (program : Program) (base : Controller WorkState (Outcome × List Nat) Memory)
    (initial : NativeMachine) (capacity fuel : Nat) (record : Recording.Prefix WorkState)
    (retained : (Snapshot.run (occurrenceSystem program)
      (Recording.controller base (fun _ selected _ _ => selected) (some capacity)) fuel
        (Recording.start (Snapshot.initial base [WorkOccurrence.root initial])
          (some capacity))).memory.2 = some record)
    {node : WorkState} (member : node ∈ record.items) :
    ∃ history : History (capturePathMachine program initial) initial node.state,
      indices (capturePathMachine program initial) history = node.trace ∧
      RowTrace program node.trace.length initial node.state
        (FreeMonoid.toList ((authoredRowAccount program initial).of history)) := by
  have replay := Recording.retained_occurrence_replays
    (capturePathMachine program initial) base initial capacity fuel record retained member
  let history := ofTrace (capturePathMachine program initial) node.trace replay
  have exactTrace : indices (capturePathMachine program initial) history = node.trace :=
    indices_ofTrace _ _ replay
  refine ⟨history, exactTrace, ?_⟩
  simpa only [exactTrace] using history_row_trace program initial history

end AuthoredHistories

def captureDomain (program : Program) (initialMachine : NativeMachine)
    (node : WorkState) : Prop :=
  WorkOccurrence.ValidFrom (capturePathMachine program initialMachine) initialMachine node

/-- Both returned and pending weighted contributions retain a replayable
history in the shared event category. The same history accounts for the ordered
coefficient and actual Need transition counter, including physical zero-weight contributions. This
is an executable semantic-machine statement, not a C-memory refinement. -/
theorem native_retained_history {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    ∃ history : Mettapedia.GSLT.Causality.OccurrenceMachineHistory.History
        (capturePathMachine program initial) initial
        (NeedWeightedResumption.retained leaf.1).state,
      Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
          (capturePathMachine program initial) history =
        (NeedWeightedResumption.retained leaf.1).trace ∧
      (NeedWeightedResumption.coefficientAccount (specification program)
        (edgeGrade clause) initial).of history = leaf.2 ∧
      (NeedWeightedResumption.retained leaf.1).state.work.transitions =
        initial.work.transitions +
          (Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
            (capturePathMachine program initial) history).length := by
  obtain ⟨history, trace, coefficient⟩ := NeedWeightedResumption.retained_history
    (specification program) (edgeGrade clause) initial fuel (WorkOccurrence.root initial) member
  have exactTrace : Mettapedia.GSLT.Causality.OccurrenceMachineHistory.indices
      (capturePathMachine program initial) history =
      (NeedWeightedResumption.retained leaf.1).trace := by
    simpa [WorkOccurrence.root] using trace
  refine ⟨history, exactTrace, coefficient, ?_⟩
  erw [exactTrace]
  exact native_retained_transition_cost program clause initial fuel member

/-- Every retained contribution is interpreted from an independently valid
row trace, and each recorded row has authored activation authority. This includes
a suspended body or a coefficient of zero. -/
theorem native_retained_provenance {V : Type} [Semiring V]
    (program : Program) (clause : WeighClause V Row)
    (initial : NativeMachine) (fuel : Nat)
    {leaf : (WorkState ⊕ WorkState) × V}
    (member : leaf ∈ WeightedBranchingResumption.contributions
      (source program clause) fuel (WorkOccurrence.root initial)) :
    ∃ choices : List Row,
      RowTrace program (NeedWeightedResumption.retained leaf.1).trace.length
        initial (NeedWeightedResumption.retained leaf.1).state choices ∧
      interpret clause choices = leaf.2 ∧
      ∀ row ∈ choices, ∃ (head : String) (arguments : List CellId),
        Activates program head arguments (.equation row.index)
          (.evaluate row.body row.environment) := by
  obtain ⟨history, trace, coefficient, _⟩ :=
    native_retained_history program clause initial fuel member
  have rows := history_row_trace program initial history
  erw [trace] at rows
  refine ⟨FreeMonoid.toList ((authoredRowAccount program initial).of history), rows, ?_, ?_⟩
  · exact (history_row_interpretation program clause initial history).trans coefficient
  · exact fun row member => row_trace_admitted program rows row member

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
def nestedValueOutcome {V Retained Work : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions ((WorkState ⊕ Retained) ⊕ Work) V) :
    Mettapedia.GSLT.Core.BoundedSelection.SelectOutcome :=
  WeightedBranchingResumption.nestedSelectionOutcome completedValue requested leaves

theorem native_nested_value_saturation_iff {V Job Grade : Type} (requested : Nat)
    (leaves : WeightedResumption.Contributions
      (WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState Job Grade ⊕
        WeightedBranchingResumption.NestedPendingState WorkState Job) V) :
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

/-- The stronger authored-evaluation invariant supplies the common caller
agreement used by phased coefficients and predicates. -/
theorem nested_capture_caller_agreement (program : Program) (annotation : Row → Option Atom)
    (body : WorkState) (score : Score) (parents : List Score)
    (valid : NestedCapturedCoefficient program annotation body score parents) :
    WeightedBranchingResumption.nestedCallerAgreement
      (fun body : WorkState => body.state) (fun held : Score => held.machine)
      (fun held : Score => held.origin.body) body score parents := by
  induction parents generalizing score with
  | nil => exact valid.2.2
  | cons parent rest ih => exact ⟨valid.2.2.1, ih parent valid.2.2.2⟩

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
def nestedInstructionAccounts : NestedWork → List Nat :=
  WeightedBranchingResumption.nestedStateAccounts
    (fun body : WorkState => body.state.work.transitions)
    (fun score : Score => score.machine.work.transitions)

theorem nested_instruction_accounts_sum (pending : NestedWork) :
    (nestedInstructionAccounts pending).sum = nestedInstructionCount pending :=
  WeightedBranchingResumption.nested_state_accounts_sum _ _ pending

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

section AuthoredPredicates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A binding-local coefficient and an optional predicate applied to its
returned value. The predicate is a native computation, not a Boolean oracle. -/
structure AuthoredClause where
  coefficient : Atom
  predicate : Option Atom := none

/-- The predicate phase retains the completed coefficient computation.
Its factor is attached only after the predicate returns true. -/
inductive AuthoredPhase where
  | coefficient
  | predicate (completedCoefficient : Score)

structure AuthoredJob where
  score : Score
  predicate : Option Atom
  phase : AuthoredPhase := .coefficient

def authoredJob {V : Type} [One V] (annotation : Row → Option AuthoredClause)
    (before after : NativeMachine) : V ⊕ AuthoredJob :=
  match NativeGradeAttachment.captureNext before after with
  | none => .inl 1
  | some capture =>
      match annotation capture.row with
      | none => .inl 1
      | some clause =>
          .inr ⟨capture.score clause.coefficient, clause.predicate, .coefficient⟩

/-- Only the two declared Boolean returns decide admission. -/
def predicateVerdict (score : Score) : Option Bool :=
  match scoreResult score with
  | some (.value (.symbol "True")) => some true
  | some (.value (.symbol "False")) => some false
  | _ => none

/-- Start the predicate in the coefficient's completed world, with the same
captured cells. Its instruction count includes the work already performed. -/
def beginPredicate (job : AuthoredJob) (predicate value : Atom) : AuthoredJob :=
  let expression := Atom.expression [predicate, value]
  { job with
    score := { job.score with
      expression := expression
      machine := { job.score.machine with
        control := .run (.evaluate expression job.score.origin.row.environment) [] } }
    phase := .predicate job.score }

/-- Both phases use actual Need steps. Equation annotations encountered in
either computation suspend the same owned parent stack. -/
def authoredGradeSource {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) :
    WeightedBranchingResumption.Coalgebra AuthoredJob AuthoredJob (V ⊕ AuthoredJob) :=
  fun job => if isHalted job.score.machine then
    match job.phase with
    | .coefficient =>
        match job.predicate, scoreResult job.score with
        | some predicate, some (.value value) =>
            .inr [(beginPredicate job predicate value, .inl 1)]
        | _, _ => .inl job
    | .predicate _ =>
        match predicateVerdict job.score with
        | some false => .inr []
        | _ => .inl job
  else
    .inr ((scoreStep program job.score).map fun next =>
      ({ job with score := next }, authoredJob annotation job.score.machine next.machine))

def authoredReadout {V : Type} (interpretation : Outcome → Option V)
    (job : AuthoredJob) : Option V :=
  match job.phase with
  | .coefficient =>
      match job.predicate with
      | none => coefficientReadout interpretation job.score
      | some _ => none
  | .predicate completed =>
      if predicateVerdict job.score = some true then coefficientReadout interpretation completed
      else none

def resumeAuthoredBody (body : WorkState) (job : AuthoredJob) : WorkState :=
  resumeCoefficient body job.score

def resumeAuthoredParent (parent child : AuthoredJob) : AuthoredJob :=
  { parent with score := resumeCoefficientScore parent.score child.score }

abbrev AuthoredWork :=
  WeightedBranchingResumption.NestedPendingState WorkState AuthoredJob

abbrev AuthoredResult :=
  WeightedBranchingResumption.NestedPendingAnswer WorkState WorkState AuthoredJob AuthoredJob

/-- Authored predicates instantiate the existing nested coefficient handler.
No body executes between the coefficient return and its admission decision. -/
def authoredSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra AuthoredWork AuthoredResult V :=
  WeightedBranchingResumption.nestedPendingSource
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent

/-- Every factor of the actual nested native source is either the unit or
an interpreted coefficient result. This includes coefficients produced while
executing another coefficient or its admission predicate. A scanner must
cover these results before using the corresponding factor law. -/
theorem authored_coefficients_satisfy {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (holds : V → Prop) (unit : holds 1)
    (interpreted : ∀ outcome value, interpretation outcome = some value → holds value) :
    WeightedBranchingResumption.CoefficientsSatisfy
      (authoredSource program annotation interpretation) holds := by
  have jobLaw : ∀ before after,
      Sum.elim holds (fun _ => True) (authoredJob annotation before after) := by
    intro before after
    cases captured : NativeGradeAttachment.captureNext before after with
    | none => simpa [authoredJob, captured] using unit
    | some capture =>
        cases annotated : annotation capture.row <;> simp [authoredJob, captured, annotated, unit]
  have readoutLaw : ∀ score value, coefficientReadout interpretation score = some value →
      holds value := by
    intro score value decoded
    simp only [coefficientReadout, Option.bind_eq_some_iff] at decoded
    obtain ⟨outcome, _, returned⟩ := decoded
    exact interpreted outcome value returned
  apply WeightedBranchingResumption.nested_coefficients_satisfy
    (holds := holds) (unit := unit)
  · exact NeedWeightedResumption.source_coefficients_satisfy
      (specification program) (authoredJob annotation) _ (fun before after _ => jobLaw before after)
  · intro job alternatives inspected next member
    unfold authoredGradeSource at inspected
    split at inspected
    · split at inspected
      · split at inspected
        · simp only [Sum.inr.injEq] at inspected
          subst alternatives
          obtain rfl := List.mem_singleton.mp member
          exact unit
        · cases inspected
      · split at inspected
        · cases inspected
          cases member
        · cases inspected
    · simp only [Sum.inr.injEq] at inspected
      subst alternatives
      obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp member
      exact jobLaw job.score.machine candidate.machine
  · intro job value decoded
    unfold authoredReadout at decoded
    split at decoded
    · split at decoded
      · exact readoutLaw _ value decoded
      · cases decoded
    · split at decoded
      · exact readoutLaw _ value decoded
      · cases decoded

@[simp] theorem authored_job_unannotated {V : Type} [One V]
    (before after : NativeMachine) :
    authoredJob (V := V) (fun _ => none) before after = .inl 1 := by
  cases inspected : NativeGradeAttachment.captureNext before after <;>
    simp [authoredJob, inspected]

theorem authored_unannotated_body_is_settled {V : Type} [One V] (program : Program) :
    NeedWeightedResumption.source (specification program)
      (authoredJob (V := V) (fun _ => none)) =
    WeightedBranchingResumption.settledBody
      (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V))) := by
  funext state
  cases control : state.state.control <;>
    simp only [NeedWeightedResumption.source, control,
      WeightedBranchingResumption.settledBody, NeedWeightedResumption.successors,
      List.map_map, authored_job_unannotated] <;> rfl

/-- The predicate extension creates no job or extra instruction for a plain
program. All ordered contributions and residual worlds agree at the same cut. -/
theorem native_authored_unannotated_exact {V : Type} [Monoid V] (program : Program)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : WorkState) :
    WeightedBranchingResumption.contributions
      (authoredSource program (fun _ => none) interpretation) fuel (.inl before) =
      (WeightedBranchingResumption.contributions
        (NeedWeightedResumption.source (specification program) (fun _ _ => (1 : V)))
        fuel before).map (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  unfold authoredSource
  rw [authored_unannotated_body_is_settled]
  exact WeightedBranchingResumption.nested_pending_settled_agrees _ _ _ _ _ _ _

theorem predicate_starts_in_completed_world (job : AuthoredJob) (predicate value : Atom) :
    (beginPredicate job predicate value).score.origin = job.score.origin ∧
    (beginPredicate job predicate value).score.machine.world = job.score.machine.world ∧
    (beginPredicate job predicate value).score.machine.work = job.score.machine.work ∧
    (beginPredicate job predicate value).score.machine.control =
      .run (.evaluate (.expression [predicate, value]) job.score.origin.row.environment) [] ∧
    (beginPredicate job predicate value).phase = .predicate job.score :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The completed coefficient is retained, rather than attached before the
predicate's own derivation factors or used to execute the body early. -/
theorem native_authored_starts_predicate {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob)
    (predicate value : Atom) (halted : isHalted job.score.machine = true)
    (phase : job.phase = .coefficient) (declared : job.predicate = some predicate)
    (returned : scoreResult job.score = some (.value value)) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inr [(.inr (body, beginPredicate job predicate value, parents), 1)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, halted, phase, declared, returned]

theorem native_authored_false_refuses {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob) (completed : Score)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (refused : predicateVerdict job.score = some false) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inr [] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, halted, phase, refused]

theorem native_authored_unknown_retains_stack {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (parents : List AuthoredJob) (completed : Score)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (unknown : predicateVerdict job.score = none) :
    authoredSource program annotation interpretation (.inr (body, job, parents)) =
      .inl (.inr (body, job, parents)) := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, unknown]

theorem native_authored_true_resumes_body {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job : AuthoredJob) (completed : Score) (value : V)
    (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (admitted : predicateVerdict job.score = some true)
    (decoded : coefficientReadout interpretation completed = some value) :
    authoredSource program annotation interpretation (.inr (body, job, [])) =
      .inr [(.inl (resumeAuthoredBody body job), value)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, admitted, decoded]

theorem native_authored_true_resumes_parent {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (body : WorkState) (job parent : AuthoredJob) (parents : List AuthoredJob)
    (completed : Score) (value : V) (halted : isHalted job.score.machine = true)
    (phase : job.phase = .predicate completed)
    (admitted : predicateVerdict job.score = some true)
    (decoded : coefficientReadout interpretation completed = some value) :
    authoredSource program annotation interpretation (.inr (body, job, parent :: parents)) =
      .inr [(.inr (body, resumeAuthoredParent parent job, parents), value)] := by
  simp [authoredSource, WeightedBranchingResumption.nestedPendingSource,
    authoredGradeSource, authoredReadout, halted, phase, admitted, decoded]

theorem authored_resume_preserves_parent (parent child : AuthoredJob) :
    (resumeAuthoredParent parent child).phase = parent.phase ∧
    (resumeAuthoredParent parent child).predicate = parent.predicate ∧
    (resumeAuthoredParent parent child).score.origin = parent.score.origin ∧
    (resumeAuthoredParent parent child).score.expression = parent.score.expression ∧
    (resumeAuthoredParent parent child).score.machine.control = parent.score.machine.control ∧
    (resumeAuthoredParent parent child).score.machine.world = child.score.machine.world ∧
    (resumeAuthoredParent parent child).score.machine.work =
      parent.score.machine.work.add child.score.machine.work :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Running a predicate or coefficient performs an actual reference-machine
instruction. The completed coefficient retained by its phase stays fixed. -/
theorem authored_running_uses_need {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job next : AuthoredJob)
    (edge : V ⊕ AuthoredJob) (running : isHalted job.score.machine = false)
    (member : (next, edge) ∈ (scoreStep program job.score).map (fun score =>
      ({ job with score := score }, authoredJob annotation job.score.machine score.machine))) :
    authoredGradeSource (V := V) program annotation job =
      .inr ((scoreStep program job.score).map fun score =>
        ({ job with score := score }, authoredJob annotation job.score.machine score.machine)) ∧
    next.score.machine ∈ NeedReference.step (specification program) job.score.machine ∧
    next.phase = job.phase ∧ next.predicate = job.predicate ∧
    next.score.origin = job.score.origin ∧ next.score.expression = job.score.expression ∧
    next.score.machine.work.transitions = job.score.machine.work.transitions + 1 := by
  obtain ⟨score, stepped, same⟩ := List.mem_map.mp member
  have nextEqual : { job with score := score } = next := (Prod.mk.inj same).1
  subst next
  obtain ⟨machine, actual, changed⟩ := (score_step_iff program job.score score).mp stepped
  obtain ⟨origin, expression, work⟩ := score_step_origin program job.score score stepped
  refine ⟨by simp [authoredGradeSource, running], ?_, rfl, rfl, origin, expression, work⟩
  simpa only [changed] using actual

/-- The native phased adapter has the same independently executed weighted
frontier interpretation as the common free handler. -/
theorem native_authored_handler_agrees {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (fuel : Nat) (before : AuthoredWork) :
    WeightedResumption.interpret WeightedBranchingResumption.catalogue
      (WeightedBranchingResumption.cut (authoredSource program annotation interpretation)
        fuel before) =
      WeightedBranchingResumption.contributions
        (authoredSource program annotation interpretation) fuel before :=
  WeightedBranchingResumption.interpret_cut _ _ _

/-- Split execution retains the predicate phase, its completed coefficient,
all suspended parents and the full ordered contribution product. -/
theorem native_authored_resume_exact {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V)
    (first second : Nat) (before : AuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) (first + second) before =
      WeightedResumption.sequence
        (WeightedBranchingResumption.contributions
          (authoredSource program annotation interpretation) first before)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : V))]
          | .inr pending => WeightedBranchingResumption.contributions
              (authoredSource program annotation interpretation) second pending) := by
  rw [WeightedBranchingResumption.contributions_add]
  apply congrArg (WeightedResumption.sequence
    (WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) first before))
  funext leaf
  cases leaf <;> rfl

end AuthoredPredicates

section AuthoredInstructionAccount

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem authored_job_capture {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    ∃ capture clause,
      NativeGradeAttachment.captureNext before after = some capture ∧
      annotation capture.row = some clause ∧
      job = ⟨capture.score clause.coefficient, clause.predicate, .coefficient⟩ := by
  cases captured : NativeGradeAttachment.captureNext before after with
  | none => simp [authoredJob, captured] at chosen
  | some capture =>
      cases authored : annotation capture.row with
      | none => simp [authoredJob, captured, authored] at chosen
      | some clause =>
          simp only [authoredJob, captured, authored, Sum.inr.injEq] at chosen
          exact ⟨capture, clause, rfl, authored, chosen.symm⟩

theorem authored_job_starts_at_zero {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    job.score.machine.work.transitions = 0 := by
  obtain ⟨_, _, _, _, rfl⟩ := authored_job_capture annotation before after job chosen
  rfl

theorem authored_job_owns_actual_body {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob)
    (chosen : authoredJob (V := V) annotation before after = .inr job) :
    job.score.origin.body = after := by
  obtain ⟨capture, _, captured, _, rfl⟩ :=
    authored_job_capture annotation before after job chosen
  exact (NativeGradeAttachment.captured_next_exact before after capture captured).1

theorem authored_grade_return_same_job {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job result : AuthoredJob)
    (returned : authoredGradeSource (V := V) program annotation job = .inl result) :
    result = job := by
  unfold authoredGradeSource at returned
  split at returned
  · split at returned
    · split at returned <;> simp_all
    · split at returned <;> simp_all
  · simp at returned

/-- The actual Need instruction account of one retained contribution.
It is distinct from cumulative whole-search or runtime-event receipts. -/
def authoredInstructionCount : AuthoredWork → Nat :=
  WeightedBranchingResumption.nestedStateMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

def authoredResultInstructionCount : AuthoredResult → Nat :=
  WeightedBranchingResumption.nestedAnswerMeter
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

/-- Read the owned accounts only when requested. The completed coefficient
retained by a predicate phase is not a second active work account. -/
def authoredInstructionAccounts : AuthoredWork → List Nat :=
  WeightedBranchingResumption.nestedStateAccounts
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)

theorem authored_instruction_accounts_sum (pending : AuthoredWork) :
    (authoredInstructionAccounts pending).sum = authoredInstructionCount pending :=
  WeightedBranchingResumption.nested_state_accounts_sum _ _ pending

theorem authored_predicate_phase_adds_no_instruction (body : WorkState) (job : AuthoredJob)
    (parents : List AuthoredJob) (predicate value : Atom) :
    authoredInstructionCount (.inr (body, beginPredicate job predicate value, parents)) =
      authoredInstructionCount (.inr (body, job, parents)) := rfl

theorem authored_grade_return_keeps_account {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job result : AuthoredJob)
    (returned : authoredGradeSource (V := V) program annotation job = .inl result) :
    result.score.machine.work.transitions = job.score.machine.work.transitions :=
  congrArg (fun held : AuthoredJob => held.score.machine.work.transitions)
    (authored_grade_return_same_job program annotation job result returned)

theorem authored_grade_step_bounds {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job : AuthoredJob)
    (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    job.score.machine.work.transitions ≤ next.1.score.machine.work.transitions ∧
    next.1.score.machine.work.transitions ≤ job.score.machine.work.transitions + 1 ∧
    Sum.elim (fun _ => True) (fun child => child.score.machine.work.transitions = 0)
      next.2 := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        simp [beginPredicate]
      · simp at requested
    · split at requested <;> simp_all
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    have spent := (score_step_origin program job.score score actual).2.2
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
    cases chosen : authoredJob (V := V) annotation job.score.machine score.machine with
    | inl value => trivial
    | inr inner =>
        exact authored_job_starts_at_zero (V := V) annotation job.score.machine
          score.machine inner chosen

/-- Every retained or returned contribution accounts for its coefficient,
predicate and suspended parents once. Phase changes may be administrative;
actual instructions never decrease and are bounded by the source allowance. -/
theorem native_authored_instruction_bounds {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel before,
      authoredInstructionCount before ≤
        Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1 ∧
      Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1 ≤
        authoredInstructionCount before + fuel := by
  unfold authoredSource authoredInstructionCount authoredResultInstructionCount
  apply WeightedBranchingResumption.nested_contributions_meter_bounds_le
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state.work.transitions)
    (fun body : WorkState => body.state.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    (fun job : AuthoredJob => job.score.machine.work.transitions)
    ?_ ?_ ?_ ?_ ?_ ?_ fuel before
  · intro body answer returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (authoredJob annotation) body answer).mp returned
    rfl
  · intro body alternatives requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    have spent : child.state.work.transitions = body.state.work.transitions + 1 :=
      step_increments_transition (specification program) _ _ (List.mem_of_getElem? actual)
    refine ⟨?_, spent.le, ?_⟩
    · change body.state.work.transitions ≤ child.state.work.transitions
      omega
    cases coefficient with
    | inl value => trivial
    | inr job =>
        exact authored_job_starts_at_zero (V := V) annotation body.state child.state
          job caused.symm
  · exact authored_grade_return_keeps_account program annotation
  · exact authored_grade_step_bounds program annotation
  · intro body result
    rfl
  · intro parent result
    rfl

end AuthoredInstructionAccount

section AuthoredCallerAgreement

/-- Every child captures the actual suspended caller, including its complete
world and control. This view does not identify or merge occurrences. -/
def authoredCallerAgreement : AuthoredWork → Prop :=
  WeightedBranchingResumption.nestedWorkCallerAgreement
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)

def authoredResultCallerAgreement : AuthoredResult → Prop :=
  WeightedBranchingResumption.nestedResultCallerAgreement
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)

theorem authored_grade_steps_keep_caller {V : Type} [One V] (program : Program)
    (annotation : Row → Option AuthoredClause) (job : AuthoredJob)
    (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    next.1.score.origin.body = job.score.origin.body ∧
    Sum.elim (fun _ => True)
      (fun child => child.score.origin.body = next.1.score.machine) next.2 := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        simp [beginPredicate]
      · simp at requested
    · split at requested <;> simp_all
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    refine ⟨congrArg Captured.body (score_step_origin program job.score score actual).1, ?_⟩
    cases chosen : authoredJob (V := V) annotation job.score.machine score.machine with
    | inl value => trivial
    | inr inner =>
        exact authored_job_owns_actual_body (V := V) annotation job.score.machine
          score.machine inner chosen

/-- The actual authored adapter preserves caller agreement through phase
changes, nested Need instructions and child returns. Unknown readouts retain
it in the parked result; no normalization or successful readout is assumed. -/
theorem native_authored_caller_agreement {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork)
    (valid : authoredCallerAgreement before) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel before,
      Sum.elim authoredResultCallerAgreement authoredCallerAgreement leaf.1 := by
  unfold authoredSource authoredCallerAgreement authoredResultCallerAgreement at *
  apply WeightedBranchingResumption.nested_contributions_caller_agreement
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state)
    (fun job : AuthoredJob => job.score.machine)
    (fun job : AuthoredJob => job.score.origin.body)
    ?_ ?_ ?_ ?_ fuel before valid
  · intro body alternatives requested next member job chosen
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, _, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    exact authored_job_owns_actual_body (V := V) annotation body.state child.state job
      (caused.symm.trans chosen)
  · intro job result returned
    exact congrArg (fun held : AuthoredJob => held.score.origin.body)
      (authored_grade_return_same_job program annotation job result returned)
  · exact authored_grade_steps_keep_caller program annotation
  · intro parent result
    rfl

theorem native_authored_root_caller_agreement {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (body : WorkState) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel (.inl body),
      Sum.elim authoredResultCallerAgreement authoredCallerAgreement leaf.1 :=
  native_authored_caller_agreement program annotation interpretation fuel (.inl body) True.intro

end AuthoredCallerAgreement

/-! ## Stateful agendas and recordings of authored coefficient computations -/

section ScheduledAuthored

open Mettapedia.GSLT.Core.BranchingTemporal

/-- The common scheduler executes the actual nested coefficient and predicate
source. Parked results retain their distinct `AuthoredResult` tag; an emitted
parked disposition is not a successful body answer. -/
def authoredSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (AuthoredWork × V) (AuthoredResult × V) :=
  WeightedBranchingResumption.Scheduled.system (authoredSource program annotation interpretation)

/-- Actual nested coefficient and predicate computations use the common finite
source certificate. Completed controllers retain the entire result bag,
including parked dispositions and duplicate occurrences. No termination claim
about other programs, equality of prefixes, or equality of host costs follows. -/
theorem authored_completed_controllers_agree {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (depth : Nat)
    {FirstMemory SecondMemory : Type*}
    (first : Controller (AuthoredWork × V) (AuthoredResult × V) FirstMemory)
    (second : Controller (AuthoredWork × V) (AuthoredResult × V) SecondMemory)
    (roots : List (AuthoredWork × V))
    (certified : ∀ root ∈ roots, Mettapedia.GSLT.Core.FiniteSearchCertificate.Certified
      (authoredSystem program annotation interpretation) depth root)
    (firstFuel secondFuel : Nat)
    (firstClosed : (Snapshot.run (authoredSystem program annotation interpretation)
      first firstFuel (Snapshot.initial first roots)).search.frontier = [])
    (secondClosed : (Snapshot.run (authoredSystem program annotation interpretation)
      second secondFuel (Snapshot.initial second roots)).search.frontier = []) :
    eventBag (Snapshot.run (authoredSystem program annotation interpretation)
        first firstFuel (Snapshot.initial first roots)).search.events =
      eventBag (Snapshot.run (authoredSystem program annotation interpretation)
        second secondFuel (Snapshot.initial second roots)).search.events :=
  Mettapedia.GSLT.Core.FiniteSearchCertificate.completed_controllers_agree
    (authoredSystem program annotation interpretation) depth first second roots certified
    firstFuel secondFuel firstClosed secondClosed

/-- A superior multiplication supplies one sufficient stopping law for the
actual nested coefficient/predicate machine. The source continues to retain
zero, duplicate and uninterpreted occurrences. -/
theorem authored_coefficient_realized {V : Type} [Monoid V] [Preorder V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V)
    (superior : Mettapedia.GSLT.Core.WeightOrderedSelection.Superior V)
    (combines : ∀ left right, superior.combine left right = left * right) :
    Mettapedia.GSLT.Core.WeightOrderedSelection.Realized
      (authoredSystem program annotation interpretation) superior Prod.snd :=
  WeightedBranchingResumption.Scheduled.system_realized
    (authoredSource program annotation interpretation) superior combines

/-- The actual nested native machine supports descending product bounds on
all nonnegative carried values. Only factors produced by the interpretation
must be at most one; the starting coefficient has no upper bound. -/
theorem authored_product_step_bound {R : Type} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option R)
    (factors : ∀ outcome value, interpretation outcome = some value →
      0 ≤ value ∧ value ≤ 1) :
    Mettapedia.GSLT.Core.WeightOrderedSelection.StepBound
      (authoredSystem program annotation interpretation)
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) :=
  WeightedBranchingResumption.Scheduled.product_stepBound _
    (authored_coefficients_satisfy program annotation interpretation _
      ⟨zero_le_one, le_rfl⟩ factors)

/-- A stateful native agenda may certify a selected batch against its full
residual using a one-sided law on a preserved coefficient domain. The
captured source/interpretation are fixed; both the runnable frontier and
retained unaccepted results need bounds. This does not provide a missing
interpretation for a parked coefficient or a requested batch size. -/
theorem authored_early_stop_selects_best {V W : Type} [Monoid V] [Preorder W]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V)
    (weight : V → W) (domain : V → Prop)
    (law : Mettapedia.GSLT.Core.WeightOrderedSelection.StepBound
      (authoredSystem program annotation interpretation)
      (fun node => weight node.2) (fun node => domain node.2))
    {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.frontier, domain item.2) {bound : W}
    (accepted : Emission (AuthoredWork × V) (AuthoredResult × V) → Prop)
    (frontierBound : ∀ item ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.frontier, bound ≤ weight item.2)
    (retainedBound : ∀ event ∈
      (Snapshot.run (authoredSystem program annotation interpretation)
        controller fuel snapshot).search.events,
      ¬ accepted event → bound ≤ weight event.origin.2)
    {selections : List (AuthoredWork × V)}
    (selectedBound : ∀ chosen ∈ selections, weight chosen.2 ≤ bound)
    {node : AuthoredWork × V} {answer : AuthoredResult × V}
    (generated : Generated (authoredSystem program annotation interpretation)
      snapshot.search.frontier node)
    (emits : (authoredSystem program annotation interpretation).emit node = some answer)
    (unaccepted : ¬ accepted ⟨node, answer⟩) :
    ∀ chosen ∈ selections, weight chosen.2 ≤ weight node.2 :=
  Mettapedia.GSLT.Core.WeightOrderedSelection.Controlled.early_stop_selects_best
    (authoredSystem program annotation interpretation)
    (fun node => weight node.2) (fun node => domain node.2) law
    controller snapshot fuel frontierDomain accepted frontierBound retainedBound selectedBound
    generated emits unaccepted

/-- The actual native snapshot cannot establish answer shortage while a
coefficient/predicate result still owns a parked caller and parent stack. -/
theorem authored_saturation_iff {V Selected Memory : Type*}
    (select : WorkState → Option Selected) (requested : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) Memory) :
    WeightedBranchingResumption.nestedSelectionOutcome select requested
      (WeightedBranchingResumption.Scheduled.observeSnapshot snapshot.search) = .saturated ↔
      (WeightedBranchingResumption.nestedSelected select
        (WeightedBranchingResumption.Scheduled.observeSnapshot snapshot.search)).length < requested ∧
      (snapshot.search.events.filterMap (fun event => match event.value.1 with
        | .inl _ => none
        | .inr parked => some (parked, event.value.2))) = [] ∧
      snapshot.search.frontier = [] := by
  convert WeightedBranchingResumption.Scheduled.nested_saturated_iff
    select requested snapshot.search using 1
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  apply Iff.of_eq
  apply congrArg (fun values => values = [])
  apply congrArg (fun read => snapshot.search.events.filterMap read)
  funext event
  cases event.value.1 <;> rfl

/-- Arbitrary lawful agendas preserve the actual caller/world agreement in
every live instruction, nested parent frame and emitted parked result. The
proof passes through the independently defined weighted source cuts. -/
theorem native_authored_scheduled_callers {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (body : WorkState) (fuel : Nat) :
    let run := Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredSystem program annotation interpretation) controller fuel
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
    (∀ node ∈ run.search.frontier, authoredCallerAgreement node.1) ∧
      (∀ event ∈ run.search.events, authoredResultCallerAgreement event.value.1) := by
  have sound := Mettapedia.GSLT.Core.InferenceControl.Snapshot.sound_run
    (authoredSystem program annotation interpretation) controller
    (snapshot := Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
      controller [(.inl body, 1)])
    (initial_sound (authoredSystem program annotation interpretation) [(.inl body, 1)]) fuel
  constructor
  · intro node member
    obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.generated_pending
      (authoredSource program annotation interpretation) (.inl body) (sound.1 node member)
    exact native_authored_root_caller_agreement program annotation interpretation
      depth body _ present
  · intro event member
    obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.event_contribution
      (authoredSource program annotation interpretation) (.inl body) (sound.2 event member)
    exact native_authored_root_caller_agreement program annotation interpretation
      depth body _ present

/-- Enabling or truncating a recording preserves the complete weighted
snapshot, including coefficients, pending predicates and nested callers. -/
theorem authored_recording_erasure {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory Event : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (observe : Memory → (AuthoredWork × V) → Option (AuthoredResult × V) →
      List (AuthoredWork × V) → Event)
    (capacity : Option Nat) (fuel : Nat)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (AuthoredWork × V) (AuthoredResult × V) (Memory × Option (Recording.Prefix Event))) :
    Recording.erase (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredSystem program annotation interpretation)
      (Recording.controller controller observe capacity) fuel snapshot) =
      Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredSystem program annotation interpretation) controller fuel
        (Recording.erase snapshot) :=
  Recording.run_erasure _ _ _ _ _ _

/-- Retained graph nodes inherit the source's caller agreement even when the
recording omits later work. No completeness claim follows from this fact. -/
theorem recorded_authored_caller_agrees {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (AuthoredWork × V) (AuthoredResult × V) Memory)
    (body : WorkState) (capacity fuel : Nat)
    (record : Recording.Prefix (AuthoredWork × V))
    (retained : (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredSystem program annotation interpretation)
      (Recording.controller controller (fun _ selected _ _ => selected) (some capacity)) fuel
      (Recording.start
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
        (some capacity))).memory.2 = some record)
    {node : AuthoredWork × V} (member : node ∈ record.items) :
    authoredCallerAgreement node.1 := by
  have generated := Recording.retained_node_generated
    (authoredSystem program annotation interpretation) controller capacity fuel
    (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller [(.inl body, 1)])
    [(.inl body, 1)] (initial_sound _ _) record retained member
  obtain ⟨depth, present⟩ := WeightedBranchingResumption.Scheduled.generated_pending
    (authoredSource program annotation interpretation) (.inl body) generated
  exact native_authored_root_caller_agreement program annotation interpretation
    depth body _ present

/-- Successor positions cover the complete authored source, including nested
coefficient and predicate phases. The inner Need receipt histories remain
part of the source states rather than being replaced by this decoration. -/
def authoredOccurrenceSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) :=
  WorkOccurrence.system (WeightedBranchingResumption.Scheduled.pathMachine
    (authoredSource program annotation interpretation))

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory

/-- With the source, coefficient interpretation and initial world fixed, a
retained occurrence replays to the same full nested state. Its coefficient
is the ordered account of actual selected source alternatives, including
zero factors. This does not authorize repeating external service effects. -/
theorem recorded_authored_weighted_history {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (body : WorkState) (capacity fuel : Nat)
    (record : Recording.Prefix (WorkOccurrence (AuthoredWork × V)))
    (retained : (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredOccurrenceSystem program annotation interpretation)
      (Recording.controller controller (fun _ selected _ _ => selected) (some capacity)) fuel
      (Recording.start
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial controller
          [WorkOccurrence.root (.inl body, 1)]) (some capacity))).memory.2 = some record)
    {node : WorkOccurrence (AuthoredWork × V)} (member : node ∈ record.items) :
    let source := authoredSource program annotation interpretation
    let machine := WeightedBranchingResumption.Scheduled.pathMachine source
    ∃ history : History machine (.inl body, 1) node.state,
      indices machine history = node.trace ∧
      node.state.2 = (eventAccount machine (fun before _ index =>
        WeightedBranchingResumption.Scheduled.edgeCoefficient source before.1 index)).of history := by
  let source := authoredSource program annotation interpretation
  let machine := WeightedBranchingResumption.Scheduled.pathMachine source
  have replayed := Recording.retained_occurrence_replays machine controller
    (.inl body, 1) capacity fuel record retained member
  let history := ofTrace machine node.trace replayed
  refine ⟨history, indices_ofTrace machine node.trace replayed, ?_⟩
  simpa only [one_mul] using
    WeightedBranchingResumption.Scheduled.history_coefficient source history

/-- Complete recorded expansions replay the actual nested native source,
including pending coefficient/predicate jobs and their captured callers.
The executable checker requires equality procedures for the retained states,
results and coefficient representation. This does not assert decidability for
arbitrary mathematical coefficients or authorize external-service replay. -/
theorem authored_recorded_replay {V : Type} [Monoid V] [DecidableEq V]
    [DecidableEq AuthoredWork] [DecidableEq AuthoredResult]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) Memory)
    (capacity fuel : Nat)
    (fits : (Recording.stream (authoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel snapshot).length ≤ capacity) :
    ((Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (authoredOccurrenceSystem program annotation interpretation)
      (Recording.controller controller Recording.Replay.observe (some capacity)) fuel
      (Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => Recording.Replay.readout
          (authoredOccurrenceSystem program annotation interpretation) controller record snapshot) =
      some (.ok (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredOccurrenceSystem program annotation interpretation) controller fuel snapshot)) :=
  Recording.Replay.recorded_replay _ _ _ _ _ fits

/-- A rejected native replay preserves the full nested checkpoint and the
entire suffix. Its accepted prefix consists of actual source expansions. -/
theorem authored_replay_refusal {V : Type} [Monoid V] [DecidableEq V]
    [DecidableEq AuthoredWork] [DecidableEq AuthoredResult]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat) Memory)
    (frames pending : List (Preparation.Capture (WorkOccurrence (AuthoredWork × V))
      ((AuthoredResult × V) × List Nat)))
    (snapshot cut : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (AuthoredWork × V)) ((AuthoredResult × V) × List Nat) Memory)
    (refused : Recording.Replay.run (authoredOccurrenceSystem program annotation interpretation)
      controller frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (authoredOccurrenceSystem program annotation interpretation) controller
        acceptedFrames.length snapshot ∧
      Recording.Replay.step? (authoredOccurrenceSystem program annotation interpretation)
        controller cut frame = none :=
  Recording.Replay.run_refused _ _ _ _ _ _ refused

end ScheduledAuthored

/-! ## Lawful changes of native coefficients

The coefficient interpretation can change through a monoid homomorphism while
retaining the complete native states, owned grade jobs, caller frames, physical
contribution order and finite cut. The authored adapter also retains its
coefficient/predicate phase and the original predicate verdict.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem coefficient_job_change {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (annotation : Row → Option Atom)
    (before after : NativeMachine) :
    coefficientJob (V := W) annotation before after =
      Sum.map change id (coefficientJob (V := V) annotation before after) := by
  cases capture : NativeGradeAttachment.captureNext before after with
  | none => simp [coefficientJob, capture]
  | some captured =>
      cases attached : annotation captured.row <;> simp [coefficientJob, capture, attached]

theorem coefficient_readout_change {V W : Type}
    (change : V → W) (interpretation : Outcome → Option V) (score : Score) :
    coefficientReadout (fun outcome => (interpretation outcome).map change) score =
      (coefficientReadout interpretation score).map change := by
  simp [coefficientReadout, Option.map_bind]

/-- Coefficient changes preserve the actual next native instruction, including
its captured body, score world and parent grade frames. -/
theorem native_nested_source_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (pending : NestedWork) :
    nestedSource program annotation (fun outcome => (interpretation outcome).map change) pending =
      match nestedSource program annotation interpretation pending with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (WeightedResumption.mapCoefficients change alternatives) := by
  unfold nestedSource
  convert WeightedBranchingResumption.nested_pending_change_coefficients
    (State := WorkState) (Answer := WorkState) (Job := Score) (Grade := Score)
    change
    (NeedWeightedResumption.source (specification program) (coefficientJob (V := V) annotation))
    (NeedWeightedResumption.source (specification program) (coefficientJob (V := W) annotation))
    (gradedCoefficientSource (V := V) program annotation)
    (gradedCoefficientSource (V := W) program annotation) ?_ ?_
    (coefficientReadout interpretation)
    (coefficientReadout (fun outcome => (interpretation outcome).map change)) ?_
    resumeCoefficient resumeCoefficientScore pending using 1
  · cases inspected : WeightedBranchingResumption.nestedPendingSource
      (NeedWeightedResumption.source (specification program) (coefficientJob (V := V) annotation))
      (gradedCoefficientSource (V := V) program annotation) (coefficientReadout interpretation)
      resumeCoefficient resumeCoefficientScore pending <;> rfl
  · intro body
    cases control : body.state.control <;>
      simp [NeedWeightedResumption.source, NeedWeightedResumption.successors,
        control, List.map_map, coefficient_job_change change]
  · intro score
    by_cases halted : isHalted score.machine
    · simp [gradedCoefficientSource, halted]
    · simp [gradedCoefficientSource, halted, List.map_map, coefficient_job_change change]
  · exact coefficient_readout_change change interpretation

theorem native_nested_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedSource program annotation (fun outcome => (interpretation outcome).map change))
      fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (nestedSource program annotation interpretation) fuel before) := by
  apply WeightedBranchingResumption.contributions_change_coefficients change _ _ ?_ fuel before
  intro pending
  convert native_nested_source_change_coefficients change program annotation interpretation pending
    using 1
  cases inspected : nestedSource program annotation interpretation pending <;> rfl

/-- A declared grade guard commutes with a coefficient change only under its
separate admission law. The comparison retains whole native residuals. -/
theorem native_nested_admitted_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option Atom)
    (interpretation : Outcome → Option V) (admitSource : V → Bool) (admitTarget : W → Bool)
    (admits : ∀ value, admitTarget (change value) = admitSource value)
    (fuel : Nat) (before : NestedWork) :
    WeightedBranchingResumption.contributions
      (nestedAdmittedSource program annotation
        (fun outcome => (interpretation outcome).map change) admitTarget) fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (nestedAdmittedSource program annotation interpretation admitSource) fuel before) := by
  apply WeightedBranchingResumption.admitting_at_contributions_change_coefficients
    change _ _ ?_ _ admitSource admitTarget admits fuel before
  intro pending
  convert native_nested_source_change_coefficients change program annotation interpretation pending
    using 1
  cases inspected : nestedSource program annotation interpretation pending <;> rfl

theorem authored_job_change {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (annotation : Row → Option AuthoredClause)
    (before after : NativeMachine) :
    authoredJob (V := W) annotation before after =
      Sum.map change id (authoredJob (V := V) annotation before after) := by
  cases capture : NativeGradeAttachment.captureNext before after with
  | none => simp [authoredJob, capture]
  | some captured =>
      cases attached : annotation captured.row <;> simp [authoredJob, capture, attached]

theorem authored_readout_change {V W : Type}
    (change : V → W) (interpretation : Outcome → Option V) (job : AuthoredJob) :
    authoredReadout (fun outcome => (interpretation outcome).map change) job =
      (authoredReadout interpretation job).map change := by
  cases phase : job.phase with
  | coefficient =>
      cases predicate : job.predicate <;>
        simp [authoredReadout, phase, predicate, coefficient_readout_change]
  | predicate completed =>
      by_cases verdict : predicateVerdict job.score = some true <;>
        simp [authoredReadout, phase, verdict, coefficient_readout_change]

theorem native_authored_change_coefficients {V W : Type} [Monoid V] [Monoid W]
    (change : V →* W) (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (before : AuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation (fun outcome => (interpretation outcome).map change))
      fuel before =
    WeightedResumption.mapCoefficients change
      (WeightedBranchingResumption.contributions
        (authoredSource program annotation interpretation) fuel before) := by
  apply WeightedBranchingResumption.contributions_change_coefficients
    change _ _ ?_ fuel before
  intro pending
  unfold authoredSource
  convert WeightedBranchingResumption.nested_pending_change_coefficients
    (State := WorkState) (Answer := WorkState) (Job := AuthoredJob) (Grade := AuthoredJob)
    change
    (NeedWeightedResumption.source (specification program) (authoredJob (V := V) annotation))
    (NeedWeightedResumption.source (specification program) (authoredJob (V := W) annotation))
    (authoredGradeSource (V := V) program annotation)
    (authoredGradeSource (V := W) program annotation) ?_ ?_
    (authoredReadout interpretation)
    (authoredReadout (fun outcome => (interpretation outcome).map change)) ?_
    resumeAuthoredBody resumeAuthoredParent pending using 1
  · cases inspected : WeightedBranchingResumption.nestedPendingSource
      (NeedWeightedResumption.source (specification program) (authoredJob (V := V) annotation))
      (authoredGradeSource (V := V) program annotation) (authoredReadout interpretation)
      resumeAuthoredBody resumeAuthoredParent pending <;> rfl
  · intro body
    cases control : body.state.control <;>
      simp [NeedWeightedResumption.source, NeedWeightedResumption.successors,
        control, List.map_map, authored_job_change change]
  · intro job
    unfold authoredGradeSource
    by_cases halted : isHalted job.score.machine
    · simp only [halted, ↓reduceIte]
      cases phase : job.phase with
      | coefficient =>
          simp only []
          split <;> simp [map_one]
      | predicate completed =>
          simp only []
          split <;> simp
    · simp [halted, List.map_map, authored_job_change change]
  · exact authored_readout_change change interpretation


/-! ## Recorded heaps through authored coefficient continuations -/

namespace AuthoredPhase

def Recorded : AuthoredPhase → Prop
  | .coefficient => True
  | .predicate completed => completed.Recorded

end AuthoredPhase

namespace AuthoredJob

def Recorded (job : AuthoredJob) : Prop := job.score.Recorded ∧ job.phase.Recorded

end AuthoredJob

def authoredHeapsRecorded : AuthoredWork → Prop :=
  WeightedBranchingResumption.nestedWorkHolds
    (fun body : WorkState => body.state.world.heap.Recorded) AuthoredJob.Recorded

def authoredResultHeapsRecorded : AuthoredResult → Prop :=
  WeightedBranchingResumption.nestedResultHolds
    (fun body : WorkState => body.state.world.heap.Recorded)
    (fun body : WorkState => body.state.world.heap.Recorded)
    AuthoredJob.Recorded AuthoredJob.Recorded

theorem authored_job_recorded {V : Type} [One V]
    (annotation : Row → Option AuthoredClause) (before after : NativeMachine)
    (job : AuthoredJob) (valid : after.world.heap.Recorded)
    (chosen : authoredJob (V := V) annotation before after = .inr job) : job.Recorded := by
  obtain ⟨capture, clause, captured, _, rfl⟩ :=
    authored_job_capture annotation before after job chosen
  have body := (NativeGradeAttachment.captured_next_exact before after capture captured).1
  have capturedHeap := congrArg (fun machine : NativeMachine => machine.world.heap) body
  have originValid : capture.Recorded := by
    change capture.world.heap.Recorded
    change capture.world.heap = after.world.heap at capturedHeap
    rw [capturedHeap]
    exact valid
  exact ⟨Captured.score_recorded capture clause.coefficient originValid, True.intro⟩

theorem begin_predicate_recorded (job : AuthoredJob) (predicate value : Atom)
    (valid : job.Recorded) : (beginPredicate job predicate value).Recorded :=
  ⟨⟨valid.1.1, valid.1.2⟩, valid.1⟩

theorem resume_authored_body_recorded (body : WorkState) (job : AuthoredJob)
    (valid : job.Recorded) : (resumeAuthoredBody body job).state.world.heap.Recorded := valid.1.2

theorem resume_authored_parent_recorded (parent child : AuthoredJob)
    (parentValid : parent.Recorded) (childValid : child.Recorded) :
    (resumeAuthoredParent parent child).Recorded :=
  ⟨⟨parentValid.1.1, childValid.1.2⟩, parentValid.2⟩

theorem authored_grade_steps_recorded {V : Type} [One V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (job : AuthoredJob) (alternatives : List (AuthoredJob × (V ⊕ AuthoredJob)))
    (valid : job.Recorded)
    (requested : authoredGradeSource program annotation job = .inr alternatives)
    (next : AuthoredJob × (V ⊕ AuthoredJob)) (member : next ∈ alternatives) :
    next.1.Recorded ∧ ∀ child, next.2 = .inr child → child.Recorded := by
  unfold authoredGradeSource at requested
  split at requested
  · split at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        obtain rfl := List.mem_singleton.mp member
        exact ⟨begin_predicate_recorded _ _ _ valid, by intro child impossible; contradiction⟩
      · simp at requested
    · split at requested
      · simp only [Sum.inr.injEq] at requested
        subst alternatives
        simp at member
      · simp at requested
  · simp only [Sum.inr.injEq] at requested
    subst alternatives
    obtain ⟨score, actual, rfl⟩ := List.mem_map.mp member
    have scoreValid := score_step_recorded program job.score score valid.1 actual
    refine ⟨⟨scoreValid, valid.2⟩, ?_⟩
    intro child chosen
    exact authored_job_recorded annotation job.score.machine score.machine child scoreValid.2 chosen

/-- Every actual transition preserves all live, captured and suspended heaps.
The generic nested-handler rule supplies stack preservation; actual Need
instructions and captured-row construction discharge its native premises. -/
theorem authored_source_recorded {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) :
    (∀ work result, authoredHeapsRecorded work →
      authoredSource program annotation interpretation work = .inl result →
      authoredResultHeapsRecorded result) ∧
    (∀ work alternatives, authoredHeapsRecorded work →
      authoredSource program annotation interpretation work = .inr alternatives →
      ∀ next ∈ alternatives, authoredHeapsRecorded next.1) := by
  apply WeightedBranchingResumption.nested_source_preserves
    (NeedWeightedResumption.source (specification program) (authoredJob annotation))
    (authoredGradeSource program annotation) (authoredReadout interpretation)
    resumeAuthoredBody resumeAuthoredParent
    (fun body : WorkState => body.state.world.heap.Recorded)
    (fun body : WorkState => body.state.world.heap.Recorded)
    AuthoredJob.Recorded AuthoredJob.Recorded
  · intro body answer inherited returned
    obtain ⟨rfl, _⟩ := (NeedWeightedResumption.source_return_iff
      (specification program) (authoredJob annotation) body answer).mp returned
    exact inherited
  · intro body alternatives inherited requested next member
    rcases next with ⟨child, coefficient⟩
    have located : (child, coefficient) ∈ NeedWeightedResumption.successors
        (specification program) (authoredJob annotation) body := by
      cases control : body.state.control <;>
        simp_all only [NeedWeightedResumption.source, Sum.inl_ne_inr, Sum.inr.injEq]
    obtain ⟨_, actual, _, caused⟩ := (NeedWeightedResumption.successor_iff
      (specification program) (authoredJob annotation) body child coefficient).mp located
    have childValid := NeedReference.step_heap_recorded (specification program) _ _
      inherited (List.mem_of_getElem? actual)
    refine ⟨childValid, ?_⟩
    intro job chosen
    exact authored_job_recorded annotation body.state child.state job childValid
      (caused.symm.trans chosen)
  · intro job result inherited returned
    rw [authored_grade_return_same_job program annotation job result returned]
    exact inherited
  · exact authored_grade_steps_recorded program annotation
  · intro body job _ valid
    exact resume_authored_body_recorded body job valid
  · exact resume_authored_parent_recorded

theorem authored_contributions_recorded {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (work : AuthoredWork)
    (valid : authoredHeapsRecorded work) :
    ∀ leaf ∈ WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel work,
      Sum.elim authoredResultHeapsRecorded authoredHeapsRecorded leaf.1 := by
  obtain ⟨returns, successors⟩ := authored_source_recorded program annotation interpretation
  exact WeightedBranchingResumption.contributions_invariant _ _ _
    returns successors fuel work valid

theorem authored_root_recorded (term : Atom) :
    authoredHeapsRecorded (.inl (WorkOccurrence.root (initial term))) :=
  initial_heap_recorded term


namespace AuthoredPhase

abbrev RecordedView := Option Score.RecordedView

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Option Score.RecordedView))

def recordedView : AuthoredPhase → RecordedView
  | .coefficient => none
  | .predicate completed => some completed.recordedView

def ofRecordedView : RecordedView → AuthoredPhase
  | none => .coefficient
  | some completed => .predicate (Score.ofRecordedView completed)

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded := by
  cases view with
  | none => trivial
  | some completed => exact Score.ofRecordedView_recorded completed

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := by cases view <;> rfl

theorem ofRecordedView_recordedView (phase : AuthoredPhase) (valid : phase.Recorded) :
    ofRecordedView phase.recordedView = phase := by
  cases phase with
  | coefficient => rfl
  | predicate completed =>
      change AuthoredPhase.predicate (Score.ofRecordedView completed.recordedView) = _
      rw [Score.ofRecordedView_recordedView completed valid]

end AuthoredPhase

namespace AuthoredJob

abbrev RecordedView := Score.RecordedView × Option Atom × AuthoredPhase.RecordedView

instance instDecidableEqRecordedView : DecidableEq RecordedView :=
  inferInstanceAs (DecidableEq (Score.RecordedView × Option Atom × AuthoredPhase.RecordedView))

def recordedView (job : AuthoredJob) : RecordedView :=
  (job.score.recordedView, job.predicate, job.phase.recordedView)

def ofRecordedView (view : RecordedView) : AuthoredJob :=
  ⟨Score.ofRecordedView view.1, view.2.1, AuthoredPhase.ofRecordedView view.2.2⟩

theorem ofRecordedView_recorded (view : RecordedView) : (ofRecordedView view).Recorded :=
  ⟨Score.ofRecordedView_recorded _, AuthoredPhase.ofRecordedView_recorded _⟩

@[simp] theorem recordedView_ofRecordedView (view : RecordedView) :
    (ofRecordedView view).recordedView = view := by
  simp only [ofRecordedView, recordedView, Score.recordedView_ofRecordedView,
    AuthoredPhase.recordedView_ofRecordedView]

theorem ofRecordedView_recordedView (job : AuthoredJob) (valid : job.Recorded) :
    ofRecordedView job.recordedView = job := by
  cases job with
  | mk score predicate phase =>
      simp only [ofRecordedView, recordedView]
      rw [Score.ofRecordedView_recordedView score valid.1,
        AuthoredPhase.ofRecordedView_recordedView phase valid.2]

theorem parents_roundtrip (parents : List AuthoredJob)
    (valid : ∀ parent ∈ parents, parent.Recorded) :
    (parents.map recordedView).map ofRecordedView = parents := by
  simp only [List.map_map]
  calc
    _ = parents.map id := by
      apply List.map_congr_left
      intro parent member
      exact ofRecordedView_recordedView parent (valid parent member)
    _ = _ := List.map_id _

end AuthoredJob

abbrev RecordedWorkView := WorkOccurrence
  (Machine.RecordedView Origin Local Resume Rule Atom Empty String Empty)

def workRecordedView (body : WorkState) : RecordedWorkView :=
  ⟨body.state.recordedView, body.trace⟩

def workOfRecordedView (view : RecordedWorkView) : WorkState :=
  ⟨Machine.ofRecordedView view.state, view.trace⟩

theorem workOfRecordedView_recorded (view : RecordedWorkView) :
    (workOfRecordedView view).state.world.heap.Recorded := Machine.ofRecordedView_recorded _

@[simp] theorem workRecordedView_ofRecordedView (view : RecordedWorkView) :
    workRecordedView (workOfRecordedView view) = view := rfl

theorem workOfRecordedView_recordedView (body : WorkState)
    (valid : body.state.world.heap.Recorded) : workOfRecordedView (workRecordedView body) = body := by
  cases body with
  | mk state trace =>
      simp only [workOfRecordedView, workRecordedView]
      rw [Machine.ofRecordedView_recordedView state valid]

abbrev AuthoredRecordedView :=
  WeightedBranchingResumption.NestedPendingState RecordedWorkView AuthoredJob.RecordedView

def authoredRecordedView : AuthoredWork → AuthoredRecordedView
  | .inl body => .inl (workRecordedView body)
  | .inr (body, job, parents) =>
      .inr (workRecordedView body, job.recordedView, parents.map AuthoredJob.recordedView)

def authoredOfRecordedView : AuthoredRecordedView → AuthoredWork
  | .inl body => .inl (workOfRecordedView body)
  | .inr (body, job, parents) =>
      .inr (workOfRecordedView body, AuthoredJob.ofRecordedView job,
        parents.map AuthoredJob.ofRecordedView)

theorem authoredOfRecordedView_recorded (view : AuthoredRecordedView) :
    authoredHeapsRecorded (authoredOfRecordedView view) := by
  cases view with
  | inl body => exact workOfRecordedView_recorded body
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      refine ⟨workOfRecordedView_recorded body, AuthoredJob.ofRecordedView_recorded job, ?_⟩
      intro parent member
      obtain ⟨view, _, rfl⟩ := List.mem_map.mp member
      exact AuthoredJob.ofRecordedView_recorded view

@[simp] theorem authoredRecordedView_ofRecordedView (view : AuthoredRecordedView) :
    authoredRecordedView (authoredOfRecordedView view) = view := by
  cases view with
  | inl body => rfl
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      simp only [authoredOfRecordedView, authoredRecordedView, workRecordedView_ofRecordedView,
        AuthoredJob.recordedView_ofRecordedView, List.map_map]
      simp only [Function.comp_def, AuthoredJob.recordedView_ofRecordedView, List.map_id']

theorem authoredOfRecordedView_recordedView (work : AuthoredWork)
    (valid : authoredHeapsRecorded work) : authoredOfRecordedView (authoredRecordedView work) = work := by
  cases work with
  | inl body =>
      simp only [authoredOfRecordedView, authoredRecordedView]
      rw [workOfRecordedView_recordedView body valid]
  | inr held =>
      rcases held with ⟨body, job, parents⟩
      rcases valid with ⟨bodyValid, jobValid, parentsValid⟩
      simp only [authoredOfRecordedView, authoredRecordedView]
      rw [workOfRecordedView_recordedView body bodyValid,
        AuthoredJob.ofRecordedView_recordedView job jobValid,
        AuthoredJob.parents_roundtrip parents parentsValid]

theorem authoredRecordedView_injective (left right : AuthoredWork)
    (leftValid : authoredHeapsRecorded left) (rightValid : authoredHeapsRecorded right)
    (same : authoredRecordedView left = authoredRecordedView right) : left = right :=
  (authoredOfRecordedView_recordedView left leftValid).symm.trans
    ((congrArg authoredOfRecordedView same).trans
      (authoredOfRecordedView_recordedView right rightValid))

/-- Equality of invariant-carrying native states executes on finite retained
data, including every captured heap and suspended coefficient parent. -/
instance : DecidableEq {work : AuthoredWork // authoredHeapsRecorded work} := fun left right =>
  if same : authoredRecordedView left.val = authoredRecordedView right.val then
    isTrue (Subtype.ext (authoredRecordedView_injective _ _ left.property right.property same))
  else isFalse (fun equal => same (congrArg (fun work => authoredRecordedView work.val) equal))

theorem authored_result_heaps_iff (result : AuthoredResult) :
    authoredResultHeapsRecorded result ↔ authoredHeapsRecorded result := by
  cases result <;> rfl

instance : DecidableEq {result : AuthoredResult // authoredResultHeapsRecorded result} :=
  fun left right =>
    if same : authoredRecordedView left.val = authoredRecordedView right.val then
      isTrue (Subtype.ext (authoredRecordedView_injective _ _
        ((authored_result_heaps_iff _).mp left.property)
        ((authored_result_heaps_iff _).mp right.property) same))
    else isFalse (fun equal => same (congrArg (fun work => authoredRecordedView work.val) equal))


/-! ## Executable replay over the actual retained native heaps

The invariant witnesses come from the native instruction and capture proofs.
They are erased at execution. Comparison uses finite views of every live and
captured world; it does not assume equality of arbitrary function-valued heaps.
-/

abbrev RecordedAuthoredWork := {work : AuthoredWork // authoredHeapsRecorded work}
abbrev RecordedAuthoredResult := {result : AuthoredResult // authoredResultHeapsRecorded result}

/-- The original source with its proved heap invariant carried in the type.
No successor, including an equal or zero-weight occurrence, is filtered. -/
def recordedAuthoredSource {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    WeightedBranchingResumption.Coalgebra RecordedAuthoredWork RecordedAuthoredResult V :=
  WeightedBranchingResumption.invariantSource
    (authoredSource program annotation interpretation)
    authoredHeapsRecorded authoredResultHeapsRecorded
    (authored_source_recorded program annotation interpretation).1
    (authored_source_recorded program annotation interpretation).2

def recordedAuthoredRoot (term : Atom) : RecordedAuthoredWork :=
  ⟨.inl (WorkOccurrence.root (initial term)), authored_root_recorded term⟩

/-- Erasure retains the complete ordered finite observation, including all
pending handler frames and coefficients, at every cut of the native run. -/
theorem recorded_authored_contributions_erasure {V : Type} [Monoid V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) (fuel : Nat) (state : RecordedAuthoredWork) :
    WeightedBranchingResumption.contributions
      (authoredSource program annotation interpretation) fuel state.val =
      (WeightedBranchingResumption.contributions
        (recordedAuthoredSource program annotation interpretation) fuel state).map
          (fun leaf => (Sum.map Subtype.val Subtype.val leaf.1, leaf.2)) :=
  WeightedBranchingResumption.invariantSource_contributions _ _ _
    (authored_source_recorded program annotation interpretation).1
    (authored_source_recorded program annotation interpretation).2 fuel state

open Mettapedia.GSLT.Core.BranchingTemporal

/-- The existing occurrence scheduler applied to the preserved native
invariant. The outer path distinguishes equal successor occurrences. -/
def recordedAuthoredOccurrenceSystem {V : Type} [Monoid V] (program : Program)
    (annotation : Row → Option AuthoredClause) (interpretation : Outcome → Option V) :
    BranchingSystem (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) :=
  WorkOccurrence.system (WeightedBranchingResumption.Scheduled.pathMachine
    (recordedAuthoredSource program annotation interpretation))

/-- Native replay now has an executable equality procedure for all retained
states and results. Only equality of the chosen coefficient representation
is requested from its provider. Rules, interpretation, controller and starting
snapshot stay fixed; repeating external effects requires another contract. -/
theorem recorded_native_replay {V : Type} [Monoid V] [DecidableEq V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) Memory)
    (snapshot : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (RecordedAuthoredWork × V)) ((RecordedAuthoredResult × V) × List Nat) Memory)
    (capacity fuel : Nat)
    (fits : (Recording.stream (recordedAuthoredOccurrenceSystem program annotation interpretation)
      controller Recording.Replay.observe fuel snapshot).length ≤ capacity) :
    ((Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
      (recordedAuthoredOccurrenceSystem program annotation interpretation)
      (Recording.controller controller Recording.Replay.observe (some capacity)) fuel
      (Recording.start snapshot (some capacity))).memory.2).bind
        (fun record => Recording.Replay.readout
          (recordedAuthoredOccurrenceSystem program annotation interpretation) controller record snapshot) =
      some (.ok (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (recordedAuthoredOccurrenceSystem program annotation interpretation) controller fuel snapshot)) :=
  Recording.Replay.recorded_replay _ _ _ _ _ fits

/-- A mismatch preserves its entire native checkpoint and unconsumed suffix.
The accepted prefix consists of actual recomputed source transitions. -/
theorem recorded_native_replay_refusal {V : Type} [Monoid V] [DecidableEq V]
    (program : Program) (annotation : Row → Option AuthoredClause)
    (interpretation : Outcome → Option V) {Memory : Type*}
    (controller : Controller (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat) Memory)
    (frames pending : List (Preparation.Capture (WorkOccurrence (RecordedAuthoredWork × V))
      ((RecordedAuthoredResult × V) × List Nat)))
    (snapshot cut : Mettapedia.GSLT.Core.InferenceControl.Snapshot
      (WorkOccurrence (RecordedAuthoredWork × V)) ((RecordedAuthoredResult × V) × List Nat) Memory)
    (refused : Recording.Replay.run (recordedAuthoredOccurrenceSystem program annotation interpretation)
      controller frames snapshot = .error (cut, pending)) :
    ∃ acceptedFrames frame rest,
      frames = acceptedFrames ++ frame :: rest ∧ pending = frame :: rest ∧
      cut = Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        (recordedAuthoredOccurrenceSystem program annotation interpretation) controller
        acceptedFrames.length snapshot ∧
      Recording.Replay.step? (recordedAuthoredOccurrenceSystem program annotation interpretation)
        controller cut frame = none :=
  Recording.Replay.run_refused _ _ _ _ _ _ refused

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
