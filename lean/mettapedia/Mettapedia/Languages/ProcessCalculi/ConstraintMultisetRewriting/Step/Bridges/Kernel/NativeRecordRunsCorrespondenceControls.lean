import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsControls

/-!
# Actual pointed lifts and a pruning counterexample

The positive controls use the existing shared-builder arithmetic execution.
The auxiliary pruning model below distinguishes existential raw readout from
the explicit satisfying-point carrier. Neither is a native EXPECT_ALPHA or
native consumer implementation claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsCorrespondenceControls

open NativeFieldSchema NativeRecordRuns InterpretedFrames NativeRecordRunsCorrespondence
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps

noncomputable section

namespace Arithmetic

open NativeRecordRunsControls

def word : List Event := [(.addSeven, 7), (.double, 14)]

def start : Store := NativeRecordRunsControls.initial 0 word (fun _ => 0) 0

def startPoint : PointData start 0 word where
  layout := canonicalLayout (fun _ => 0) 0
  environment := PUnit.unit
  fields := fields 0
  view := NativeRecordRunsControls.initial_view _ _ _ _ _

def read (values : (name : Field) → Cell name) : Nat := values .context

def edge (before : Nat) (event : Event) (after : Nat) : Prop :=
  event.2 = arithmetic event.1 before ∧ permitted event.1 before ∧ after = event.2

theorem case_meaning (record : ArithmeticRecord) (number effect : Nat)
    (valid : (clause record).guard number effect) :
    edge (read (fun name => (clause record).before name number)) (record, effect)
      (read (fun name => (clause record).after name number)) := by
  change effect = arithmetic record number ∧ permitted record number ∧ arithmetic record number = effect
  exact ⟨valid.1, valid.2, valid.1.symm⟩

theorem actual_reallocated_lift :
    ∃ lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment,
      lift.path.length = 2 ∧
      firingWord lift.path = reallocatedArithmeticExecution.run.word ∧
      forgetPath lift.path = Execution.toEvents (rawStep clause) reallocatedArithmeticExecution.run := by
  obtain ⟨lift⟩ := lift_run clause reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment
    reallocatedArithmeticExecution.view.solved startPoint reallocatedArithmeticExecution.restricts
  exact ⟨lift, lift.exact_length.trans reallocatedArithmeticExecution.count, lift.exact_firing_word, lift.projected⟩

theorem lifted_second_uses_noncanonical_field_id
    (lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment) :
    ∃ selected, (firingWord lift.path)[1]? = some selected ∧
      Occurrence.request 2 ∈ selected.2.selection.taken := by
  rw [lift.exact_firing_word]
  exact ⟨_, rfl, reallocated_second_consumes_changed_identity⟩

theorem lifted_final_observation
    (lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment) :
    observe read ⟨reallocatedArithmeticExecution.run.last, lift.finalCursor, lift.remaining, lift.point⟩ =
      (⟨14, 2, []⟩ : QueueState Nat Event) := by
  have finalView := lift.point.view
  rw [lift.environmentSame] at finalView
  obtain ⟨sameFields, sameCursor, samePending⟩ := view_observables finalView reallocatedArithmeticExecution.view
  apply QueueState.ext
  · exact congrArg read sameFields
  · exact sameCursor
  · exact samePending

theorem source_readback_of_actual_lift
    (lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment) :
    ∃ path : ExecutionPath (sourceTheory edge) (⟨0, 0, word⟩ : QueueState Nat Event) ⟨14, 2, []⟩,
      path.length ≤ 2 := by
  let reader := readback clause read edge case_meaning
  have related : reader.related (⟨0, 0, word⟩ : QueueState Nat Event) ⟨start, 0, word, startPoint⟩ := rfl
  obtain ⟨after, path, finalRelated, bound⟩ := reader.reflectPath related (toTheoryPath lift.path)
  have finalSame : after = (⟨14, 2, []⟩ : QueueState Nat Event) :=
    finalRelated.symm.trans (lifted_final_observation lift)
  have castLength : (finalSame ▸ path).length = path.length := by cases finalSame; rfl
  refine ⟨finalSame ▸ path, castLength.trans_le (bound.trans_eq ?_)⟩
  exact (toTheoryPath_length lift.path).trans (lift.exact_length.trans reallocatedArithmeticExecution.count)

theorem actual_two_occurrences_and_readback :
    ∃ lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment,
      lift.path.length = 2 ∧ firingWord lift.path = reallocatedArithmeticExecution.run.word ∧
      ∃ path : ExecutionPath (sourceTheory edge) (⟨0, 0, word⟩ : QueueState Nat Event) ⟨14, 2, []⟩,
        path.length ≤ 2 := by
  obtain ⟨lift, length, wordSame, _⟩ := actual_reallocated_lift
  exact ⟨lift, length, wordSame, source_readback_of_actual_lift lift⟩

theorem source_path_cursor {first last : QueueState Nat Event}
    (path : ExecutionPath (sourceTheory edge) first last) : last.cursor = first.cursor + path.length := by
  induction path with
  | refl state => rfl
  | @cons first middle last step rest ih =>
      obtain ⟨event, remaining, _, cursorSame, _, _⟩ := step.down
      change last.cursor = first.cursor + (rest.length+1)
      omega

theorem exact_source_readback_of_actual_lift
    (lift : RunLiftData clause startPoint reallocatedArithmeticExecution.run reallocatedArithmeticExecution.environment) :
    ∃ path : ExecutionPath (sourceTheory edge) (⟨0, 0, word⟩ : QueueState Nat Event) ⟨14, 2, []⟩,
      path.length = 2 := by
  obtain ⟨path, _⟩ := source_readback_of_actual_lift lift
  have cursor := source_path_cursor path
  change (2 : Nat) = 0 + path.length at cursor
  exact ⟨path, by omega⟩

end Arithmetic

namespace Pruning

inductive Record where
  | testZero
  deriving DecidableEq, Repr

abbrev Cell (_ : Field) := Nat
abbrev numberFrame : Frame := ⟨Nat, ⟨0⟩⟩
abbrev Event := Record × numberFrame.Carrier
abbrev Value := AtomData Cell Event
abbrev Store := StoreData Cell Event

def values (number : Nat) : (name : Field) → Cell name :=
  fun name => if name = .context then number else 0

def clause (record : Record) : QueueClause Cell Record numberFrame where
  witness := numberFrame
  before name number := values number name
  after name number := values number name
  record _ := record
  guard number effect := number = 0 ∧ effect = 0
  writes := []
  writes_distinct := by decide
  unchanged _ _ _ := rfl

def rules : RuleSyntax.Program (Terms Value) := familyProgram clause
theorem member (record : Record) : (clause record).rule ∈ rules := ⟨record, rfl⟩

def layout : Layout := canonicalLayout (fun _ => 0) 0
def word : List Event := [(.testZero, 0)]

/-- The old frame has two genuine observed solutions, zero and one. -/
def raw : Store where
  frame := numberFrame
  knowledge := []
  present := layout.support
  label occurrence number := match occurrence with
    | .field name _ => .field name (values number name)
    | .request _ => .pending 0 word

theorem raw_view (number : Nat) : ViewData raw layout number (values number) 0 word := by
  refine ⟨rfl, ?_, fun _ => rfl, rfl⟩
  intro equation inside
  cases inside

def startPoint (number : Nat) : PointData raw 0 word where
  layout := layout
  environment := number
  fields := values number
  view := raw_view number

def locals : (clause .testZero).localFrame.Carrier := ⟨0, [], (0 : Nat), (0 : Nat)⟩
def made : List Occurrence := NativeRecordLayouts.allocate layout []
def selected : Selection Occurrence := selectionAt layout [] made
def actual := (clause .testZero).firing (member .testZero) (old := raw.frame) selected

theorem actual_admitted : (rawStep clause).Admits (s := raw) actual :=
  (clause .testZero).admitted_at_view (member .testZero) raw layout (0 : Nat) (values 0) 0 word (raw_view 0)
    locals (fun _ => rfl) rfl rfl ⟨rfl, rfl⟩ made
    (NativeRecordLayouts.allocate_length layout []) (NativeRecordLayouts.allocate_nodup layout [])
    (NativeRecordLayouts.allocate_fresh layout [])

def result : Store := actual.result (frames Value) raw

def execution : ExecutionData rules raw (0 : Nat) 1 [] 1 :=
  (clause .testZero).one_step_at_execution (member .testZero) raw layout 0 (0 : Nat) (values 0) word
    (raw_view 0) locals (fun _ => rfl) rfl rfl ⟨rfl, rfl⟩

def finishPoint : PointData result 1 [] := execution.point

def read (fields : (name : Field) → Cell name) : Nat := fields .context

def edge (before : Nat) (event : Event) (after : Nat) : Prop :=
  before = 0 ∧ event.2 = 0 ∧ after = before

theorem case_meaning (record : Record) (number effect : Nat)
    (valid : (clause record).guard number effect) :
    edge (read (fun name => (clause record).before name number)) (record, effect)
      (read (fun name => (clause record).after name number)) := ⟨valid.1, valid.2, rfl⟩

theorem old_two_observed_solutions :
    ViewData raw layout (0 : Nat) (values 0) 0 word ∧ ViewData raw layout (1 : Nat) (values 1) 0 word ∧
      read (values 0) ≠ read (values 1) := ⟨raw_view 0, raw_view 1, by decide⟩

theorem result_old_component_zero (environment : result.frame.Carrier)
    (satisfied : Satisfies result.knowledge environment) : environment.1 = (0 : Nat) := by
  obtain ⟨move⟩ := invert_move clause raw actual actual_admitted environment satisfied
    layout (values environment.1) 0 word (raw_view environment.1)
  have same := move.input.fieldsSame .context
  change environment.1 = move.locals.values at same
  exact same.trans move.valid.1

/-- Pruning removes observed one at every admissible result view, regardless
of the proposed layout, cursor or residual word. -/
theorem result_observed_zero (environment : result.frame.Carrier) (otherLayout : Layout)
    (fields : (name : Field) → Cell name) (cursor : Nat) (pending : List Event)
    (view : ViewData result otherLayout environment fields cursor pending) : read fields = 0 := by
  obtain ⟨move⟩ := invert_move clause raw actual actual_admitted environment view.solved
    layout (values environment.1) 0 word (raw_view environment.1)
  have equal := (view_observables move.result view).1
  have contextSame := congrFun equal .context
  exact contextSame.symm.trans move.valid.1

def naiveRelated (source : QueueState Nat Event) (state : Store) : Prop :=
  ∃ (layout : Layout) (environment : state.frame.Carrier) (fields : (name : Field) → Cell name),
    ViewData state layout environment fields source.cursor source.pending ∧ read fields = source.value

def discarded : QueueState Nat Event := ⟨1, 0, word⟩

theorem discarded_origin_related : naiveRelated discarded raw := ⟨layout, (1 : Nat), values 1, raw_view 1, rfl⟩

theorem no_result_value_one (source : QueueState Nat Event) (one : source.value = 1) :
    ¬ naiveRelated source result := by
  rintro ⟨layout, environment, fields, view, observed⟩
  have zero := result_observed_zero environment layout fields source.cursor source.pending view
  omega

theorem discarded_has_no_source_step (next : QueueState Nat Event) : ¬ QueueStep edge discarded next := by
  rintro ⟨event, remaining, _, _, _, valid⟩
  have impossible : (1 : Nat) = 0 := valid.1
  omega

theorem actual_raw_transition : (Execution.theory (rawStep clause)).Step raw result :=
  ⟨actual, actual_admitted, rfl⟩

/-- The naive existential relation cannot satisfy the existing readStep law
for this actual admitted raw transition. -/
theorem naive_readback_impossible :
    ¬ ∃ reader : OperationalReadback (sourceTheory edge) (Execution.theory (rawStep clause)),
      reader.related = naiveRelated := by
  rintro ⟨reader, related⟩
  have before : reader.related discarded raw := related.symm ▸ discarded_origin_related
  rcases reader.readStep before actual_raw_transition with unchanged | ⟨next, stepped, _⟩
  · have after : naiveRelated discarded result := related ▸ unchanged
    exact no_result_value_one discarded rfl after
  · exact discarded_has_no_source_step next stepped

def compatible_event : PointedEvent clause ⟨raw, 0, word, startPoint 0⟩ ⟨result, 1, [], finishPoint⟩ :=
  PointedEvent.fire (startPoint 0) actual actual_admitted finishPoint rfl

theorem pointed_zero_reads :
    QueueStep edge (observe read (⟨raw, 0, word, startPoint 0⟩ : NativeRecordRunsCorrespondence.Configuration Cell Event))
      (observe read (⟨result, 1, [], finishPoint⟩ : NativeRecordRunsCorrespondence.Configuration Cell Event)) :=
  event_reads_step clause read edge case_meaning compatible_event

theorem discarded_point_incompatible (finishCursor : Nat) (finishPending : List Event)
    (finish : PointData result finishCursor finishPending) : finish.environment.1 ≠ (startPoint 1).environment := by
  have zero := result_old_component_zero finish.environment finish.view.solved
  change finish.environment.1 ≠ (1 : Nat)
  intro same
  have impossible : (0 : Nat) = 1 := zero.symm.trans same
  exact Nat.zero_ne_one impossible

end Pruning

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsCorrespondenceControls
