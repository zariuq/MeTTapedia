import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeQueueCommitGrain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsCorrespondenceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeRoundExecution

/-!
# A real singleton queue event and the boundary of its round bound

The arithmetic fixture uses the existing admitted zero-test and its retained
source solution. Repeating that event conflicts on the same input occurrence.
The separate existing native maker example admits a three-event round, so
the queue's bound does not generalize to arbitrary native stores.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeQueueCommitGrainControls

open NativeRecordRuns NativeRecordRunsCorrespondence NativeQueueCommitGrain
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite

noncomputable section

namespace Fixture

open NativeRecordRunsCorrespondenceControls.Pruning

def start : NativeRecordRunsCorrespondence.Configuration Cell Event := ⟨raw,0,word,startPoint 0⟩
def finish : NativeRecordRunsCorrespondence.Configuration Cell Event := ⟨result,1,[],finishPoint⟩

def event : PointedEvent clause start finish :=
  .fire (startPoint 0) actual actual_admitted finishPoint execution.restricts

def outgoing : Outgoing clause start := ⟨finish,event⟩

theorem actual_event_admitted : (targetTheory clause).Step start finish := ⟨event⟩

theorem actual_singleton_independent :
    ([outgoing] : List (Outgoing clause start)).Pairwise Apart := singleton_independent outgoing

theorem actual_singleton_reports_one : ([outgoing] : List (Outgoing clause start)).length = 1 := rfl

theorem repeated_input_is_not_an_independent_round :
    ¬ ([outgoing,outgoing] : List (Outgoing clause start)).Pairwise Apart :=
  two_occurrences_not_independent outgoing outgoing

theorem another_solution_cannot_use_the_event (last : NativeRecordRunsCorrespondence.Configuration Cell Event) :
    ¬ Nonempty (PointedEvent clause ⟨raw,0,word,startPoint 1⟩ last) := by
  rintro ⟨wrong⟩
  have source := event_reads_step clause read edge case_meaning wrong
  exact discarded_has_no_source_step (observe read last) source

end Fixture

theorem another_native_store_has_a_larger_round :
    ∃ last, ∃ witness : NativeRoundExecution.Witness NativeResidualExample.initial
      NativeIteratedControls.makers last, witness.toRun.word.length > 1 := by
  obtain ⟨last,witness,length,_⟩ :=
    NativeRoundExecution.three_makers_have_actual_runs (List.Perm.refl NativeIteratedControls.makers)
  exact ⟨last,witness,by omega⟩

namespace SerialCoarsening

open NativeRecordRunsControls

private theorem route_two {before after : NativeRecordRunsCorrespondence.Configuration Cell Event}
    (route : Route (PointedEvent clause) before after) (two : route.length = 2) :
    ∃ middle, (targetTheory clause).Step before middle ∧ (targetTheory clause).Step middle after := by
  cases route with
  | refl => cases two
  | cons first rest =>
      cases rest with
      | refl => cases two
      | cons second tail =>
          cases tail with
          | refl => exact ⟨_,⟨first⟩,⟨second⟩⟩
          | cons third later =>
              change later.length + 1 + 1 + 1 = 2 at two
              omega

/-- The actual two-record arithmetic run expands as two firings. Its
unchanged observation cannot satisfy a zero-or-one-step readback after
those two dependent events are grouped into one serial macro step. -/
theorem actual_expansion_and_single_step_obstruction :
    ∃ before after, ∃ stepped : (twoStepTheory clause).Step before after,
      ((expandTwo clause).mapStep stepped).length = 2 ∧
      ¬ ∃ reader : OperationalReadback
          (sourceTheory NativeRecordRunsCorrespondenceControls.Arithmetic.edge) (twoStepTheory clause),
        ∀ source current, reader.related source current ↔
          observe NativeRecordRunsCorrespondenceControls.Arithmetic.read current = source := by
  obtain ⟨lift,length,_,_⟩ := NativeRecordRunsCorrespondenceControls.Arithmetic.actual_reallocated_lift
  obtain ⟨middle,first,last⟩ := route_two lift.path length
  exact ⟨_,_,⟨middle,first,last⟩,expandTwo_length clause _,
    two_steps_cannot_read_as_one NativeRecordRunsCorrespondenceControls.Arithmetic.read
      NativeRecordRunsCorrespondenceControls.Arithmetic.edge first last⟩

end SerialCoarsening

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeQueueCommitGrainControls
