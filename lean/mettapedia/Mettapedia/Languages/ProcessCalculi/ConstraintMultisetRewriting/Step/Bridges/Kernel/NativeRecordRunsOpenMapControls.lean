import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsOpenMap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsCorrespondenceControls

/-!
# Pointed future lifting and failure of raw future lifting

These auxiliary controls use the existing shared-builder test-zero firing.
The same raw state supports observed zero and one. The firing is compatible
with zero and prunes one; forgetting the satisfying point carries steps but
does not lift all raw steps. No native EXPECT_ALPHA guard is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsOpenMapControls

open NativeRecordRuns NativeRecordRunsCorrespondence NativeRecordRunsOpenMap
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps

open NativeRecordRunsCorrespondenceControls

noncomputable section

abbrev Configuration := NativeRecordRunsCorrespondence.Configuration Pruning.Cell Pruning.Event

def good : Configuration := ⟨Pruning.raw, 0, Pruning.word, Pruning.startPoint 0⟩
def discarded : Configuration := ⟨Pruning.raw, 0, Pruning.word, Pruning.startPoint 1⟩
def finish : Configuration := ⟨Pruning.result, 1, [], Pruning.finishPoint⟩

theorem good_actual_step : (targetTheory Pruning.clause).Step good finish := ⟨Pruning.compatible_event⟩

theorem good_source_successor_unique {next : QueueState Nat Pruning.Event}
    (stepped : (sourceTheory Pruning.edge).Step (observe Pruning.read good) next) : next = observe Pruning.read finish := by
  obtain ⟨event, remaining, pendingSame, cursorSame, remainingSame, valid⟩ := stepped
  have empty : remaining = [] := by
    have same := congrArg List.tail pendingSame
    simpa [good, observe, Pruning.word] using same.symm
  apply QueueState.ext
  · exact valid.2.2
  · exact cursorSame
  · exact remainingSame.trans empty

/-- Every source successor of the compatible point is realized by the
actual admitted queue firing, including its exact observed endpoint. -/
theorem good_source_step_lifts {next : QueueState Nat Pruning.Event}
    (stepped : (sourceTheory Pruning.edge).Step (observe Pruning.read good) next) :
    ∃ after, (targetTheory Pruning.clause).Step good after ∧ observe Pruning.read after = next :=
  ⟨finish, good_actual_step, (good_source_successor_unique stepped).symm⟩

theorem good_diamond_commutes (predicate : QueueState Nat Pruning.Event → Prop) :
    pb (observe Pruning.read) (derivedDiamond (span (sourceTheory Pruning.edge).Step) predicate) good ↔
      derivedDiamond (span (targetTheory Pruning.clause).Step) (pb (observe Pruning.read) predicate) good := by
  change derivedDiamond (span (sourceTheory Pruning.edge).Step) predicate (observe Pruning.read good) ↔ _
  rw [diamond_iff, diamond_iff]
  constructor
  · rintro ⟨next, stepped, holds⟩
    obtain ⟨after, actual, same⟩ := good_source_step_lifts stepped
    exact ⟨after, actual, show predicate (observe Pruning.read after) from same.symm ▸ holds⟩
  · rintro ⟨after, ⟨event⟩, holds⟩
    exact ⟨observe Pruning.read after, event_reads_step Pruning.clause Pruning.read Pruning.edge Pruning.case_meaning event, holds⟩

theorem discarded_has_no_pointed_step (next : Configuration) : ¬ (targetTheory Pruning.clause).Step discarded next := by
  rintro ⟨event⟩
  have stepped := event_reads_step Pruning.clause Pruning.read Pruning.edge Pruning.case_meaning event
  change QueueStep Pruning.edge Pruning.discarded (observe Pruning.read next) at stepped
  exact Pruning.discarded_has_no_source_step _ stepped

theorem raw_forget_zig :
    Zig (targetTheory Pruning.clause).Step (Execution.theory (rawStep Pruning.clause)).Step
      (fun current : Configuration => current.state) :=
  (forgetTranslation Pruning.clause).mapStep

/-- A genuine admitted raw firing has no lift from the discarded old point. -/
theorem raw_forget_not_zag :
    ¬ Zag (targetTheory Pruning.clause).Step (Execution.theory (rawStep Pruning.clause)).Step
      (fun current : Configuration => current.state) := by
  intro lifts
  obtain ⟨next, stepped, _⟩ := lifts (x := discarded) Pruning.actual_raw_transition
  exact discarded_has_no_pointed_step next stepped

theorem raw_forget_not_functional_bisimulation :
    ¬ FunctionalBisimulation (targetTheory Pruning.clause).Step (Execution.theory (rawStep Pruning.clause)).Step
      (fun current : Configuration => current.state) :=
  fun comparison => raw_forget_not_zag comparison.zag

theorem raw_forget_diamond_fails :
    pb (fun current : Configuration => current.state)
        (derivedDiamond (span (Execution.theory (rawStep Pruning.clause)).Step) (· = Pruning.result)) discarded ∧
      ¬ derivedDiamond (span (targetTheory Pruning.clause).Step)
        (pb (fun current : Configuration => current.state) (· = Pruning.result)) discarded := by
  constructor
  · exact (diamond_iff _ _ Pruning.raw).mpr ⟨Pruning.result, Pruning.actual_raw_transition, rfl⟩
  · intro holds
    obtain ⟨next, stepped, _⟩ := (diamond_iff _ _ discarded).mp holds
    exact discarded_has_no_pointed_step next stepped

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsOpenMapControls
