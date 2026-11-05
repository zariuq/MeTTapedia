import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

/-!
# Selected contextual bodies admit fresh allocation names at the resource boundary

The source keeps its existing occurrence type. Only the compiler comparison
names each internal creation separately. Erasing those bound names recovers
the exact ordered source selections and the final source occurrence set.
The retained contextual admission still governs the whole body. Conditional
rows and original guard cuts have not been erased into resource enabling.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def allocated (schedule : Schedule S O Γ sort before after) : List (Selection (OccurrenceAllocationRenaming.Name O)) :=
  OccurrenceAllocationRenaming.rename OccurrenceAllocationRenaming.Cursor.initial schedule.selections

theorem allocated_trace (schedule : Schedule S O Γ sort before after) :
    schedule.allocated.map OccurrenceAllocationRenaming.project = schedule.selections :=
  OccurrenceAllocationRenaming.trace_projection schedule.selections OccurrenceAllocationRenaming.Cursor.initial

theorem allocated_resources_of_executable (schedule : Schedule S O Γ sort before after)
    (executable : Executable unitLabel before.present schedule.commits) :
    Executable OccurrenceAllocationRenaming.label (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits schedule.allocated) ∧
      fireList (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits schedule.allocated) =
        after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current := by
  have prepared : Executable OccurrenceAllocationRenaming.label before.present (OccurrenceAllocationRenaming.commits schedule.selections) := by
    with_unfolding_all exact executable
  obtain ⟨renamed, same⟩ := OccurrenceAllocationRenaming.lifts schedule.selections OccurrenceAllocationRenaming.Cursor.initial before.present prepared
  refine ⟨renamed, ?_⟩
  have sourceResult : fireList before.present (OccurrenceAllocationRenaming.commits schedule.selections) = after.present := by
    with_unfolding_all exact schedule.physical_trace
  rw [sourceResult] at same
  exact same

theorem allocated_resources (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) :
    Executable OccurrenceAllocationRenaming.label (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits schedule.allocated) ∧
      fireList (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits schedule.allocated) =
        after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current :=
  schedule.allocated_resources_of_executable
    (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).2.1

/-- One existing occurrence commit realizes the renamed resource boundary of every admitted body. -/
theorem allocated_net_commit (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) :
    let net := CompiledSchedule.compile OccurrenceAllocationRenaming.label (OccurrenceAllocationRenaming.commits schedule.allocated)
    Enabled OccurrenceAllocationRenaming.label (before.present.image Sum.inl) net.effect ∧
      (fire (before.present.image Sum.inl) net.effect).image OccurrenceAllocationRenaming.erase = after.present := by
  have executable := (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).2.1
  have prepared : Executable OccurrenceAllocationRenaming.label before.present (OccurrenceAllocationRenaming.commits schedule.selections) := by
    with_unfolding_all exact executable
  have result := OccurrenceAllocationRenaming.one_net_commit schedule.selections before.present prepared
  have sourceResult : fireList before.present (OccurrenceAllocationRenaming.commits schedule.selections) = after.present := by
    with_unfolding_all exact schedule.physical_trace
  rw [sourceResult] at result
  exact result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
