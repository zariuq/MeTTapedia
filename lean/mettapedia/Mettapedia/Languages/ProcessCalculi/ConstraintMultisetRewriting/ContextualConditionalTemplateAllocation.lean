import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateInputModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationInputs

/-!
# Allocated mixed-body firings use exactly tracked entry inputs

Logical source identifiers may be consumed and later reused. The existing
allocation cursor gives each creation a fresh bound name. Its net inputs
are original entry occurrences, and the source input-model theorem applies
to every such occurrence. Physical correctness uses the complete original
resource trace, rather than its net effect alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem initialInputs_iff_initialUse (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    occurrence ∈ schedule.initialInputs ↔ OccurrenceAllocationRenaming.initialUse schedule.selections occurrence :=
  (schedule.mem_initialInputs occurrence).trans
    ((schedule.footprint_has_port (.inl occurrence)).trans
      (OccurrenceAllocationRenaming.usesName_initial_iff schedule.selections occurrence))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem initialInputs_iff_initialUse (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    occurrence ∈ schedule.initialInputs ↔ OccurrenceAllocationRenaming.initialUse schedule.selections occurrence := by
  induction schedule with
  | nil _ => simp only [initialInputs, Finset.notMem_empty, selections, OccurrenceAllocationRenaming.initialUse]
  | segment past plain prior =>
      change occurrence ∈ past.initialInputs ∪ (plain.initialInputs \ past.creations) ↔
        OccurrenceAllocationRenaming.initialUse (past.selections ++ plain.selections) occurrence
      rw [Finset.mem_union, Finset.mem_sdiff, prior, plain.initialInputs_iff_initialUse,
        not_mem_creations, OccurrenceAllocationRenaming.initialUse_append]
      tauto
  | template mid past queries inners rule picked prior =>
      change occurrence ∈ past.initialInputs ∪ ((picked.taken.toFinset ∪ picked.read.toFinset) \ past.creations) ↔
        OccurrenceAllocationRenaming.initialUse (past.selections ++ [picked]) occurrence
      rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, List.mem_toFinset,
        prior, not_mem_creations, OccurrenceAllocationRenaming.initialUse_append]
      simp only [OccurrenceAllocationRenaming.initialUse, and_false, or_false]
      tauto

def allocated (schedule : Schedule S O Γ sort before after) : List (Selection (OccurrenceAllocationRenaming.Name O)) :=
  OccurrenceAllocationRenaming.rename OccurrenceAllocationRenaming.Cursor.initial schedule.selections

def net (schedule : Schedule S O Γ sort before after) : CompiledSchedule (OccurrenceAllocationRenaming.Name O) Unit :=
  CompiledSchedule.compile OccurrenceAllocationRenaming.label (OccurrenceAllocationRenaming.commits schedule.allocated)

theorem allocated_resources_of_executable (schedule : Schedule S O Γ sort before after)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    Executable OccurrenceAllocationRenaming.label (before.present.image Sum.inl)
        (OccurrenceAllocationRenaming.commits schedule.allocated) ∧
      fireList (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits schedule.allocated) =
        after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current := by
  have prepared : Executable OccurrenceAllocationRenaming.label before.present
      (OccurrenceAllocationRenaming.commits schedule.selections) := by
    with_unfolding_all exact resources
  obtain ⟨renamed, same⟩ := OccurrenceAllocationRenaming.lifts schedule.selections
    OccurrenceAllocationRenaming.Cursor.initial before.present prepared
  refine ⟨renamed, ?_⟩
  have sourceResult : fireList before.present (OccurrenceAllocationRenaming.commits schedule.selections) = after.present := by
    with_unfolding_all exact schedule.physical_trace
  rw [sourceResult] at same
  exact same

theorem allocated_net_commit (schedule : Schedule S O Γ sort before after)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    Enabled OccurrenceAllocationRenaming.label (before.present.image Sum.inl) schedule.net.effect ∧
      fire (before.present.image Sum.inl) schedule.net.effect =
        after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current := by
  obtain ⟨executable, same⟩ := schedule.allocated_resources_of_executable resources
  obtain ⟨enabled, netResult⟩ := (CompiledSchedule.compile_correct OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (before.present.image Sum.inl)).2
      ((CompiledSchedule.compile_condition_iff _ _ _).mpr executable)
  exact ⟨enabled, netResult.trans same⟩


theorem net_input_is_initial (schedule : Schedule S O Γ sort before after)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (physical : OccurrenceAllocationRenaming.Name O)
    (used : physical ∈ schedule.net.effect.taken ∪ schedule.net.effect.kept) :
    ∃ occurrence ∈ before.present, physical = Sum.inl occurrence ∧ occurrence ∈ schedule.initialInputs := by
  have enabled := (schedule.allocated_net_commit resources).1
  have present : physical ∈ before.present.image Sum.inl := by
    rcases Finset.mem_union.mp used with taken | kept
    · exact enabled.taken_subset taken
    · exact enabled.kept_subset kept
  obtain ⟨occurrence, member, same⟩ := Finset.mem_image.mp present
  refine ⟨occurrence, member, same.symm, ?_⟩
  obtain ⟨commit, inside, port⟩ := OccurrenceAllocationRenaming.compiled_input_has_port OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) physical used
  obtain ⟨picked, selected, rfl⟩ := List.mem_map.mp inside
  have named : OccurrenceAllocationRenaming.UsesName schedule.allocated (Sum.inl occurrence) :=
    ⟨picked, selected, (by simpa only [Selection.commit, List.mem_toFinset, same] using port)⟩
  exact (schedule.initialInputs_iff_initialUse occurrence).mpr
    ((OccurrenceAllocationRenaming.usesName_initial_iff schedule.selections occurrence).mp named)

theorem current_name_inherited_iff_shapes (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) :
    (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence =
      Sum.inl occurrence ↔ schedule.outputBirth occurrence = none := by
  rw [OccurrenceAllocationRenaming.finish_current_inl_iff]
  change (Sum.inl occurrence = Sum.inl occurrence ∧ _) ↔ _
  simp only [true_and]
  exact (schedule.outputBirth_none_iff_shapes shapes occurrence).symm

theorem net_made_not_inherited (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Sum.inl occurrence ∉ schedule.net.effect.made := by
  intro made
  obtain ⟨commit, member, created⟩ := OccurrenceAllocationRenaming.compiled_made_has_creation OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (Sum.inl occurrence) made
  exact OccurrenceAllocationRenaming.renamed_made_not_initial
    OccurrenceAllocationRenaming.Cursor.initial schedule.selections commit member occurrence created

theorem net_output_has_birth (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (physical : OccurrenceAllocationRenaming.Name O) (made : physical ∈ schedule.net.effect.made) :
    ∃ occurrence ∈ after.present, ∃ birth : Birth after.declarations O Γ sort,
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence = physical ∧
        schedule.outputBirth occurrence = some birth ∧ OccurrenceAllocationRenaming.erase physical = occurrence := by
  have present : physical ∈ fire (before.present.image Sum.inl) schedule.net.effect :=
    Finset.mem_union.mpr (.inr made)
  rw [(schedule.allocated_net_commit resources).2] at present
  obtain ⟨occurrence, member, same⟩ := Finset.mem_image.mp present
  cases selected : schedule.outputBirth occurrence with
  | none =>
      have inherited := (schedule.current_name_inherited_iff_shapes shapes occurrence).mpr selected
      have original : physical = Sum.inl occurrence := same.symm.trans inherited
      exact False.elim (schedule.net_made_not_inherited occurrence (original ▸ made))
  | some birth =>
      refine ⟨occurrence, member, birth, same, selected, ?_⟩
      rw [← same]
      exact (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects occurrence

theorem net_output_instances {Next : Type} {next : Next → MetaArity S}
    (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (physical : OccurrenceAllocationRenaming.Name O) (made : physical ∈ schedule.net.effect.made)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    ∃ birth : Birth after.declarations O Γ sort,
      schedule.outputBirth (OccurrenceAllocationRenaming.erase physical) = some birth ∧
        (birth.origin.Instances candidate pattern ↔
          ContextualConditionalRows.Matches last after.declarations candidate pattern
            (after.rows (OccurrenceAllocationRenaming.erase physical))) := by
  obtain ⟨occurrence, _present, birth, _current, selected, erased⟩ := schedule.net_output_has_birth shapes resources physical made
  refine ⟨birth, erased ▸ selected, ?_⟩
  rw [erased]
  exact schedule.selected_birth_instances shapes occurrence birth selected next candidate pattern

theorem net_inputs_realize_together {Next : Type} {next : Next → MetaArity S}
    (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (candidate : Assignment after.declarations next) (model : ContextualResidual.Models candidate after.equations)
    (inputs : List (OccurrenceAllocationRenaming.Name O))
    (used : ∀ physical ∈ inputs, physical ∈ schedule.net.effect.taken ∪ schedule.net.effect.kept) :
    ∃ extension : ContextualGuardMatching.Extension next, ∃ _filler : Assignment first extension.declarations,
      ∀ physical ∈ inputs, ∃ pattern : Term (signature S extension.declarations) Γ sort,
        ContextualConditionalRealizations.Realizes first before.declarations
          (Assignment.compose extension.assignment (Assignment.compose candidate schedule.frame.assignment))
          pattern (before.rows (OccurrenceAllocationRenaming.erase physical)) := by
  have logicalUsed : ∀ occurrence ∈ inputs.map OccurrenceAllocationRenaming.erase, occurrence ∈ schedule.initialInputs := by
    intro occurrence member
    obtain ⟨physical, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, _present, same, initial⟩ := schedule.net_input_is_initial resources physical (used physical inside)
    simpa only [same, OccurrenceAllocationRenaming.erase] using initial
  obtain ⟨extension, filler, realized⟩ := schedule.initial_inputs_realize_together shapes candidate model
    (inputs.map OccurrenceAllocationRenaming.erase) logicalUsed
  exact ⟨extension, filler, fun physical member => realized _ (List.mem_map.mpr ⟨physical, member, rfl⟩)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
