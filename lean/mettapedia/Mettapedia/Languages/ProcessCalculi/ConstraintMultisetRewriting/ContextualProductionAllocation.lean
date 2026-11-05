import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationInputs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleRowAssembly

/-!
# Native net outputs select surviving source productions

An inherited allocation name corresponds to an input row. Every name in the
compiled net output set has a concrete surviving production index. Thus the
resource compiler cannot request an output payload from a retained-input
fallback, including when a source occurrence number is recycled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

namespace OccurrenceAllocationRenaming

variable {O : Type} [DecidableEq O]

theorem finish_current_inl_iff (cursor : Cursor O) (code : List (Selection O)) (occurrence original : O) :
    (finish cursor code).current occurrence = .inl original ↔
      cursor.current occurrence = .inl original ∧ ∀ picked ∈ code, occurrence ∉ picked.made := by
  induction code generalizing cursor with
  | nil => simp only [finish, List.not_mem_nil, false_implies, implies_true, and_true]
  | cons picked rest prior =>
      rw [finish, prior]
      by_cases made : occurrence ∈ picked.made
      · simp [Cursor.advance, made, fresh]
      · simp [Cursor.advance, made]

theorem renamed_made_not_initial (cursor : Cursor O) (code : List (Selection O)) :
    ∀ commit ∈ commits (rename cursor code), ∀ occurrence, Sum.inl occurrence ∉ commit.made := by
  induction code generalizing cursor with
  | nil => simp only [rename, commits, List.map_nil, List.not_mem_nil, false_implies, implies_true]
  | cons picked rest prior =>
      intro commit member occurrence
      change commit ∈ (cursor.rename picked).commit :: commits (rename (cursor.advance picked) rest) at member
      rcases List.mem_cons.mp member with rfl | tail
      · change Sum.inl occurrence ∉ (picked.made.map (fresh cursor.next)).toFinset
        simp [fresh]
      · exact prior (cursor.advance picked) commit tail occurrence

end OccurrenceAllocationRenaming

namespace ContextualSourceSchedules.Schedule

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem current_name_inherited_iff_shapes (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) :
    (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence =
      Sum.inl occurrence ↔ schedule.productionIndex occurrence = none := by
  rw [OccurrenceAllocationRenaming.finish_current_inl_iff]
  change (Sum.inl occurrence = Sum.inl occurrence ∧ _) ↔ _
  simp only [true_and]
  exact (schedule.productionIndex_none_iff_shapes shapes occurrence).symm

theorem current_name_inherited_iff (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (occurrence : O) :
    (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence =
      Sum.inl occurrence ↔ schedule.productionIndex occurrence = none :=
  schedule.current_name_inherited_iff_shapes (schedule.admitted_characterization.mp admitted).1 occurrence


theorem net_made_not_inherited (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Sum.inl occurrence ∉ schedule.net.effect.made := by
  intro made
  obtain ⟨commit, member, created⟩ := OccurrenceAllocationRenaming.compiled_made_has_creation OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (Sum.inl occurrence) made
  exact OccurrenceAllocationRenaming.renamed_made_not_initial
    OccurrenceAllocationRenaming.Cursor.initial schedule.selections commit member occurrence created

/-- Every physical net output has a source production, with the same logical occurrence under erasure. -/
theorem net_output_has_production_of_resources (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (physical : OccurrenceAllocationRenaming.Name O)
    (made : physical ∈ schedule.net.effect.made) :
    ∃ occurrence ∈ after.present, ∃ index : schedule.BirthIndex,
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence = physical ∧
        schedule.productionIndex occurrence = some index ∧ OccurrenceAllocationRenaming.erase physical = occurrence := by
  have present : physical ∈ schedule.assembled.present := by
    change physical ∈ (before.present.image Sum.inl \ schedule.net.effect.taken) ∪ schedule.net.effect.made
    exact Finset.mem_union.mpr (.inr made)
  rw [schedule.assembled_physical_of_resources resources] at present
  obtain ⟨occurrence, member, same⟩ := Finset.mem_image.mp present
  cases selected : schedule.productionIndex occurrence with
  | none =>
      have inherited := (schedule.current_name_inherited_iff_shapes shapes occurrence).mpr selected
      have impossible : physical = Sum.inl occurrence := same.symm.trans inherited
      exact False.elim (schedule.net_made_not_inherited occurrence (impossible ▸ made))
  | some index =>
      refine ⟨occurrence, member, index, same, selected, ?_⟩
      rw [← same]
      exact (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects occurrence

theorem net_output_has_production (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) (physical : OccurrenceAllocationRenaming.Name O)
    (made : physical ∈ schedule.net.effect.made) :
    ∃ occurrence ∈ after.present, ∃ index : schedule.BirthIndex,
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence = physical ∧
        schedule.productionIndex occurrence = some index ∧ OccurrenceAllocationRenaming.erase physical = occurrence :=
  schedule.net_output_has_production_of_resources
    (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).1
    (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).2.1 physical made

end ContextualSourceSchedules.Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
