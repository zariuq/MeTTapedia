import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativePublicationValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativePublicationModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

/-!
# Actual mixed producer results preserve source worlds

The physical comparison decodes only names allocated inside the firing.
Every source information model extends to an actual returned model, and
every present row keeps its conditional instances in all fresh futures.
This result concerns the binding/resource producer. Attaching original-cut
predicate queries remains a separate admission obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

private theorem fire_with_control {N : Type} [DecidableEq N] (world : Finset N) (effect : Commit N Unit) :
    fire (insert none (world.image some))
        (⟨insert none (effect.taken.image some), effect.kept.image some, effect.made.image some, []⟩ : Commit (Option N) Unit) =
      (fire world effect).image some := by
  ext physical
  cases physical <;> simp [mem_fire]

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def producerPhysical (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (OccurrenceAllocationRenaming.Name O) :=
  some ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)

theorem producer_physical_injective (schedule : Schedule S O Γ sort before after) :
    Function.Injective schedule.producerPhysical :=
  fun _ _ same => (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).injective
    (Option.some.inj same)

namespace NativePublication

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}

theorem result_physical (publication : NativePublication schedule occupied)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    publication.target.present = after.present.image schedule.producerPhysical := by
  have sets := schedule.binding_selection_sets
  have commit : schedule.bindingSelection.commit (T := Unit) =
      ⟨insert none (schedule.net.effect.taken.image some), schedule.net.effect.kept.image some,
        schedule.net.effect.made.image some, []⟩ := by
    change Commit.mk _ _ _ [] = _
    rw [sets.1, sets.2.1, sets.2.2]
  rw [publication.physical_result, schedule.native_store_with_control occupied, commit, fire_with_control,
    (schedule.allocated_net_commit resources).2, Finset.image_image]
  rfl

theorem retained_input_matches (publication : NativePublication schedule occupied) (occurrence : O)
    (retained : some (Sum.inl occurrence) ∉ publication.firing.selection.made)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (some (Sum.inl occurrence))) ↔
      Matches first before.declarations
        (Assignment.compose (Assignment.compose candidate publication.returnCurrent) schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  rw [publication.retained_matches _ retained next candidate pattern,
    publication.firing.retained_matches _ retained next candidate pattern]
  change Matches (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily
    _ pattern
    (ContextualConditionalPublication.extendPrivate schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
      (schedule.bindingInput occurrence)) ↔ _
  erw [ContextualConditionalPublication.extendPrivate_matches_iff]
  rw [Assignment.compose_associative]
  erw [schedule.binding_input_matches]
  have square : Assignment.compose
      (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource publication.firing.update))
        (ContextualSelectionViews.capturedTarget
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
      schedule.bindingCaptures =
      Assignment.compose (Assignment.compose candidate publication.returnCurrent) schedule.frame.assignment := by
    simp only [returnCurrent, returnGuard, bindingCaptures, Assignment.compose_associative]
    exact congrArg (fun assignment => Assignment.compose
      (Assignment.compose assignment schedule.bindingCurrent) schedule.frame.assignment)
      (Assignment.compose_associative
        (ContextualSelectionViews.capturedTarget
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily)
        (ContextualComputedFreshFrame.includeSource publication.firing.update) candidate).symm
  erw [square]

theorem row_matches_source (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (schedule.producerPhysical occurrence)) ↔
      Matches last after.declarations (Assignment.compose candidate publication.returnCurrent) pattern (after.rows occurrence) := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  by_cases made : cursor.current occurrence ∈ schedule.net.effect.made
  · have madePort : some (cursor.current occurrence) ∈ schedule.bindingSelection.made :=
      List.mem_map.mpr ⟨cursor.current occurrence, Finset.mem_toList.mpr made, rfl⟩
    obtain ⟨birth, selected, meaning⟩ := schedule.net_output_instances shapes resources
      (cursor.current occurrence) made (Assignment.compose candidate publication.returnCurrent) pattern
    have existsRow := (schedule.output_row_exists_iff
      (OccurrenceAllocationRenaming.erase (cursor.current occurrence))).mpr ⟨birth, selected⟩
    obtain ⟨row, selectedRow⟩ := existsRow
    have rowMeaning := schedule.output_row_instances (OccurrenceAllocationRenaming.erase (cursor.current occurrence))
      (Assignment.compose candidate publication.returnCurrent) pattern
    have rowInstances : Matches (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase (cursor.current occurrence)))
        after.declarations (Assignment.compose candidate publication.returnCurrent) pattern row ↔
        birth.origin.Instances (Assignment.compose candidate publication.returnCurrent) pattern := by
      constructor
      · intro matched
        obtain ⟨other, same, observed⟩ := rowMeaning.mp ⟨row, selectedRow, matched⟩
        have equal := Option.some.inj (selected.symm.trans same)
        exact equal.symm ▸ observed
      · intro matched
        obtain ⟨other, same, observed⟩ := rowMeaning.mpr ⟨birth, selected, matched⟩
        have equal := Option.some.inj (selectedRow.symm.trans same)
        exact equal.symm ▸ observed
    exact (publication.output_matches (cursor.current occurrence) madePort row selectedRow next candidate pattern).trans
      (rowInstances.trans (by simpa only [cursor.projects] using meaning))
  · have visible : cursor.current occurrence ∈
        (before.present.image Sum.inl \ schedule.net.effect.taken) ∪ schedule.net.effect.made := by
      change cursor.current occurrence ∈ fire (before.present.image Sum.inl) schedule.net.effect
      rw [(schedule.allocated_net_commit resources).2]
      exact Finset.mem_image_of_mem _ present
    have old := (Finset.mem_sdiff.mp ((Finset.mem_union.mp visible).resolve_right made)).1
    obtain ⟨original, _oldPresent, same⟩ := Finset.mem_image.mp old
    have logical : original = occurrence := (congrArg OccurrenceAllocationRenaming.erase same).trans (cursor.projects occurrence)
    subst original
    have current : cursor.current occurrence = Sum.inl occurrence := same.symm
    have noBirth := (schedule.current_name_inherited_iff_shapes shapes occurrence).mp current
    have notMade : some (Sum.inl occurrence) ∉ publication.firing.selection.made := by
      rw [publication.selected]
      intro port
      obtain ⟨physical, member, physicalEq⟩ := List.mem_map.mp port
      have equal := Option.some.inj physicalEq
      apply made
      rw [current, ← equal]
      exact Finset.mem_toList.mp member
    change Matches _ _ candidate pattern (publication.target.rows (some (cursor.current occurrence))) ↔ _
    rw [current, publication.retained_input_matches occurrence notMade candidate pattern]
    exact schedule.retained_entry_instances shapes occurrence noBirth next
      (Assignment.compose candidate publication.returnCurrent) pattern

noncomputable def projection (publication : NativePublication schedule occupied) :
    ContextualClauseSourceState.World publication.resultLocals O Γ sort where
  Names := publication.firing.target.Names
  equality := publication.firing.target.equality
  declarations := publication.firing.target.declarations
  equations := publication.target.equations
  present := publication.target.present.biUnion fun physical =>
    match physical with
    | none => ∅
    | some name => {OccurrenceAllocationRenaming.erase name}
  rows occurrence := publication.target.rows (schedule.producerPhysical occurrence)

theorem projection_physical (publication : NativePublication schedule occupied)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    publication.projection.present = after.present := by
  change (publication.target.present.biUnion _) = _
  rw [publication.result_physical resources]
  ext occurrence
  constructor
  · intro member
    obtain ⟨physical, visible, decoded⟩ := Finset.mem_biUnion.mp member
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp visible
    change occurrence ∈ {OccurrenceAllocationRenaming.erase
      ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current original)} at decoded
    have same := Finset.mem_singleton.mp decoded
    rw [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects] at same
    exact same.symm ▸ present
  · intro member
    apply Finset.mem_biUnion.mpr
    refine ⟨schedule.producerPhysical occurrence, Finset.mem_image_of_mem _ member, ?_⟩
    change occurrence ∈ {OccurrenceAllocationRenaming.erase
      ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)}
    rw [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects]
    exact Finset.mem_singleton_self _

theorem related (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (candidate : Assignment publication.firing.target.declarations next)
    (model : ContextualResidual.Models candidate publication.target.equations) :
    ContextualWorldComparison.Related after (generator after.declarations)
      publication.projection publication.returnCurrent
      (Assignment.compose candidate publication.returnCurrent) candidate := by
  refine ⟨publication.every_target_model_projects next candidate model, model, Assignment.compose_identity_right _, ?_⟩
  intro later pattern occurrence present
  erw [Assignment.compose_associative]
  exact (publication.row_matches_source shapes resources (Assignment.compose later.assignment candidate)
    pattern occurrence present).symm

theorem world_equivalent (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    ContextualWorldComparison.Equivalent after (generator after.declarations) publication.projection publication.returnCurrent := by
  refine ⟨(publication.projection_physical resources).symm, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨extension, other, targetModel, fixed⟩ := publication.every_source_model_extends shapes resources future candidate model
    refine ⟨extension, other, ?_⟩
    have comparison := publication.related shapes resources other targetModel
    rw [fixed] at comparison
    exact comparison
  · intro Future future candidate model
    refine ⟨ContextualGuardMatching.Extension.identity future,
      Assignment.compose candidate publication.returnCurrent, ?_⟩
    change ContextualWorldComparison.Related after _ _ _ _ (Assignment.compose (generator future) candidate)
    rw [Assignment.compose_identity_left]
    exact publication.related shapes resources candidate model

end NativePublication

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
