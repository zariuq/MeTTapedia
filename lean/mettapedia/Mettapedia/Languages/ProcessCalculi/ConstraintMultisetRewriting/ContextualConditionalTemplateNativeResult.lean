import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativePublicationValues
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeResults
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeInvocation

/-!
# Actual mixed producer results preserve source worlds

The physical comparison decodes only names allocated inside the firing.
Every source information model extends to an actual returned model, and
every present row keeps its conditional instances in all fresh futures.
The physical, model and world laws are the common ones of
`ContextualNativeResults`; this file supplies the captured publication
contract, then joins it with the common query-admitted firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

namespace NativePublication

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}


theorem retained_input_matches (publication : NativePublication schedule occupied) (occurrence : O)
    (retained : some (Sum.inl occurrence) ∉ publication.firing.selection.made)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (some (Sum.inl occurrence))) ↔
      Matches first before.declarations
        (Assignment.compose (Assignment.compose candidate publication.producerCaller) schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  rw [publication.retained_matches _ retained next candidate pattern,
    schedule.native.retained_native_row_matches_input occupied publication.firing occurrence retained candidate pattern]
  have square : Assignment.compose
      (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource publication.firing.update))
        (ContextualSelectionViews.capturedTarget
          (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) schedule.native.guardFamily))
      schedule.native.bindingCaptures =
      Assignment.compose (Assignment.compose candidate publication.producerCaller) schedule.frame.assignment := by
    let images : Assignment schedule.native.guardFamily next :=
      Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource publication.firing.update))
        schedule.native.guardNativeCaptures
    change Assignment.compose images (Assignment.compose schedule.native.bindingCurrent schedule.frame.assignment) =
      Assignment.compose (Assignment.compose candidate publication.producerCaller) schedule.frame.assignment
    exact (Assignment.compose_associative schedule.frame.assignment schedule.native.bindingCurrent images).trans
      (congrArg (fun assignment => Assignment.compose assignment schedule.frame.assignment)
        (schedule.native.producer_caller_assignment occupied publication.firing candidate).symm)

  erw [square]

theorem row_matches_source (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (schedule.native.producerPhysical occurrence)) ↔
      Matches last after.declarations (Assignment.compose candidate publication.producerCaller) pattern (after.rows occurrence) := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  by_cases made : cursor.current occurrence ∈ schedule.net.effect.made
  · have madePort : some (cursor.current occurrence) ∈ schedule.native.bindingSelection.made :=
      List.mem_map.mpr ⟨cursor.current occurrence, Finset.mem_toList.mpr made, rfl⟩
    obtain ⟨birth, selected, meaning⟩ := schedule.net_output_instances shapes resources
      (cursor.current occurrence) made (Assignment.compose candidate publication.producerCaller) pattern
    have existsRow := (schedule.output_row_exists_iff
      (OccurrenceAllocationRenaming.erase (cursor.current occurrence))).mpr ⟨birth, selected⟩
    obtain ⟨row, selectedRow⟩ := existsRow
    have rowMeaning := schedule.output_row_instances (OccurrenceAllocationRenaming.erase (cursor.current occurrence))
      (Assignment.compose candidate publication.producerCaller) pattern
    have rowInstances : Matches (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase (cursor.current occurrence)))
        after.declarations (Assignment.compose candidate publication.producerCaller) pattern row ↔
        birth.origin.Instances (Assignment.compose candidate publication.producerCaller) pattern := by
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
      (Assignment.compose candidate publication.producerCaller) pattern

/-- The decoded visible world of the mixed publication. -/
noncomputable def projection (publication : NativePublication schedule occupied) :
    ContextualClauseSourceState.World publication.resultLocals O Γ sort :=
  schedule.native.projectionOf occupied publication.firing publication.resultLocals publication.target.rows

theorem world_equivalent (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits) :
    ContextualWorldComparison.Equivalent after (generator after.declarations) publication.projection publication.producerCaller := by
  exact schedule.native.world_equivalent_of_rows occupied publication.firing shapes resources schedule.producer.values
    publication.authored publication.selected publication.resultLocals publication.target.rows
    (fun _ candidate pattern occurrence present => by
      exact publication.row_matches_source shapes resources candidate pattern occurrence present)

end NativePublication

/-- A mixed body of ordinary/shared segments and captured templates is
admitted exactly when one actual constructed native firing, with the
complete resource and original-cut query list, is admitted at the given
finite budget. Its conditional publication is then source-equivalent under
the declared row/model observation and bound-name projection. -/
theorem source_iff_native_body (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : ContextualPredicateQueryAdmission.WithQueries schedule.native.guardNativeBank
          (schedule.native.nativeBindingState occupied),
        ∃ rule : observed.firing.rule = schedule.producer.rule,
        ∃ selection : observed.firing.selection = schedule.native.bindingSelection,
        ∃ outputs : observed.firing.outputs = schedule.producer.outputs occupied,
        ∃ flags : observed.firing.reusable = schedule.producerReusable,
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producer.queries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (NativePublication.projection ⟨observed.firing, rule, selection, outputs, flags⟩)
            (NativePublication.producerCaller ⟨observed.firing, rule, selection, outputs, flags⟩) := by
  constructor
  · intro source
    obtain ⟨shapes, resources, _consistent, _guards⟩ := schedule.admitted_characterization.mp source
    obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
      (schedule.producer.source_iff_native_body_admission occupied fuel).mp source
    exact ⟨observed, rule, selection, outputs, flags, budget, queries,
      NativePublication.world_equivalent ⟨observed.firing, rule, selection, outputs, flags⟩ shapes resources⟩
  · rintro ⟨observed, rule, selection, outputs, flags, budget, queries, _equivalent⟩
    exact (schedule.producer.source_iff_native_body_admission occupied fuel).mpr
      ⟨observed, rule, selection, outputs, flags, budget, queries⟩

/-- The same firing completes the selected invocation: it consumes the
control occurrence, even for a mixed body without visible effects. -/
theorem source_iff_completed_invocation (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : ContextualPredicateQueryAdmission.WithQueries schedule.native.guardNativeBank
          (schedule.native.nativeBindingState occupied),
        ∃ rule : observed.firing.rule = schedule.producer.rule,
        ∃ selection : observed.firing.selection = schedule.native.bindingSelection,
        ∃ outputs : observed.firing.outputs = schedule.producer.outputs occupied,
        ∃ flags : observed.firing.reusable = schedule.producerReusable,
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producer.queries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (NativePublication.projection ⟨observed.firing, rule, selection, outputs, flags⟩)
            (NativePublication.producerCaller ⟨observed.firing, rule, selection, outputs, flags⟩) ∧
          none ∉ observed.firing.target.present ∧
          ContextualNativeBodies.invocationPending observed.firing.target.present <
            ContextualNativeBodies.invocationPending (schedule.native.nativeBindingState occupied).present := by
  constructor
  · intro source
    obtain ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent⟩ :=
      (schedule.source_iff_native_body occupied fuel).mp source
    exact ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent,
      schedule.native.completed_control_absent occupied observed.firing selection,
      schedule.native.invocation_pending_decreases occupied observed.firing selection⟩
  · rintro ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent, _completed, _progress⟩
    exact (schedule.source_iff_native_body occupied fuel).mpr
      ⟨observed, rule, selection, outputs, flags, budget, queries, equivalent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
