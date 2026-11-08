import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeInvocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

/-!
# The constructed native producer preserves visible source rows and bindings

Created occurrence names are decoded through the authored allocation map.
The explicit control row is excluded by the declared source observation.
Ordinary, shared and retained rows are compared at each present source
occurrence under the same returned caller assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualPredicateQueryAdmission
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

section Firing

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing schedule.native.guardNativeBank (schedule.native.nativeBindingState occupied))

theorem producer_row_matches_origin (source : schedule.Admitted)
    (rule : firing.rule = schedule.producer.rule) (selection : firing.selection = schedule.native.bindingSelection)
    (outputs : firing.outputs = schedule.producer.outputs occupied) (flags : firing.reusable = schedule.producerReusable)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches (ContextualPublication.privateFamily schedule.native.guardNativeBank firing.update.declaration) firing.target.declarations
        candidate pattern (firing.target.rows (schedule.native.producerPhysical occurrence)) ↔
      (schedule.origins occurrence).Instances (Assignment.compose candidate (schedule.native.producerCaller occupied firing)) pattern := by
  obtain ⟨shapes, resources, consistent, _guards⟩ := schedule.admitted_characterization.mp source
  let physical := schedule.native.producerPhysical occurrence
  by_cases made : physical ∈ schedule.native.bindingSelection.made
  · obtain ⟨index, selected⟩ := schedule.producer_birth_exists shapes resources physical made
    have sourceIndex : schedule.productionIndex occurrence = some index := by
      change schedule.productionIndex (OccurrenceAllocationRenaming.erase
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) = some index at selected
      rwa [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects] at selected
    have origin := schedule.selected_production_origin occurrence index sourceIndex
    have value := schedule.producer_output_birth occupied physical made index selected
    have flag := schedule.producer_flag_birth physical index selected
    have actualMade : physical ∈ firing.selection.made := by rw [selection]; exact made
    rw [← origin]
    by_cases ordinary : (schedule.births.get index).reusable = true
    · have actualOrdinary : firing.reusable physical = true := by rw [flags, flag, ordinary]
      have actualValue : firing.outputs physical = schedule.nativeBirthValue index := by
        rw [outputs, value, producerBirthValue, ordinary]
        rfl
      simpa only [Birth.origin, ordinary, if_true, Origin.Instances] using
        (schedule.ordinary_native_row_matches_birth shapes resources consistent occupied schedule.producer.values []
          firing rule selection physical actualMade actualOrdinary index actualValue candidate pattern)
    · have shared : (schedule.births.get index).reusable = false := Bool.eq_false_iff.mpr ordinary
      have actualShared : firing.reusable physical = false := by rw [flags, flag, shared]
      have actualValue : firing.outputs physical =
          schedule.native.nativeBindingValue (instantiate schedule.native.bindingCurrent
            (instantiate (schedule.births.get index).transport (schedule.births.get index).value)) := by
        rw [outputs, value, producerBirthValue, shared]
        rfl
      simp only [Birth.origin, shared, Bool.false_eq_true, if_false, Origin.Instances]
      rw [schedule.native.producer_caller_assignment occupied firing candidate]
      exact schedule.native.shared_native_row_matches_current occupied firing physical actualMade actualShared
        (instantiate (schedule.births.get index).transport (schedule.births.get index).value) actualValue candidate pattern
  · let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
    have netNotMade : cursor.current occurrence ∉ schedule.net.effect.made := by
      intro created
      apply made
      exact List.mem_map.mpr ⟨cursor.current occurrence, Finset.mem_toList.mpr created, rfl⟩
    have visible : cursor.current occurrence ∈ (before.present.image Sum.inl \ schedule.net.effect.taken) ∪ schedule.net.effect.made := by
      change cursor.current occurrence ∈ schedule.assembled.present
      rw [schedule.assembled_physical_of_resources resources]
      exact Finset.mem_image_of_mem _ present
    have old := (Finset.mem_sdiff.mp ((Finset.mem_union.mp visible).resolve_right netNotMade)).1
    obtain ⟨original, _present, same⟩ := Finset.mem_image.mp old
    have logical : original = occurrence := (congrArg OccurrenceAllocationRenaming.erase same).trans (cursor.projects occurrence)
    subst original
    have current : cursor.current occurrence = Sum.inl occurrence := same.symm
    have noBirth := (schedule.current_name_inherited_iff_shapes shapes occurrence).mp current
    have origin : schedule.origins occurrence =
        Origin.retained first before.declarations (before.rows occurrence) schedule.frame.assignment := by
      rw [← schedule.production_origin, productionOrigin, noBirth]
      rfl
    have actualRetained : some (Sum.inl occurrence) ∉ firing.selection.made := by
      rw [selection, ← current]
      exact made
    have row := schedule.native.retained_native_row_matches_input occupied firing occurrence actualRetained candidate pattern
    change Matches _ _ candidate pattern (firing.target.rows (some (cursor.current occurrence))) ↔ _
    rw [current, origin]
    have square : Assignment.compose (Assignment.compose candidate (schedule.native.producerCaller occupied firing)) schedule.frame.assignment =
        Assignment.compose (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
          schedule.native.guardNativeCaptures) schedule.native.bindingCaptures := by
      rw [schedule.native.producer_caller_assignment occupied firing candidate]
      exact (Assignment.compose_associative schedule.frame.assignment schedule.native.bindingCurrent _).symm
    change _ ↔ Matches first before.declarations
      (Assignment.compose (Assignment.compose candidate (schedule.native.producerCaller occupied firing)) schedule.frame.assignment)
      pattern (before.rows occurrence)
    rw [square]
    exact row

theorem producer_row_matches_source (source : schedule.Admitted)
    (rule : firing.rule = schedule.producer.rule) (selection : firing.selection = schedule.native.bindingSelection)
    (outputs : firing.outputs = schedule.producer.outputs occupied) (flags : firing.reusable = schedule.producerReusable)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches (ContextualPublication.privateFamily schedule.native.guardNativeBank firing.update.declaration) firing.target.declarations
        candidate pattern (firing.target.rows (schedule.native.producerPhysical occurrence)) ↔
      Matches last after.declarations (Assignment.compose candidate (schedule.native.producerCaller occupied firing)) pattern
        (after.rows occurrence) :=
  (schedule.producer_row_matches_origin occupied firing source rule selection outputs flags candidate pattern occurrence present).trans
    (schedule.origins_instances source next (Assignment.compose candidate (schedule.native.producerCaller occupied firing)) pattern occurrence)

theorem producer_world_equivalent (source : schedule.Admitted)
    (rule : firing.rule = schedule.producer.rule) (selection : firing.selection = schedule.native.bindingSelection)
    (outputs : firing.outputs = schedule.producer.outputs occupied) (flags : firing.reusable = schedule.producerReusable) :
    ContextualWorldComparison.Equivalent after (generator after.declarations)
      (schedule.native.producerProjection occupied firing) (schedule.native.producerCaller occupied firing) := by
  have parts := schedule.admitted_characterization.mp source
  exact schedule.native.world_equivalent_of_rows occupied firing parts.1 parts.2.1 schedule.producer.values rule selection _
    firing.target.rows (fun _ candidate pattern occurrence present =>
      schedule.producer_row_matches_source occupied firing source rule selection outputs flags candidate pattern occurrence present)

end Firing

/-- The actual constructed firing and its visible conditional world both
agree with the selected source body. The projection excludes control data
and decodes bound creation names; it is not full-inventory equality. -/
theorem source_iff_native_body (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : WithQueries schedule.native.guardNativeBank (schedule.native.nativeBindingState occupied),
        observed.firing.rule = schedule.producer.rule ∧ observed.firing.selection = schedule.native.bindingSelection ∧
          observed.firing.outputs = schedule.producer.outputs occupied ∧ observed.firing.reusable = schedule.producerReusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producer.queries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (schedule.native.producerProjection occupied observed.firing) (schedule.native.producerCaller occupied observed.firing) := by
  constructor
  · intro source
    obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
      (schedule.producer.source_iff_native_body_admission occupied fuel).mp source
    exact ⟨observed, rule, selection, outputs, flags, budget, queries,
      schedule.producer_world_equivalent occupied observed.firing source rule selection outputs flags⟩
  · rintro ⟨observed, rule, selection, outputs, flags, budget, queries, _equivalent⟩
    exact (schedule.producer.source_iff_native_body_admission occupied fuel).mpr
      ⟨observed, rule, selection, outputs, flags, budget, queries⟩

/-- The constructed invocation includes both the source/result comparison
and actual control consumption, even for a source body with no effects. -/
theorem source_iff_completed_invocation (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : ContextualPredicateQueryAdmission.WithQueries schedule.native.guardNativeBank (schedule.native.nativeBindingState occupied),
        observed.firing.rule = schedule.producer.rule ∧ observed.firing.selection = schedule.native.bindingSelection ∧
          observed.firing.outputs = schedule.producer.outputs occupied ∧ observed.firing.reusable = schedule.producerReusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producer.queries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (schedule.native.producerProjection occupied observed.firing) (schedule.native.producerCaller occupied observed.firing) ∧
          none ∉ observed.firing.target.present ∧
          ContextualNativeBodies.invocationPending observed.firing.target.present < ContextualNativeBodies.invocationPending (schedule.native.nativeBindingState occupied).present := by
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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
