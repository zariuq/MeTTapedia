import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProgramExecution
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

def producerPhysical (schedule : Schedule S O Γ sort before after) (occurrence : O) : GuardPhysical O :=
  some ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)

theorem producer_physical_injective (schedule : Schedule S O Γ sort before after) :
    Function.Injective schedule.producerPhysical :=
  fun _ _ same => (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).injective
    (Option.some.inj same)

section Firing

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (schedule : Schedule S O Γ sort before after) (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing schedule.guardNativeBank (schedule.nativeBindingState occupied))

def producerCaller : Assignment after.declarations firing.target.declarations :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
    (Assignment.compose schedule.guardNativeCaptures schedule.bindingCurrent)

theorem producer_caller_assignment (candidate : Assignment firing.target.declarations next) :
    Assignment.compose candidate (schedule.producerCaller occupied firing) =
      Assignment.compose (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
        schedule.guardNativeCaptures) schedule.bindingCurrent := by
  unfold producerCaller
  erw [Assignment.compose_associative, Assignment.compose_associative]

theorem producer_result_physical (resources : Executable unitLabel before.present schedule.commits)
    (selection : firing.selection = schedule.bindingSelection) :
    firing.target.present = after.present.image schedule.producerPhysical := by
  have sets := schedule.binding_selection_sets
  have commit : schedule.bindingSelection.commit (T := Unit) =
      ⟨insert none (schedule.net.effect.taken.image some), schedule.net.effect.kept.image some, schedule.net.effect.made.image some, []⟩ := by
    change Commit.mk _ _ _ [] = _
    rw [sets.1, sets.2.1, sets.2.2]
  rw [firing.physical_result, selection, schedule.native_store_with_control occupied, commit, fire_with_control]
  have boundary := schedule.assembled_physical_of_resources resources
  change fire (before.present.image Sum.inl) schedule.net.effect = after.present.image
    (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current at boundary
  rw [boundary, Finset.image_image]
  rfl

theorem producer_row_matches_origin (source : schedule.Admitted)
    (rule : firing.rule = schedule.producerRule) (selection : firing.selection = schedule.bindingSelection)
    (outputs : firing.outputs = schedule.producerOutputs occupied) (flags : firing.reusable = schedule.producerReusable)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration) firing.target.declarations
        candidate pattern (firing.target.rows (schedule.producerPhysical occurrence)) ↔
      (schedule.origins occurrence).Instances (Assignment.compose candidate (schedule.producerCaller occupied firing)) pattern := by
  obtain ⟨shapes, resources, consistent, _guards⟩ := schedule.admitted_characterization.mp source
  let physical := schedule.producerPhysical occurrence
  by_cases made : physical ∈ schedule.bindingSelection.made
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
        (schedule.ordinary_native_row_matches_birth shapes resources consistent occupied schedule.producerValues []
          firing rule selection physical actualMade actualOrdinary index actualValue candidate pattern)
    · have shared : (schedule.births.get index).reusable = false := Bool.eq_false_iff.mpr ordinary
      have actualShared : firing.reusable physical = false := by rw [flags, flag, shared]
      have actualValue : firing.outputs physical =
          schedule.nativeBindingValue (instantiate schedule.bindingCurrent
            (instantiate (schedule.births.get index).transport (schedule.births.get index).value)) := by
        rw [outputs, value, producerBirthValue, shared]
        rfl
      simp only [Birth.origin, shared, Bool.false_eq_true, if_false, Origin.Instances]
      rw [schedule.producer_caller_assignment occupied firing candidate]
      exact schedule.shared_native_row_matches_current occupied firing physical actualMade actualShared
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
    have row := schedule.retained_native_row_matches_input occupied firing occurrence actualRetained candidate pattern
    change Matches _ _ candidate pattern (firing.target.rows (some (cursor.current occurrence))) ↔ _
    rw [current, origin]
    have square : Assignment.compose (Assignment.compose candidate (schedule.producerCaller occupied firing)) schedule.frame.assignment =
        Assignment.compose (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
          schedule.guardNativeCaptures) schedule.bindingCaptures := by
      rw [schedule.producer_caller_assignment occupied firing candidate]
      exact (Assignment.compose_associative schedule.frame.assignment schedule.bindingCurrent _).symm
    change _ ↔ Matches first before.declarations
      (Assignment.compose (Assignment.compose candidate (schedule.producerCaller occupied firing)) schedule.frame.assignment)
      pattern (before.rows occurrence)
    rw [square]
    exact row

theorem producer_row_matches_source (source : schedule.Admitted)
    (rule : firing.rule = schedule.producerRule) (selection : firing.selection = schedule.bindingSelection)
    (outputs : firing.outputs = schedule.producerOutputs occupied) (flags : firing.reusable = schedule.producerReusable)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort)
    (occurrence : O) (present : occurrence ∈ after.present) :
    Matches (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration) firing.target.declarations
        candidate pattern (firing.target.rows (schedule.producerPhysical occurrence)) ↔
      Matches last after.declarations (Assignment.compose candidate (schedule.producerCaller occupied firing)) pattern
        (after.rows occurrence) :=
  (schedule.producer_row_matches_origin occupied firing source rule selection outputs flags candidate pattern occurrence present).trans
    (schedule.origins_instances source next (Assignment.compose candidate (schedule.producerCaller occupied firing)) pattern occurrence)

def producerProjection : ContextualClauseSourceState.World
    (ContextualPublication.privateFamily schedule.guardNativeBank firing.update.declaration) O Γ sort where
  Names := firing.target.Names
  equality := firing.target.equality
  declarations := firing.target.declarations
  equations := firing.target.equations
  present := firing.target.present.biUnion fun physical =>
    match physical with
    | none => ∅
    | some name => {OccurrenceAllocationRenaming.erase name}
  rows occurrence := firing.target.rows (schedule.producerPhysical occurrence)

theorem producer_projection_physical (resources : Executable unitLabel before.present schedule.commits)
    (selection : firing.selection = schedule.bindingSelection) :
    (schedule.producerProjection occupied firing).present = after.present := by
  change (firing.target.present.biUnion _) = _
  rw [schedule.producer_result_physical occupied firing resources selection]
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

theorem producer_projected_model (rule : firing.rule = schedule.producerRule)
    (selection : firing.selection = schedule.bindingSelection) (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate (schedule.producerCaller occupied firing)) after.equations := by
  rw [schedule.producer_caller_assignment occupied firing candidate]
  exact schedule.native_returned_current_model occupied schedule.producerValues [] firing rule selection candidate model

theorem producer_related (source : schedule.Admitted)
    (rule : firing.rule = schedule.producerRule) (selection : firing.selection = schedule.bindingSelection)
    (outputs : firing.outputs = schedule.producerOutputs occupied) (flags : firing.reusable = schedule.producerReusable)
    (candidate : Assignment firing.target.declarations next) (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualWorldComparison.Related after (generator after.declarations)
      (schedule.producerProjection occupied firing) (schedule.producerCaller occupied firing)
      (Assignment.compose candidate (schedule.producerCaller occupied firing)) candidate := by
  refine ⟨schedule.producer_projected_model occupied firing rule selection candidate model, model,
    Assignment.compose_identity_right _, ?_⟩
  intro later pattern occurrence present
  erw [Assignment.compose_associative]
  exact (schedule.producer_row_matches_source occupied firing source rule selection outputs flags
    (Assignment.compose later.assignment candidate) pattern occurrence present).symm

private def producerResultFrame : ContextualGuardMatching.Extension schedule.guardNativeFamily where
  Names := firing.target.Names
  declarations := firing.target.declarations
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

private theorem producer_result_frame_assignment :
    (producerResultFrame schedule occupied firing).assignment = ContextualComputedFreshFrame.includeSource firing.update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image firing.update name).symm

theorem producer_source_model_extends (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits)
    (rule : firing.rule = schedule.producerRule) (selection : firing.selection = schedule.bindingSelection)
    (candidate : Assignment after.declarations next) (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ other : Assignment firing.target.declarations extension.declarations,
        ContextualResidual.Models other firing.target.equations ∧
          Assignment.compose other (schedule.producerCaller occupied firing) = Assignment.compose extension.assignment candidate := by
  obtain ⟨earlier, native, nativeModel, fixed⟩ :=
    schedule.source_model_extends_native_binding shapes resources occupied schedule.producerValues [] candidate model
  let frame := producerResultFrame schedule occupied firing
  let _ : DecidableEq frame.Names := firing.target.equality
  let extra := ContextualGuardMatching.Extension.withLocals frame.complementDeclarations earlier.declarations
  let other := frame.liftModel native
  have information : ContextualConditionalExecution.information schedule.guardNativeBank schedule.guardFamily occupied
      firing.selection firing.rule (schedule.nativeBindingState occupied).rows (schedule.nativeBindingState occupied).equations =
      schedule.nativeBindingInformation occupied schedule.producerValues [] := by
    rw [rule, selection]
    rfl
  have targetModel : ContextualResidual.Models other firing.target.equations := by
    change ContextualResidual.Models other (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource firing.update) _)
    rw [← producer_result_frame_assignment schedule occupied firing]
    apply (ContextualConditionalNaturality.models_liftModel_iff frame native _).mpr
    erw [information]
    exact nativeModel
  let current := Assignment.compose schedule.guardNativeCaptures schedule.bindingCurrent
  have nativeCurrent : Assignment.compose native current = Assignment.compose earlier.assignment candidate :=
    (Assignment.compose_associative schedule.bindingCurrent schedule.guardNativeCaptures native).trans fixed
  have frameCurrent : schedule.producerCaller occupied firing = Assignment.compose frame.assignment current := by
    unfold producerCaller
    rw [producer_result_frame_assignment schedule occupied firing]
    rfl
  have extraAssignment : extra.assignment = ContextualPrefixModels.inclusion frame.complementDeclarations earlier.declarations := by
    funext name
    rfl
  have frameSquare : Assignment.compose other frame.assignment = Assignment.compose extra.assignment native := by
    rw [extraAssignment]
    exact frame.liftModel_square native
  have projected : Assignment.compose other (schedule.producerCaller occupied firing) =
      Assignment.compose (earlier.trans extra).assignment candidate := by
    rw [frameCurrent]
    have first := Assignment.compose_associative current frame.assignment other
    have second := congrArg (fun images => Assignment.compose images current) frameSquare
    have third := (Assignment.compose_associative current native extra.assignment).symm
    have fourth := congrArg (Assignment.compose extra.assignment) nativeCurrent
    have fifth := Assignment.compose_associative candidate earlier.assignment extra.assignment
    have sixth := congrArg (fun images => Assignment.compose images candidate)
      (ContextualGuardMatching.Extension.trans_assignment earlier extra).symm
    exact first.trans (second.trans (third.trans (fourth.trans (fifth.trans sixth))))
  exact ⟨earlier.trans extra, other, targetModel, projected⟩

theorem producer_world_equivalent (source : schedule.Admitted)
    (rule : firing.rule = schedule.producerRule) (selection : firing.selection = schedule.bindingSelection)
    (outputs : firing.outputs = schedule.producerOutputs occupied) (flags : firing.reusable = schedule.producerReusable) :
    ContextualWorldComparison.Equivalent after (generator after.declarations)
      (schedule.producerProjection occupied firing) (schedule.producerCaller occupied firing) := by
  have parts := schedule.admitted_characterization.mp source
  refine ⟨(schedule.producer_projection_physical occupied firing parts.2.1 selection).symm, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨extension, other, targetModel, fixed⟩ :=
      schedule.producer_source_model_extends occupied firing parts.1 parts.2.1 rule selection candidate model
    refine ⟨extension, other, ?_⟩
    have related := schedule.producer_related occupied firing source rule selection outputs flags other targetModel
    rw [fixed] at related
    exact related
  · intro Future future candidate model
    refine ⟨ContextualGuardMatching.Extension.identity future,
      Assignment.compose candidate (schedule.producerCaller occupied firing), ?_⟩
    change ContextualWorldComparison.Related after _ _ _ _ (Assignment.compose (generator future) candidate)
    rw [Assignment.compose_identity_left]
    exact schedule.producer_related occupied firing source rule selection outputs flags candidate model

end Firing

/-- The actual constructed firing and its visible conditional world both
agree with the selected source body. The projection excludes control data
and decodes bound creation names; it is not full-inventory equality. -/
theorem source_iff_native_body (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat) (fuel : Nat) :
    schedule.Admitted ↔
      ∃ observed : WithQueries schedule.guardNativeBank (schedule.nativeBindingState occupied),
        observed.firing.rule = schedule.producerRule ∧ observed.firing.selection = schedule.bindingSelection ∧
          observed.firing.outputs = schedule.producerOutputs occupied ∧ observed.firing.reusable = schedule.producerReusable ∧
          observed.firing.fuel = fuel ∧ observed.queries = schedule.producerQueries occupied ∧
          ContextualWorldComparison.Equivalent after (generator after.declarations)
            (schedule.producerProjection occupied observed.firing) (schedule.producerCaller occupied observed.firing) := by
  constructor
  · intro source
    obtain ⟨observed, rule, selection, outputs, flags, budget, queries⟩ :=
      (schedule.source_iff_native_body_admission occupied fuel).mp source
    exact ⟨observed, rule, selection, outputs, flags, budget, queries,
      schedule.producer_world_equivalent occupied observed.firing source rule selection outputs flags⟩
  · rintro ⟨observed, rule, selection, outputs, flags, budget, queries, _equivalent⟩
    exact (schedule.source_iff_native_body_admission occupied fuel).mpr
      ⟨observed, rule, selection, outputs, flags, budget, queries⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
