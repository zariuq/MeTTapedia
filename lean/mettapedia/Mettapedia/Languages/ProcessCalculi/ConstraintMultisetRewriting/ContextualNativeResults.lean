import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeProducerAdmission

/-!
# The returned world of a native body firing

For every compiled body, an actual firing of its constructed rule returns
information whose models are exactly the source models, up to fresh
declarations, with the current caller fixed. Shared outputs follow that
caller, and retained entry rows keep their original conditional meaning.
The physical result is the source occurrence set under the authored
allocation names. Given the row meaning of a clause kind's publication
contract, the decoded visible world is source-equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body

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

def nativeBindingValue (body : Body S O Γ sort before after)
    (value : Term (signature S body.guardFamily) Γ sort) :
    Term (signature S (ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily)) Γ sort :=
  instantiate (ContextualSelectionViews.capturedTarget
    (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily) value

theorem native_binding_value_instances (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (value : Term (signature S body.guardFamily) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (body.nativeBindingInformation occupied produced guards)
        (body.nativeBindingValue value) next pattern ↔
      ContextualPublication.SourceInstances body.guardProblem value next pattern := by
  constructor
  · rintro ⟨extension, candidate, model, same⟩
    refine ⟨extension, Assignment.compose candidate
      (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals)
        body.guardFamily), body.native_binding_model_reflects occupied produced guards candidate model, ?_⟩
    exact (Assignment.instantiate_compose candidate _ value).trans same
  · rintro ⟨extension, candidate, model, same⟩
    obtain ⟨extra, combined, solved, fixed⟩ := body.native_binding_model_extends shapes resources occupied
      produced guards candidate model
    refine ⟨extension.trans extra, combined, solved, ?_⟩
    change instantiate combined (instantiate _ value) = _
    erw [← Assignment.instantiate_compose, fixed, Assignment.instantiate_compose,
      ContextualGuardMatching.Extension.trans_assignment, Assignment.instantiate_compose]
    exact congrArg (instantiate extra.assignment) same

theorem native_current_instances (body : Body S O Γ sort before after)
    (shapes : body.ShapesHold) (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (value : Term (signature S after.declarations) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (body.nativeBindingInformation occupied produced guards)
        (body.nativeBindingValue (instantiate body.bindingCurrent value)) next pattern ↔
      ContextualPublication.SourceInstances after.equations value next pattern := by
  rw [body.native_binding_value_instances shapes resources occupied produced guards _ pattern]
  have instances := ContextualIndependentProblems.instances_iff body.guardVariables body.guardDeclarations body.guardConditions
    (body.guard_blocks_solvable consistent) body.guardIndices (.inl none)
    body.guard_index_current_listed value pattern
  change ContextualPublication.SourceInstances body.guardProblem _ next pattern ↔
    ContextualPublication.SourceInstances body.currentProblem value next pattern at instances
  rw [body.current_problem_eq] at instances
  exact instances

theorem native_returned_current_model (body : Body S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort)))
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied))
    (rule : firing.rule = body.nativeBindingRule produced guards)
    (selection : firing.selection = body.bindingSelection)
    (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models
      (Assignment.compose
        (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
          (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily))
        body.bindingCurrent) after.equations := by
  have source := (ContextualResidual.models_mapProblem _ _ _).mp model
  have information : ContextualConditionalExecution.information
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily occupied
      firing.selection firing.rule (body.nativeBindingState occupied).rows (body.nativeBindingState occupied).equations =
      body.nativeBindingInformation occupied produced guards := by
    rw [rule, selection]
    rfl
  have native := (congrArg
    (ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))) information).mp source
  exact body.binding_current_model _
    (body.native_binding_model_reflects occupied produced guards _ native)

theorem shared_native_row_matches_current (body : Body S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied))
    (occurrence : Option (OccurrenceAllocationRenaming.Name O)) (made : occurrence ∈ firing.selection.made)
    (shared : firing.reusable occurrence = false) (value : Term (signature S after.declarations) Γ sort)
    (output : firing.outputs occurrence = body.nativeBindingValue (instantiate body.bindingCurrent value))
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      pattern = instantiate
        (Assignment.compose
          (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
            (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily))
          body.bindingCurrent) value := by
  rw [firing.shared_row occurrence made shared, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff, output]
  unfold nativeBindingValue
  erw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose]

theorem retained_native_row_matches_input (body : Body S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied))
    (occurrence : O) (retained : some (Sum.inl occurrence) ∉ firing.selection.made)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows (some (Sum.inl occurrence))) ↔
      Matches first before.declarations
        (Assignment.compose
          (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
            (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily))
          body.bindingCaptures) pattern (before.rows occurrence) := by
  rw [firing.retained_matches (some (Sum.inl occurrence)) retained next candidate pattern]
  change Matches (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) body.guardFamily
    _ pattern
    (ContextualConditionalPublication.extendPrivate body.bindingLocals body.bindingLocals body.guardFamily
      (body.bindingInput occurrence)) ↔ _
  erw [ContextualConditionalPublication.extendPrivate_matches_iff]
  rw [Assignment.compose_associative]
  exact body.binding_input_matches occurrence _ pattern

/-- Returned model statements have genuine instances: the target's fresh
helper declarations preserve the admitted input information's solvability. -/
theorem native_target_solvable (body : Body S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank body.bindingLocals body.bindingLocals) (body.nativeBindingState occupied)) :
    ContextualConditionalExecution.Solvable firing.target.equations := by
  let frame : ContextualGuardMatching.Extension
      (ContextualClauseFrames.nativeActive body.bindingLocals body.bindingLocals body.guardFamily) :=
    { Names := firing.target.Names
      declarations := firing.target.declarations
      name := Sum.inl
      injective := Sum.inl_injective
      preserves := fun _ => rfl }
  have assignment : frame.assignment = ContextualComputedFreshFrame.includeSource firing.update := by
    funext name
    exact (ContextualFreshFrameScopeLedger.includeSource_image firing.update name).symm
  change ContextualConditionalExecution.Solvable (ContextualResidual.mapProblem
    (ContextualComputedFreshFrame.includeSource firing.update) _)
  rw [← assignment]
  exact (ContextualConditionalNaturality.solvable_extension_iff frame _).mpr firing.admitted.solvable


def producerPhysical (body : Body S O Γ sort before after) (occurrence : O) : GuardPhysical O :=
  some ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current occurrence)

theorem producer_physical_injective (body : Body S O Γ sort before after) :
    Function.Injective body.producerPhysical :=
  fun _ _ same => (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).injective
    (Option.some.inj same)

section Firing

variable [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (body : Body S O Γ sort before after) (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing body.guardNativeBank (body.nativeBindingState occupied))

def producerCaller : Assignment after.declarations firing.target.declarations :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
    (Assignment.compose body.guardNativeCaptures body.bindingCurrent)

theorem producer_caller_assignment (candidate : Assignment firing.target.declarations next) :
    Assignment.compose candidate (body.producerCaller occupied firing) =
      Assignment.compose (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
        body.guardNativeCaptures) body.bindingCurrent := by
  unfold producerCaller
  erw [Assignment.compose_associative, Assignment.compose_associative]

theorem producer_result_physical (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (selection : firing.selection = body.bindingSelection) :
    firing.target.present = after.present.image body.producerPhysical := by
  have sets := body.binding_selection_sets
  have commit : body.bindingSelection.commit (T := Unit) =
      ⟨insert none (body.net.effect.taken.image some), body.net.effect.kept.image some, body.net.effect.made.image some, []⟩ := by
    change Commit.mk _ _ _ [] = _
    rw [sets.1, sets.2.1, sets.2.2]
  rw [firing.physical_result, selection, body.native_store_with_control occupied, commit, fire_with_control]
  have boundary : fire (before.present.image Sum.inl) body.net.effect = after.present.image
      (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current := by
    change fire _ (CompiledSchedule.compile _ _).effect = _
    rw [CompiledSchedule.compile_effect (body.allocated_resources_of_executable resources).1]
    exact (body.allocated_resources_of_executable resources).2
  rw [boundary, Finset.image_image]
  rfl

/-- The decoded visible world of a firing under a publication's rows. -/
def projectionOf {Local : Type} (locals : Local → MetaArity S)
    (rows : GuardPhysical O → Row locals firing.target.declarations Γ sort) :
    ContextualClauseSourceState.World locals O Γ sort where
  Names := firing.target.Names
  equality := firing.target.equality
  declarations := firing.target.declarations
  equations := firing.target.equations
  present := firing.target.present.biUnion fun physical =>
    match physical with
    | none => ∅
    | some name => {OccurrenceAllocationRenaming.erase name}
  rows occurrence := rows (body.producerPhysical occurrence)

/-- The decoded visible world under the firing's own published rows. -/
abbrev producerProjection :=
  body.projectionOf occupied firing (ContextualPublication.privateFamily body.guardNativeBank firing.update.declaration)
    firing.target.rows

theorem projection_physical (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (selection : firing.selection = body.bindingSelection) {Local : Type} (locals : Local → MetaArity S)
    (rows : GuardPhysical O → Row locals firing.target.declarations Γ sort) :
    (body.projectionOf occupied firing locals rows).present = after.present := by
  change (firing.target.present.biUnion _) = _
  rw [body.producer_result_physical occupied firing resources selection]
  ext occurrence
  constructor
  · intro member
    obtain ⟨physical, visible, decoded⟩ := Finset.mem_biUnion.mp member
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp visible
    change occurrence ∈ {OccurrenceAllocationRenaming.erase
      ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current original)} at decoded
    have same := Finset.mem_singleton.mp decoded
    rw [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).projects] at same
    exact same.symm ▸ present
  · intro member
    apply Finset.mem_biUnion.mpr
    refine ⟨body.producerPhysical occurrence, Finset.mem_image_of_mem _ member, ?_⟩
    change occurrence ∈ {OccurrenceAllocationRenaming.erase
      ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current occurrence)}
    rw [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).projects]
    exact Finset.mem_singleton_self _

theorem producer_projected_model
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (rule : firing.rule = body.nativeBindingRule produced []) (selection : firing.selection = body.bindingSelection)
    (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate (body.producerCaller occupied firing)) after.equations := by
  rw [body.producer_caller_assignment occupied firing candidate]
  exact body.native_returned_current_model occupied produced [] firing rule selection candidate model


theorem producer_source_model_extends (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (rule : firing.rule = body.nativeBindingRule produced []) (selection : firing.selection = body.bindingSelection)
    (candidate : Assignment after.declarations next) (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ other : Assignment firing.target.declarations extension.declarations,
        ContextualResidual.Models other firing.target.equations ∧
          Assignment.compose other (body.producerCaller occupied firing) = Assignment.compose extension.assignment candidate := by
  obtain ⟨earlier, native, nativeModel, fixed⟩ :=
    body.source_model_extends_native_binding shapes resources occupied produced [] candidate model
  let frame := firing.resultFrame
  let _ : DecidableEq frame.Names := firing.target.equality
  let extra := ContextualGuardMatching.Extension.withLocals frame.complementDeclarations earlier.declarations
  let other := frame.liftModel native
  have information : ContextualConditionalExecution.information body.guardNativeBank body.guardFamily occupied
      firing.selection firing.rule (body.nativeBindingState occupied).rows (body.nativeBindingState occupied).equations =
      body.nativeBindingInformation occupied produced [] := by
    rw [rule, selection]
    rfl
  have targetModel : ContextualResidual.Models other firing.target.equations := by
    change ContextualResidual.Models other (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource firing.update) _)
    rw [← firing.resultFrame_assignment]
    apply (ContextualConditionalNaturality.models_liftModel_iff frame native _).mpr
    erw [information]
    exact nativeModel
  let current := Assignment.compose body.guardNativeCaptures body.bindingCurrent
  have nativeCurrent : Assignment.compose native current = Assignment.compose earlier.assignment candidate :=
    (Assignment.compose_associative body.bindingCurrent body.guardNativeCaptures native).trans fixed
  have frameCurrent : body.producerCaller occupied firing = Assignment.compose frame.assignment current := by
    unfold producerCaller
    rw [firing.resultFrame_assignment]
    rfl
  have extraAssignment : extra.assignment = ContextualPrefixModels.inclusion frame.complementDeclarations earlier.declarations := by
    funext name
    rfl
  have frameSquare : Assignment.compose other frame.assignment = Assignment.compose extra.assignment native := by
    rw [extraAssignment]
    exact frame.liftModel_square native
  have projected : Assignment.compose other (body.producerCaller occupied firing) =
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

/-- A publication whose rows have the source row meaning at every present
occurrence returns a source-equivalent visible world. -/
theorem world_equivalent_of_rows (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (produced : List (Term (signature S (queryFamily body.bindingLocals body.guardFamily)) Γ sort))
    (rule : firing.rule = body.nativeBindingRule produced []) (selection : firing.selection = body.bindingSelection)
    {Local : Type} (locals : Local → MetaArity S)
    (rows : GuardPhysical O → Row locals firing.target.declarations Γ sort)
    (meaning : ∀ {Future : Type} (future : Future → MetaArity S)
      (candidate : Assignment firing.target.declarations future) (pattern : Term (signature S future) Γ sort)
      (occurrence : O), occurrence ∈ after.present →
        (Matches locals firing.target.declarations candidate pattern (rows (body.producerPhysical occurrence)) ↔
          Matches last after.declarations (Assignment.compose candidate (body.producerCaller occupied firing)) pattern
            (after.rows occurrence))) :
    ContextualWorldComparison.Equivalent after (generator after.declarations)
      (body.projectionOf occupied firing locals rows) (body.producerCaller occupied firing) := by
  have related {Future : Type} (future : Future → MetaArity S) (candidate : Assignment firing.target.declarations future)
      (model : ContextualResidual.Models candidate firing.target.equations) :
      ContextualWorldComparison.Related after (generator after.declarations)
        (body.projectionOf occupied firing locals rows) (body.producerCaller occupied firing)
        (Assignment.compose candidate (body.producerCaller occupied firing)) candidate := by
    refine ⟨body.producer_projected_model occupied firing produced rule selection candidate model, model,
      Assignment.compose_identity_right _, ?_⟩
    intro later pattern occurrence present
    erw [Assignment.compose_associative]
    exact (meaning _ (Assignment.compose later.assignment candidate) pattern occurrence present).symm
  refine ⟨(body.projection_physical occupied firing resources selection locals rows).symm, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨extension, other, targetModel, fixed⟩ :=
      body.producer_source_model_extends occupied firing shapes resources produced rule selection candidate model
    refine ⟨extension, other, ?_⟩
    have comparison := related _ other targetModel
    rw [fixed] at comparison
    exact comparison
  · intro Future future candidate model
    refine ⟨ContextualGuardMatching.Extension.identity future,
      Assignment.compose candidate (body.producerCaller occupied firing), ?_⟩
    change ContextualWorldComparison.Related after _ _ _ _ (Assignment.compose (generator future) candidate)
    rw [Assignment.compose_identity_left]
    exact related future candidate model

end Firing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies.Body
