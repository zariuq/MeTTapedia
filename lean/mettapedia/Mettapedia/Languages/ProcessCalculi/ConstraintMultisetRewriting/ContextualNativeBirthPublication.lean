import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBindingProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSurvivingProductions

/-!
# Native input binding retains independent creation-time output instances

The native port equations preserve every given compiled information model.
Consequently they neither add nor remove instances of a value in any saved
creation block. This comparison uses actual native information, including
the selected rows' latent conditions, without assuming successful guards.

The ordinary-output theorem applies the existing conditional producer's
row semantics to that comparison. It does not construct the full compiled
firing or claim the captured-template and program-context joins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def nativeBindingValue (schedule : Schedule S O Γ sort before after)
    (value : Term (signature S schedule.guardFamily) Γ sort) :
    Term (signature S (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)) Γ sort :=
  instantiate (ContextualSelectionViews.capturedTarget
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily) value

theorem native_binding_value_instances (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (value : Term (signature S schedule.guardFamily) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (schedule.nativeBindingInformation occupied produced guards)
        (schedule.nativeBindingValue value) next pattern ↔
      ContextualPublication.SourceInstances schedule.guardProblem value next pattern := by
  constructor
  · rintro ⟨extension, candidate, model, same⟩
    refine ⟨extension, Assignment.compose candidate
      (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals)
        schedule.guardFamily), schedule.native_binding_model_reflects occupied produced guards candidate model, ?_⟩
    exact (Assignment.instantiate_compose candidate _ value).trans same
  · rintro ⟨extension, candidate, model, same⟩
    obtain ⟨extra, combined, solved, fixed⟩ := schedule.native_binding_model_extends shapes resources occupied
      produced guards candidate model
    refine ⟨extension.trans extra, combined, solved, ?_⟩
    change instantiate combined (instantiate _ value) = _
    erw [← Assignment.instantiate_compose, fixed, Assignment.instantiate_compose,
      ContextualGuardMatching.Extension.trans_assignment, Assignment.instantiate_compose]
    exact congrArg (instantiate extra.assignment) same

def nativeBirthValue (schedule : Schedule S O Γ sort before after) (index : schedule.BirthIndex) :
    Term (signature S (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)) Γ sort :=
  schedule.nativeBindingValue
    (instantiate (ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inl (some index)))
      (schedule.births.get index).value)

/-- Other creation blocks, later caller information and selected input
conditions do not narrow this ordinary output's original instances. -/
theorem native_birth_instances (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (index : schedule.BirthIndex) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (schedule.nativeBindingInformation occupied produced guards)
        (schedule.nativeBirthValue index) next pattern ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern :=
  (schedule.native_binding_value_instances shapes resources occupied produced guards _ pattern).trans
    (ContextualIndependentProblems.instances_iff schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
      (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inl (some index))
      (schedule.guard_index_list_complete _) (schedule.births.get index).value pattern)

theorem native_current_instances (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (value : Term (signature S after.declarations) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (schedule.nativeBindingInformation occupied produced guards)
        (schedule.nativeBindingValue (instantiate schedule.bindingCurrent value)) next pattern ↔
      ContextualPublication.SourceInstances after.equations value next pattern := by
  rw [schedule.native_binding_value_instances shapes resources occupied produced guards _ pattern]
  have instances := ContextualIndependentProblems.instances_iff schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
    (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inl none)
    (schedule.guard_index_list_complete _) value pattern
  change ContextualPublication.SourceInstances schedule.guardProblem _ next pattern ↔
    ContextualPublication.SourceInstances schedule.currentProblem value next pattern at instances
  rw [currentProblem, ← schedule.final_equations] at instances
  exact instances

instance bindingVariableEquality (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] (index : Option O) : DecidableEq (schedule.bindingVariables index) := by
  cases index <;> dsimp only [bindingVariables] <;> infer_instance

theorem ordinary_native_row_matches_birth (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied))
    (rule : firing.rule = schedule.nativeBindingRule produced guards)
    (selection : firing.selection = schedule.bindingSelection)
    (occurrence : Option (OccurrenceAllocationRenaming.Name O)) (made : occurrence ∈ firing.selection.made)
    (ordinary : firing.reusable occurrence = true) (index : schedule.BirthIndex)
    (output : firing.outputs occurrence = schedule.nativeBirthValue index)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern := by
  rw [firing.ordinary_matches_source occurrence made ordinary next candidate pattern, rule, selection, output]
  exact schedule.native_birth_instances shapes resources consistent occupied produced guards index pattern

theorem native_returned_current_model (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (produced : List (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort))
    (guards : List (Check (Term (signature S (queryFamily schedule.bindingLocals schedule.guardFamily)) Γ sort)))
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied))
    (rule : firing.rule = schedule.nativeBindingRule produced guards)
    (selection : firing.selection = schedule.bindingSelection)
    (candidate : Assignment firing.target.declarations next)
    (model : ContextualResidual.Models candidate firing.target.equations) :
    ContextualResidual.Models
      (Assignment.compose
        (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
          (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
        schedule.bindingCurrent) after.equations := by
  have source := (ContextualResidual.models_mapProblem _ _ _).mp model
  have information : ContextualConditionalExecution.information
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily occupied
      firing.selection firing.rule (schedule.nativeBindingState occupied).rows (schedule.nativeBindingState occupied).equations =
      schedule.nativeBindingInformation occupied produced guards := by
    rw [rule, selection]
    rfl
  have native := (congrArg
    (ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))) information).mp source
  exact schedule.binding_current_model _
    (schedule.native_binding_model_reflects occupied produced guards _ native)

theorem shared_native_row_matches_current (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied))
    (occurrence : Option (OccurrenceAllocationRenaming.Name O)) (made : occurrence ∈ firing.selection.made)
    (shared : firing.reusable occurrence = false) (value : Term (signature S after.declarations) Γ sort)
    (output : firing.outputs occurrence = schedule.nativeBindingValue (instantiate schedule.bindingCurrent value))
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows occurrence) ↔
      pattern = instantiate
        (Assignment.compose
          (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
            (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
          schedule.bindingCurrent) value := by
  rw [firing.live_row occurrence made shared, ofStored_matches_iff, ContextualGuardMatching.live_matches_iff, output]
  unfold nativeBindingValue
  erw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose]

theorem retained_native_row_matches_input (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied))
    (occurrence : O) (retained : some (Sum.inl occurrence) ∉ firing.selection.made)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches
        (ContextualPublication.privateFamily
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) firing.update.declaration)
        firing.target.declarations candidate pattern (firing.target.rows (some (Sum.inl occurrence))) ↔
      Matches first before.declarations
        (Assignment.compose
          (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource firing.update))
            (ContextualSelectionViews.capturedTarget
              (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
          schedule.bindingCaptures) pattern (before.rows occurrence) := by
  rw [firing.retained_matches (some (Sum.inl occurrence)) retained next candidate pattern]
  change Matches (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily
    _ pattern
    (ContextualConditionalPublication.extendPrivate schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
      (schedule.bindingInput occurrence)) ↔ _
  erw [ContextualConditionalPublication.extendPrivate_matches_iff]
  rw [Assignment.compose_associative]
  exact schedule.binding_input_matches occurrence _ pattern

/-- Returned model statements have genuine instances: the target's fresh
helper declarations preserve the admitted input information's solvability. -/
theorem native_target_solvable (schedule : Schedule S O Γ sort before after)
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (occupied : Finset Nat)
    (firing : ContextualConditionalExecution.Firing
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) (schedule.nativeBindingState occupied)) :
    ContextualConditionalExecution.Solvable firing.target.equations := by
  let frame : ContextualGuardMatching.Extension
      (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) :=
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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
