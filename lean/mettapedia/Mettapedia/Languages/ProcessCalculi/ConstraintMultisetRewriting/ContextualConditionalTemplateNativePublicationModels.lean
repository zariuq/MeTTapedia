import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativePublication

/-!
# Actual producer publication preserves each source information model

Every given final source model extends through the constructed native
binding problem and the actual firing's returned declaration frame.
Conversely, every actual target model projects to source information.
The equations of dormant output schemas remain local metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule.NativePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}

def resultFrame (publication : NativePublication schedule occupied) :
    ContextualGuardMatching.Extension (ContextualClauseFrames.nativeActive schedule.bindingLocals schedule.bindingLocals schedule.guardFamily) where
  Names := publication.firing.target.Names
  declarations := publication.firing.target.declarations
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

theorem resultFrame_assignment (publication : NativePublication schedule occupied) :
    publication.resultFrame.assignment = ContextualComputedFreshFrame.includeSource publication.firing.update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image publication.firing.update name).symm

theorem actual_information (publication : NativePublication schedule occupied) :
    publication.target.equations = ContextualResidual.mapProblem
      (ContextualComputedFreshFrame.includeSource publication.firing.update)
      (schedule.nativeBindingInformation occupied schedule.producerValues []) := by
  have information : ContextualConditionalExecution.information
      (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals)
      (schedule.nativeBindingState occupied).declarations (schedule.nativeBindingState occupied).occupied
      publication.firing.selection publication.firing.rule
      (schedule.nativeBindingState occupied).rows (schedule.nativeBindingState occupied).equations =
      schedule.nativeBindingInformation occupied schedule.producerValues [] := by
    rw [publication.compiled, publication.selected]
    rfl
  exact congrArg (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource publication.firing.update)) information

theorem every_target_model_projects (publication : NativePublication schedule occupied)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next)
    (model : ContextualResidual.Models candidate publication.target.equations) :
    ContextualResidual.Models (Assignment.compose candidate publication.returnCurrent) after.equations := by
  rw [publication.actual_information] at model
  have raw := (ContextualResidual.models_mapProblem _ _ _).mp model
  have guarded := schedule.native_binding_model_reflects occupied schedule.producerValues [] _ raw
  have current := schedule.binding_current_model _ guarded
  have square : Assignment.compose candidate publication.returnCurrent =
      Assignment.compose
        (Assignment.compose (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource publication.firing.update))
          (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
        schedule.bindingCurrent := by
    exact (Assignment.compose_associative schedule.bindingCurrent publication.returnGuard candidate).trans
      (congrArg (fun assignment => Assignment.compose assignment schedule.bindingCurrent)
        (Assignment.compose_associative
          (ContextualSelectionViews.capturedTarget
            (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily)
          (ContextualComputedFreshFrame.includeSource publication.firing.update) candidate))
  exact square.symm ▸ current

theorem every_source_model_extends (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Executable
      ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment publication.firing.target.declarations extension.declarations,
        ContextualResidual.Models combined publication.target.equations ∧
          Assignment.compose combined publication.returnCurrent = Assignment.compose extension.assignment candidate := by
  obtain ⟨source, images, sourceModel, sourceCurrent⟩ :=
    schedule.source_model_extends_native_binding shapes resources occupied schedule.producerValues [] candidate model
  let extra := ContextualGuardMatching.Extension.withLocals publication.resultFrame.complementDeclarations source.declarations
  refine ⟨source.trans extra, publication.resultFrame.liftModel images, ?_, ?_⟩
  · rw [publication.actual_information, ← publication.resultFrame_assignment]
    exact (ContextualConditionalNaturality.models_liftModel_iff publication.resultFrame images _).mpr sourceModel
  · have lifted := publication.resultFrame.liftModel_square images
    rw [publication.resultFrame_assignment] at lifted
    change Assignment.compose (publication.resultFrame.liftModel images)
      (Assignment.compose (Assignment.compose (ContextualComputedFreshFrame.includeSource publication.firing.update)
        (ContextualSelectionViews.capturedTarget
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily))
        schedule.bindingCurrent) = _
    have fixed : Assignment.compose images
        (Assignment.compose (ContextualSelectionViews.capturedTarget
          (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily)
          schedule.bindingCurrent) = Assignment.compose source.assignment candidate :=
      (Assignment.compose_associative _ _ _).trans sourceCurrent
    erw [Assignment.compose_associative, Assignment.compose_associative, lifted,
      ← Assignment.compose_associative, ← Assignment.compose_associative, fixed,
      ContextualGuardMatching.Extension.trans_assignment, Assignment.compose_associative]
    rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule.NativePublication
