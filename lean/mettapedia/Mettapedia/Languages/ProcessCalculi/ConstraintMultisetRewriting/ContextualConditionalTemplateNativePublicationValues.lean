import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateNativePublication

/-!
# Published conditional bodies decode from the actual native firing

The decoder binds only the dedicated output-hole declarations. Current
caller and original-cut declarations retain their source identities. Both
the schema value and its local equations use that same role assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule.NativePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    [DecidableEq First] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {schedule : Schedule S O Γ sort before after} {occupied : Finset Nat}

def decoder (publication : NativePublication schedule occupied) :
    Assignment publication.firing.target.declarations
      (ContextualSelectionViews.source publication.resultLocals publication.firing.target.declarations)
  | .inl (.inr ⟨.inr occurrence, name⟩) =>
      generator (ContextualSelectionViews.source publication.resultLocals publication.firing.target.declarations)
        (.inl ⟨some occurrence, name⟩)
  | identity =>
      generator (ContextualSelectionViews.source publication.resultLocals publication.firing.target.declarations) (.inr identity)

theorem returnGuard_image (publication : NativePublication schedule occupied)
    (identity : ContextualAnswerFamilies.Names schedule.guardVariables) :
    publication.returnGuard identity = generator publication.firing.target.declarations (.inl (.inr identity)) := by
  change instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (generator _ (.inr identity)) = _
  erw [instantiate_generator]
  exact ContextualFreshFrameScopeLedger.includeSource_image publication.firing.update _

theorem returnGuard_generator (publication : NativePublication schedule occupied)
    (identity : ContextualAnswerFamilies.Names schedule.guardVariables) :
    instantiate publication.returnGuard (generator schedule.guardFamily identity) =
      generator publication.firing.target.declarations (.inl (.inr identity)) := by
  exact (instantiate_generator publication.returnGuard identity).trans (publication.returnGuard_image identity)

theorem returnCurrent_image (publication : NativePublication schedule occupied) (name : after.Names) :
    publication.returnCurrent name = generator publication.firing.target.declarations (.inl (.inr ⟨.inl none, name⟩)) := by
  change instantiate publication.returnGuard (generator schedule.guardFamily ⟨.inl none, name⟩) = _
  exact publication.returnGuard_generator ⟨.inl none, name⟩

theorem actual_output_body (publication : NativePublication schedule occupied)
    (physical : OccurrenceAllocationRenaming.Name O) (made : some physical ∈ schedule.bindingSelection.made)
    (value : Term (signature S schedule.guardFamily) Γ sort)
    (selectedBody : schedule.outputBody (OccurrenceAllocationRenaming.erase physical) = some value) :
    instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
        (publication.firing.outputs (some physical)) = instantiate publication.returnGuard value := by
  rw [publication.values, schedule.producer_outputs_at occupied (some physical) made]
  simp only [producerCode, selectedBody, Option.map_some, Option.getD_some]
  have square : Assignment.compose
      (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
      (Assignment.compose (queryEmbedding schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)
        (ContextualSelectionViews.capturedSource schedule.bindingLocals schedule.guardFamily)) =
      ContextualSelectionViews.capturedTarget
        (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily := by
    funext name
    change instantiate
      (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
      (instantiate (queryEmbedding schedule.bindingLocals schedule.bindingLocals schedule.guardFamily)
        (generator (queryFamily schedule.bindingLocals schedule.guardFamily) (.inr name))) = _
    erw [instantiate_generator, instantiate_generator]
    rfl
  let frame := (ContextualClauseFrames.frame schedule.bindingLocals schedule.bindingLocals schedule.guardFamily occupied).assignment
  let query := queryEmbedding schedule.bindingLocals schedule.bindingLocals schedule.guardFamily
  let capture := ContextualSelectionViews.capturedSource schedule.bindingLocals schedule.guardFamily
  let target := ContextualSelectionViews.capturedTarget
    (ContextualClauseFrames.bank schedule.bindingLocals schedule.bindingLocals) schedule.guardFamily
  have inner : instantiate frame (instantiate query (instantiate capture value)) = instantiate target value := by
    calc
      _ = instantiate frame (instantiate (Assignment.compose query capture) value) :=
        congrArg (instantiate frame) (Assignment.instantiate_compose query capture value).symm
      _ = instantiate (Assignment.compose frame (Assignment.compose query capture)) value :=
        (Assignment.instantiate_compose frame (Assignment.compose query capture) value).symm
      _ = instantiate target value := congrArg (fun assignment => instantiate assignment value) square
  exact (congrArg (instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)) inner).trans
    (Assignment.instantiate_compose (ContextualComputedFreshFrame.includeSource publication.firing.update) target value).symm

set_option maxHeartbeats 800000 in
theorem output_role_square (publication : NativePublication schedule occupied) (occurrence : O) :
    Assignment.compose (Assignment.compose publication.decoder publication.returnGuard) (schedule.outputEnvironment occurrence) =
      Assignment.compose
        (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
          publication.firing.target.declarations (some occurrence))
        (ContextualStoredRows.liftCaptures (schedule.outputDeclarations occurrence) publication.returnCurrent) := by
  funext name
  change instantiate (Assignment.compose publication.decoder publication.returnGuard)
    (schedule.outputEnvironment occurrence name) = _
  rw [Assignment.instantiate_compose]
  cases name with
  | inl name =>
      change instantiate publication.decoder
        (instantiate publication.returnGuard (generator schedule.guardFamily ⟨.inr occurrence, name⟩)) = _
      erw [returnGuard_generator, instantiate_generator]
      change _ = instantiate
        (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
          publication.firing.target.declarations (some occurrence))
        (generator (ContextualSelectionViews.source (schedule.outputDeclarations occurrence) publication.firing.target.declarations)
          (.inl name))
      erw [instantiate_generator]
      rfl
  | inr name =>
      change instantiate publication.decoder
        (instantiate publication.returnGuard (generator schedule.guardFamily ⟨.inl none, name⟩)) = instantiate
        (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
          publication.firing.target.declarations (some occurrence))
        (instantiate (ContextualSelectionViews.capturedSource (schedule.outputDeclarations occurrence) publication.firing.target.declarations)
          (publication.returnCurrent name))
      rw [returnCurrent_image]
      erw [returnGuard_generator, instantiate_generator]
      dsimp only [decoder, ContextualSelectionViews.capturedSource]
      exact (instantiate_generator
        (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
          publication.firing.target.declarations (some occurrence))
        (.inr (.inl (.inr ⟨.inl none, name⟩)))).symm.trans
          (congrArg (instantiate
            (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
              publication.firing.target.declarations (some occurrence)))
            (instantiate_generator
              (ContextualSelectionViews.capturedSource (schedule.outputDeclarations occurrence)
                publication.firing.target.declarations)
              (.inl (.inr ⟨.inl none, name⟩)))).symm

theorem published_body_from_actual_output (publication : NativePublication schedule occupied)
    (physical : OccurrenceAllocationRenaming.Name O) (made : some physical ∈ schedule.bindingSelection.made)
    (row : Row (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations Γ sort)
    (selectedRow : schedule.outputRow (OccurrenceAllocationRenaming.erase physical) = some row) :
    instantiate publication.decoder
        (instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
          (publication.firing.outputs (some physical))) =
      ContextualStoredRows.asTemplate publication.resultLocals publication.firing.target.declarations
        (publication.target.rows (some physical)).value := by
  have selectedBody : schedule.outputBody (OccurrenceAllocationRenaming.erase physical) =
      some (instantiate (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical))
        (ContextualStoredRows.asTemplate _ _ row.value)) := by
    rw [outputBody, selectedRow]
    rfl
  rw [actual_output_body publication physical made _ selectedBody]
  change _ = ContextualStoredRows.asTemplate _ _ (publication.rows (some physical)).value
  simp only [rows, if_pos made, selectedRow]
  rw [ContextualConditionalRowPacking.template]
  change _ = instantiate _ (ContextualStoredRows.asTemplate _ _ (row.value.map _ publication.returnCurrent))
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    output_role_square]
  exact Assignment.instantiate_compose _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule.NativePublication
