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
  | .inl (.inr ⟨.inl (some occurrence), name⟩) =>
      generator (ContextualSelectionViews.source publication.resultLocals publication.firing.target.declarations)
        (.inl ⟨some occurrence, name⟩)
  | identity =>
      generator (ContextualSelectionViews.source publication.resultLocals publication.firing.target.declarations) (.inr identity)

theorem returnGuard_image (publication : NativePublication schedule occupied)
    (identity : ContextualAnswerFamilies.Names schedule.native.guardVariables) :
    publication.returnGuard identity = generator publication.firing.target.declarations (.inl (.inr identity)) := by
  change instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (generator _ (.inr identity)) = _
  erw [instantiate_generator]
  exact ContextualFreshFrameScopeLedger.includeSource_image publication.firing.update _

theorem returnGuard_generator (publication : NativePublication schedule occupied)
    (identity : ContextualAnswerFamilies.Names schedule.native.guardVariables) :
    instantiate publication.returnGuard (generator schedule.native.guardFamily identity) =
      generator publication.firing.target.declarations (.inl (.inr identity)) := by
  exact (instantiate_generator publication.returnGuard identity).trans (publication.returnGuard_image identity)

theorem producerCaller_image (publication : NativePublication schedule occupied) (name : after.Names) :
    publication.producerCaller name = generator publication.firing.target.declarations (.inl (.inr ⟨.inl none, name⟩)) := by
  change instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (instantiate (ContextualSelectionViews.capturedTarget
      (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) schedule.native.guardFamily)
      (generator schedule.native.guardFamily ⟨.inl none, name⟩)) = _
  exact (Assignment.instantiate_compose
    (ContextualComputedFreshFrame.includeSource publication.firing.update)
    (ContextualSelectionViews.capturedTarget
      (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) schedule.native.guardFamily)
    (generator schedule.native.guardFamily ⟨.inl none, name⟩)).symm.trans
      (publication.returnGuard_generator ⟨.inl none, name⟩)

theorem actual_output_body (publication : NativePublication schedule occupied)
    (physical : OccurrenceAllocationRenaming.Name O) (made : some physical ∈ schedule.native.bindingSelection.made)
    (value : Term (signature S schedule.native.guardFamily) Γ sort)
    (selectedBody : schedule.outputBody (OccurrenceAllocationRenaming.erase physical) = some value) :
    instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update)
        (publication.firing.outputs (some physical)) = instantiate publication.returnGuard value := by
  rw [publication.values, schedule.producer.outputs_at occupied (some physical) made]
  simp only [producer, producerCode, selectedBody, Option.map_some, Option.getD_some]
  have square : Assignment.compose
      (ContextualClauseFrames.frame schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily occupied).assignment
      (Assignment.compose (queryEmbedding schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)
        (ContextualSelectionViews.capturedSource schedule.native.bindingLocals schedule.native.guardFamily)) =
      ContextualSelectionViews.capturedTarget
        (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) schedule.native.guardFamily := by
    funext name
    change instantiate
      (ContextualClauseFrames.frame schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily occupied).assignment
      (instantiate (queryEmbedding schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)
        (generator (queryFamily schedule.native.bindingLocals schedule.native.guardFamily) (.inr name))) = _
    erw [instantiate_generator, instantiate_generator]
    rfl
  let frame := (ContextualClauseFrames.frame schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily occupied).assignment
  let query := queryEmbedding schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily
  let capture := ContextualSelectionViews.capturedSource schedule.native.bindingLocals schedule.native.guardFamily
  let target := ContextualSelectionViews.capturedTarget
    (ContextualClauseFrames.bank schedule.native.bindingLocals schedule.native.bindingLocals) schedule.native.guardFamily
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
        (ContextualStoredRows.liftCaptures (schedule.outputDeclarations occurrence) publication.producerCaller) := by
  funext name
  change instantiate (Assignment.compose publication.decoder publication.returnGuard)
    (schedule.outputEnvironment occurrence name) = _
  rw [Assignment.instantiate_compose]
  cases name with
  | inl name =>
      change instantiate publication.decoder
        (instantiate publication.returnGuard (generator schedule.native.guardFamily ⟨.inl (some occurrence), name⟩)) = _
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
        (instantiate publication.returnGuard (generator schedule.native.guardFamily ⟨.inl none, name⟩)) = instantiate
        (ContextualConditionalRowPacking.inclusion publication.PrivateNames publication.privateDeclarations
          publication.firing.target.declarations (some occurrence))
        (instantiate (ContextualSelectionViews.capturedSource (schedule.outputDeclarations occurrence) publication.firing.target.declarations)
          (publication.producerCaller name))
      rw [producerCaller_image]
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

/-- Embedding recipe-private names and transporting captures decodes the
same actual names as the native output decoder. -/
theorem recipe_decoder_square (publication : NativePublication schedule occupied)
    (isSchema : Bool) (conditions : ContextualResidual.Problem schedule.native.guardFamily) :
    Assignment.compose
        (ContextualStoredRows.liftCaptures publication.resultLocals
          (ContextualComputedFreshFrame.includeSource publication.firing.update))
        (publication.embedRecipe (schedule.producerRecipe isSchema conditions)).assignment =
      Assignment.compose publication.decoder
        (ContextualComputedFreshFrame.includeSource publication.firing.update) := by
  funext identity
  cases identity with
  | inl name =>
      change instantiate (ContextualStoredRows.liftCaptures publication.resultLocals (ContextualComputedFreshFrame.includeSource publication.firing.update)) (generator (ContextualSelectionViews.source publication.resultLocals (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)) (.inr (.inl name))) =
        instantiate publication.decoder (ContextualComputedFreshFrame.includeSource publication.firing.update (.inl name))
      rw [ContextualFreshFrameScopeLedger.includeSource_image]
      erw [instantiate_generator, instantiate_generator]
      change instantiate (ContextualSelectionViews.capturedSource publication.resultLocals _)
        (ContextualComputedFreshFrame.includeSource publication.firing.update (.inl name)) = _
      rw [ContextualFreshFrameScopeLedger.includeSource_image]
      exact instantiate_generator _ _
  | inr identity =>
      rcases identity with ⟨block, name⟩
      cases block with
      | inl output =>
          cases output with
          | none =>
              change instantiate (ContextualStoredRows.liftCaptures publication.resultLocals (ContextualComputedFreshFrame.includeSource publication.firing.update)) (generator (ContextualSelectionViews.source publication.resultLocals (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)) (.inr (.inr ⟨.inl none, name⟩))) =
                instantiate publication.decoder (ContextualComputedFreshFrame.includeSource publication.firing.update (.inr ⟨.inl none, name⟩))
              rw [ContextualFreshFrameScopeLedger.includeSource_image]
              erw [instantiate_generator, instantiate_generator]
              change instantiate (ContextualSelectionViews.capturedSource publication.resultLocals _)
                (ContextualComputedFreshFrame.includeSource publication.firing.update (.inr ⟨.inl none, name⟩)) = _
              rw [ContextualFreshFrameScopeLedger.includeSource_image]
              exact instantiate_generator _ _
          | some occurrence =>
              change instantiate (ContextualStoredRows.liftCaptures publication.resultLocals (ContextualComputedFreshFrame.includeSource publication.firing.update)) (generator (ContextualSelectionViews.source publication.resultLocals (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)) (.inl ⟨some occurrence, name⟩)) =
                instantiate publication.decoder (ContextualComputedFreshFrame.includeSource publication.firing.update (.inr ⟨.inl (some occurrence), name⟩))
              rw [ContextualFreshFrameScopeLedger.includeSource_image]
              erw [instantiate_generator, instantiate_generator]
              rfl
      | inr cut =>
          change instantiate (ContextualStoredRows.liftCaptures publication.resultLocals (ContextualComputedFreshFrame.includeSource publication.firing.update)) (generator (ContextualSelectionViews.source publication.resultLocals (ContextualClauseFrames.nativeActive schedule.native.bindingLocals schedule.native.bindingLocals schedule.native.guardFamily)) (.inr (.inr ⟨.inr cut, name⟩))) =
            instantiate publication.decoder (ContextualComputedFreshFrame.includeSource publication.firing.update (.inr ⟨.inr cut, name⟩))
          rw [ContextualFreshFrameScopeLedger.includeSource_image]
          erw [instantiate_generator, instantiate_generator]
          change instantiate (ContextualSelectionViews.capturedSource publication.resultLocals _)
            (ContextualComputedFreshFrame.includeSource publication.firing.update (.inr ⟨.inr cut, name⟩)) = _
          rw [ContextualFreshFrameScopeLedger.includeSource_image]
          exact instantiate_generator _ _

theorem recipe_schema_body (publication : NativePublication schedule occupied)
    (conditions : ContextualResidual.Problem schedule.native.guardFamily)
    (emitted : Term (signature S (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
      schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort) :
    ((publication.embedRecipe (schedule.producerRecipe true conditions)).publish
      (ContextualComputedFreshFrame.includeSource publication.firing.update) emitted).value =
      .schema (instantiate publication.decoder
        (instantiate (ContextualComputedFreshFrame.includeSource publication.firing.update) emitted)) := by
  change ContextualStoredRows.Row.schema (instantiate _ (instantiate _ emitted)) = _
  rw [← Assignment.instantiate_compose]
  erw [publication.recipe_decoder_square true conditions]
  erw [Assignment.instantiate_compose]
  rfl

theorem recipe_conditions (publication : NativePublication schedule occupied)
    (isSchema : Bool) (conditions : ContextualResidual.Problem schedule.native.guardFamily)
    (emitted : Term (signature S (ContextualClauseFrames.nativeActive schedule.native.bindingLocals
      schedule.native.bindingLocals schedule.native.guardFamily)) Γ sort) :
    ((publication.embedRecipe (schedule.producerRecipe isSchema conditions)).publish
      (ContextualComputedFreshFrame.includeSource publication.firing.update) emitted).obligations =
      ContextualResidual.mapProblem publication.decoder
        (ContextualResidual.mapProblem publication.returnGuard conditions) := by
  change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _
    (ContextualResidual.mapProblem _ conditions)) = _
  rw [ContextualConditionalNaturality.map_problem_compose]
  erw [publication.recipe_decoder_square isSchema conditions]
  erw [ContextualConditionalNaturality.map_problem_compose, ← Assignment.compose_associative]
  exact (ContextualConditionalNaturality.map_problem_compose publication.returnGuard publication.decoder conditions).symm

set_option maxHeartbeats 800000 in
/-- A produced row, including its schema/shared constructor and local
conditions, is reconstructed from the actual output and its recipe. -/
theorem row_from_actual_output (publication : NativePublication schedule occupied)
    (physical : OccurrenceAllocationRenaming.Name O) (made : some physical ∈ schedule.native.bindingSelection.made)
    (row : Row (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations Γ sort)
    (selectedRow : schedule.outputRow (OccurrenceAllocationRenaming.erase physical) = some row) :
    publication.rows (some physical) =
      ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
        publication.firing.target.declarations (some (OccurrenceAllocationRenaming.erase physical))
        (row.map _ _ publication.producerCaller) := by
  have selectedBody : schedule.outputBody (OccurrenceAllocationRenaming.erase physical) =
      some (instantiate (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical))
        (ContextualStoredRows.asTemplate _ _ row.value)) := by
    rw [outputBody, selectedRow]
    rfl
  have emitted := publication.actual_output_body physical made _ selectedBody
  simp only [rows, ContextualConditionalRowPacking.publishWithFallback, producerRecipes, if_pos made, selectedRow, Option.map_some]
  have conditions (isSchema : Bool) :
      ((publication.embedRecipe (schedule.producerRecipe isSchema
          (ContextualResidual.mapProblem (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical)) row.obligations))).publish
        (ContextualComputedFreshFrame.includeSource publication.firing.update)
        (publication.firing.outputs (some physical))).obligations =
      (ContextualConditionalRowPacking.pack publication.PrivateNames publication.privateDeclarations
        publication.firing.target.declarations (some (OccurrenceAllocationRenaming.erase physical))
        (row.map _ _ publication.producerCaller)).obligations := by
    erw [recipe_conditions]
    change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _
      (ContextualResidual.mapProblem _ row.obligations)) =
      ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ row.obligations)
    rw [ContextualConditionalNaturality.map_problem_compose,
      ContextualConditionalNaturality.map_problem_compose, output_role_square]
    exact (ContextualConditionalNaturality.map_problem_compose _ _ row.obligations).symm
  rcases row with ⟨value, obligations⟩
  cases value with
  | schema body =>
      change Row.mk _ _ = Row.mk _ _
      congr 1
      · have actual := publication.recipe_schema_body
          (ContextualResidual.mapProblem (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical)) obligations)
          (publication.firing.outputs (some physical))
        refine actual.trans ?_
        rw [emitted]
        change ContextualStoredRows.Row.schema (instantiate _ (instantiate _ (instantiate _ body))) =
          ContextualStoredRows.Row.schema (instantiate _ (instantiate _ body))
        rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
          output_role_square, Assignment.instantiate_compose]
      · exact conditions true
  | shared value =>
      change Row.mk _ _ = Row.mk _ _
      congr 1
      · change ContextualStoredRows.Row.shared (instantiate _ (publication.firing.outputs (some physical))) =
          ContextualStoredRows.Row.shared (instantiate publication.producerCaller value)
        rw [emitted]
        have square : Assignment.compose
            (Assignment.compose publication.returnGuard (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical)))
            (ContextualSelectionViews.capturedSource (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations) =
            publication.producerCaller := by
          funext name
          change instantiate
            (Assignment.compose publication.returnGuard (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase physical)))
            (generator (ContextualSelectionViews.source (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations) (.inr name)) = _
          erw [instantiate_generator]
          change instantiate publication.returnGuard (generator _ ⟨.inl none, name⟩) = _
          rw [returnGuard_generator, producerCaller_image]
        change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ (instantiate _ value))) = _
        rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, square]
      · exact conditions false

theorem published_body_from_actual_output (publication : NativePublication schedule occupied)
    (physical : OccurrenceAllocationRenaming.Name O) (made : some physical ∈ schedule.native.bindingSelection.made)
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
  rw [publication.row_from_actual_output physical made row selectedRow]
  rw [ContextualConditionalRowPacking.template]
  change _ = instantiate _ (ContextualStoredRows.asTemplate _ _ (row.value.map _ publication.producerCaller))
  rw [ContextualStoredRows.asTemplate_map, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose,
    output_role_square]
  exact Assignment.instantiate_compose _ _ _

/-- Every genuine net output has a saved birth, hence an explicit recipe.
No fallback raw row is used for a successfully compiled body's output. -/
theorem recipes_cover_outputs (publication : NativePublication schedule occupied)
    (shapes : schedule.ShapesHold)
    (resources : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Executable
      ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (physical : Option (OccurrenceAllocationRenaming.Name O))
    (made : physical ∈ publication.firing.selection.made) :
    ∃ recipe, publication.recipes physical = some recipe := by
  have nativeMade : physical ∈ schedule.native.bindingSelection.made := by
    rwa [publication.selected] at made
  obtain ⟨name, member, rfl⟩ := List.mem_map.mp nativeMade
  have output : name ∈ schedule.net.effect.made := Finset.mem_toList.mp member
  obtain ⟨occurrence, _present, birth, _current, selected, erased⟩ :=
    schedule.net_output_has_birth shapes resources name output
  have existsRow := (schedule.output_row_exists_iff (OccurrenceAllocationRenaming.erase name)).mpr
    (by rw [erased]; exact ⟨birth, selected⟩)
  obtain ⟨row, selectedRow⟩ := existsRow
  refine ⟨publication.embedRecipe (schedule.producerRecipe
    (match row.value with | .schema _ => true | .shared _ => false)
    (ContextualResidual.mapProblem (schedule.outputEnvironment (OccurrenceAllocationRenaming.erase name)) row.obligations)), ?_⟩
  simp only [recipes, producerRecipes, if_pos nativeMade, selectedRow, Option.map_some]
  rfl

theorem output_matches (publication : NativePublication schedule occupied) (physical : OccurrenceAllocationRenaming.Name O)
    (made : some physical ∈ schedule.native.bindingSelection.made)
    (row : Row (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations Γ sort)
    (selectedRow : schedule.outputRow (OccurrenceAllocationRenaming.erase physical) = some row)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment publication.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches publication.resultLocals publication.firing.target.declarations candidate pattern
        (publication.target.rows (some physical)) ↔
      Matches (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations
        (Assignment.compose candidate publication.producerCaller) pattern row := by
  change Matches _ _ candidate pattern (publication.rows (some physical)) ↔ _
  rw [publication.row_from_actual_output physical made row selectedRow]
  exact (ContextualConditionalRowPacking.matches_iff publication.PrivateNames publication.privateDeclarations
    publication.firing.target.declarations (some (OccurrenceAllocationRenaming.erase physical)) _ candidate pattern).trans
      (matches_map_iff (schedule.outputDeclarations (OccurrenceAllocationRenaming.erase physical)) after.declarations
        publication.producerCaller candidate pattern row)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule.NativePublication
