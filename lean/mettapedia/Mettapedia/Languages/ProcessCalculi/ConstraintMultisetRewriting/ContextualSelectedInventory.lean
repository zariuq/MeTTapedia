import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

/-! # Selected executions retain exact symbolic outputs and all rule roots -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger
open ContextualSelectedNormalization ContextualExecutionCommutationNames
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : Endpoint locals O Γ sort}

namespace Interaction

private theorem frame_capture (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Assignment.compose (ContextualComputedFreshFrame.includeSource (interaction.prepared prior incoming).update)
      (ContextualSelectionViews.capturedTarget locals before.declarations) = intoCapture locals before.declarations := by
  funext name
  change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations) (Sum.inr name)) = _
  rw [instantiate_generator, ContextualFreshFrameScopeLedger.includeSource_image]
  rfl

private theorem frame_output (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Assignment.compose (ContextualComputedFreshFrame.includeSource (interaction.prepared prior incoming).update)
      (ContextualFreshening.assignment locals before.declarations interaction.scope) =
        intoCreated locals before.declarations interaction.scope := by
  funext name
  cases name with
  | inl name =>
      change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations)
        (Sum.inl (Mettapedia.Logic.LP.ScopedVar.at interaction.scope name))) = _
      rw [instantiate_generator, ContextualFreshFrameScopeLedger.includeSource_image]
      rfl
  | inr name =>
      change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations) (Sum.inr name)) = _
      rw [instantiate_generator, ContextualFreshFrameScopeLedger.includeSource_image]
      rfl

theorem target_rows (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) (occurrence : O) :
    (interaction.target prior incoming).inventory.rows occurrence =
      if occurrence ∈ interaction.made then .shared (instantiate (intoCreated locals before.declarations interaction.scope)
        (interaction.value occurrence))
      else (before.inventory.rows occurrence).map locals (intoCapture locals before.declarations) := by
  change ((ContextualActivatedStep.resultRows locals before.declarations interaction.selection interaction.outputs
    before.inventory.rows occurrence).map locals (ContextualComputedFreshFrame.includeSource
      (interaction.prepared prior incoming).update)) = _
  unfold ContextualActivatedStep.resultRows
  simp only [selection]
  split_ifs with member
  · change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose, frame_output interaction prior incoming]
  · rw [ContextualStoredRows.Row.map_compose, frame_capture]

def inputTerms (interaction : Interaction before) := interaction.taken.map interaction.label ++ interaction.read.map interaction.label

def rootValues {V : Type} (declaration : V → MetaArity S)
    (change : Assignment (ContextualSelectionViews.source locals before.declarations) declaration)
    (interaction : Interaction before) : List (Observation S declaration) :=
  interaction.inputTerms.map (observe ∘ Rigid.includeTerm declaration) ++
    interaction.made.map (fun occurrence => observe (instantiate change (interaction.value occurrence)))

theorem target_retained (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    (interaction.target prior incoming).inventory.retained =
      before.inventory.retained.map (instantiateObservation (intoCapture locals before.declarations)) ++
      interaction.rootValues (declarations locals before.declarations) (intoCreated locals before.declarations interaction.scope) := by
  change ((before.inventory.retained.map (instantiateObservation (ContextualSelectionViews.capturedTarget locals before.declarations))) ++
    ruleRoots (ContextualActivatedStep.prepared locals before.declarations before.occupied interaction.selection interaction.rule
      before.inventory.rows).rule).map (instantiateObservation (ContextualComputedFreshFrame.includeSource
        (interaction.prepared prior incoming).update)) = _
  rw [List.map_append, List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro value _member
    rw [Function.comp_apply, instantiateObservation_comp, frame_capture]
  · simp only [ruleRoots, ruleTerms, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
      ContextualFreshening.ruleAt, RuleInstance.map, rule, List.map_nil, List.append_nil, List.flatMap_nil,
      List.map_map, List.map_append, rootValues, inputTerms]
    apply congrArg₂ List.append
    · apply congrArg₂ List.append <;> apply List.map_congr_left
      all_goals
        intro occurrence _member
        change observe (instantiate _ (instantiate _ (Rigid.includeTerm _ _))) = _
        simp only [Rigid.instantiate_include]
        rfl
    · apply List.map_congr_left
      intro occurrence _member
      change observe (instantiate _ (instantiate _ _)) = _
      rw [← Assignment.instantiate_compose]
      exact congrArg (fun change => observe (instantiate change (interaction.value occurrence)))
        (frame_output interaction prior incoming)

theorem target_templates (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    (interaction.target prior incoming).inventory.templates =
      before.inventory.templates.map (instantiateObservation (ContextualStoredRows.liftCaptures locals
        (intoCapture locals before.declarations))) := by
  change (before.inventory.templates.map (instantiateObservation (ContextualStoredRows.liftCaptures locals
    (ContextualSelectionViews.capturedTarget locals before.declarations)))).map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals
        (ContextualComputedFreshFrame.includeSource (interaction.prepared prior incoming).update))) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose, frame_capture]

theorem captures_keep_scopes (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    Respects before.scopes (interaction.target prior incoming).scopes (intoCapture locals before.declarations) := by
  intro name
  change term (interaction.target prior incoming).scopes (generator _ (capture name)) ⊆ _
  rw [term_generator]
  exact Finset.Subset.refl _

theorem target_retains_ledger (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    before.occupied ⊆ (interaction.target prior incoming).occupied :=
  Finset.Subset.trans (ContextualActivationScopes.old_scopes_retained before.occupied interaction.selection)
    (ContextualFreshFrameScopeLedger.old_scopes_retained _)

theorem target_ledger (interaction : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior) :
    (interaction.target prior incoming).occupied = ContextualSelectedScopes.advance before.occupied
      (ContextualActivationScopes.count interaction.selection) := rfl

end Interaction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution
