import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationProducers

/-! # Exact source inventories of the symbolic-producer commutation profile -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport ContextualWorldScopeLedger
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : Endpoint locals O Γ sort}

namespace Producer

private theorem frame_capture (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    Assignment.compose (ContextualComputedFreshFrame.includeSource (producer.prepared empty).update)
      (ContextualSelectionViews.capturedTarget locals before.declarations) =
        ContextualExecutionCommutationNames.intoCapture locals before.declarations := by
  funext name
  change instantiate _ (generator _ (Sum.inr name)) = _
  rw [instantiate_generator]
  rw [ContextualFreshFrameScopeLedger.includeSource_image]
  rfl

private theorem frame_output (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    Assignment.compose (ContextualComputedFreshFrame.includeSource (producer.prepared empty).update)
      (ContextualFreshening.assignment locals before.declarations producer.scope) =
        ContextualExecutionCommutationNames.intoCreated locals before.declarations producer.scope := by
  funext name
  cases name with
  | inl name =>
      change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations)
        (Sum.inl (Mettapedia.Logic.LP.ScopedVar.at producer.scope name))) = _
      rw [instantiate_generator]
      rw [ContextualFreshFrameScopeLedger.includeSource_image]
      rfl
  | inr name =>
      change instantiate _ (generator (ContextualActivatedStep.target locals before.declarations) (Sum.inr name)) = _
      rw [instantiate_generator]
      rw [ContextualFreshFrameScopeLedger.includeSource_image]
      rfl

theorem target_rows (producer : Producer before) (empty : before.inventory.configuration.equations = []) (occurrence : O) :
    (producer.target empty).inventory.rows occurrence =
      if occurrence ∈ producer.made then .shared
        (instantiate (ContextualExecutionCommutationNames.intoCreated locals before.declarations producer.scope)
          (producer.value occurrence))
      else (before.inventory.rows occurrence).map locals
        (ContextualExecutionCommutationNames.intoCapture locals before.declarations) := by
  change ((ContextualActivatedStep.resultRows locals before.declarations producer.selection producer.outputs
    before.inventory.rows occurrence).map locals (ContextualComputedFreshFrame.includeSource
      (producer.prepared empty).update)) = _
  unfold ContextualActivatedStep.resultRows
  simp only [selection]
  split_ifs with member
  · change ContextualStoredRows.Row.shared (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose, frame_output producer empty]
  · rw [ContextualStoredRows.Row.map_compose, frame_capture]

theorem target_retained (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    (producer.target empty).inventory.retained =
      before.inventory.retained.map (instantiateObservation
        (ContextualExecutionCommutationNames.intoCapture locals before.declarations)) ++
      producer.made.map (fun occurrence => observe
        (instantiate (ContextualExecutionCommutationNames.intoCreated locals before.declarations producer.scope)
          (producer.value occurrence))) := by
  change ((before.inventory.retained.map (instantiateObservation (ContextualSelectionViews.capturedTarget locals before.declarations))) ++
    ruleRoots (ContextualActivatedStep.prepared locals before.declarations before.occupied producer.selection producer.rule
      before.inventory.rows).rule).map (instantiateObservation (ContextualComputedFreshFrame.includeSource
        (producer.prepared empty).update)) = _
  rw [List.map_append, List.map_map]
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro value _member
    rw [Function.comp_apply, instantiateObservation_comp, frame_capture]
  · simp only [ruleRoots, ruleTerms, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
      ContextualFreshening.ruleAt, RuleInstance.map, rule, List.map_nil, List.nil_append, List.flatMap_nil,
      List.map_map]
    apply List.map_congr_left
    intro occurrence _member
    change observe (instantiate _ (instantiate _ _)) = _
    rw [← Assignment.instantiate_compose]
    exact congrArg (fun change => observe (instantiate change (producer.value occurrence)))
      (frame_output producer empty)

theorem target_templates (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    (producer.target empty).inventory.templates =
      before.inventory.templates.map (instantiateObservation (ContextualStoredRows.liftCaptures locals
        (ContextualExecutionCommutationNames.intoCapture locals before.declarations))) := by
  change (before.inventory.templates.map (instantiateObservation (ContextualStoredRows.liftCaptures locals
    (ContextualSelectionViews.capturedTarget locals before.declarations)))).map
      (instantiateObservation (ContextualStoredRows.liftCaptures locals
        (ContextualComputedFreshFrame.includeSource (producer.prepared empty).update))) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro value _member
  rw [Function.comp_apply, instantiateObservation_comp, ContextualStoredRows.liftCaptures_compose, frame_capture]

def nextLedger (occupied : Finset Nat) : Finset Nat := ContextualFreshFrameScopeLedger.helperLedger
  (occupied ∪ Finset.Ico (ContextualActivationScopes.start occupied) (ContextualActivationScopes.start occupied + 1))

theorem target_ledger (producer : Producer before) (empty : before.inventory.configuration.equations = []) :
    (producer.target empty).occupied = nextLedger before.occupied := rfl

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem scope_is_start (producer : Producer before) : producer.scope = ContextualActivationScopes.start before.occupied :=
  Nat.add_zero _

theorem later_scope (first second : Producer before) (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.after second empty separate).scope = ContextualActivationScopes.start (nextLedger before.occupied) :=
  (first.after second empty separate).scope_is_start

end Producer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
