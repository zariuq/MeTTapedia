import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses

/-!
# The actual compiled clause represents its independent source state update

The comparison retains the whole information problem, physical effects,
ordinary schemas, shared references, untouched rows and returned query
environment. Native scope and helper allocation may change declaration
families; source observations are pulled back along the actual source frame.
No solver completion assumption is needed.
The row observation is conditional matching in every future family.
Additional inspections of native representations need their own comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Local Query O : Type} {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {queries : Query → MetaArity S} {locals : Local → MetaArity S}
    {before : ContextualClauseSourceState.World locals O Γ sort} {occupied : Finset Nat}
    {plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort)}
    {picked : Selection O}
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before.native occupied) plan picked)

include compiled in
theorem source_is_admitted : ContextualClauseSourceState.Admitted queries locals before plan picked :=
  ContextualConditionalClauses.Compiled.source_admitted compiled

theorem information_exact : compiled.firing.target.equations =
    ContextualResidual.mapProblem compiled.sourceFrame.assignment
      (ContextualClauseSourceState.target queries locals before plan picked).equations :=
  compiled.result_equations

theorem physical_exact : compiled.firing.target.present =
    (ContextualClauseSourceState.target queries locals before plan picked).present :=
  compiled.physical_result

theorem solvable_iff : ContextualConditionalExecution.Solvable compiled.firing.target.equations ↔
    ContextualConditionalExecution.Solvable
      (ContextualClauseSourceState.target queries locals before plan picked).equations := by
  rw [information_exact compiled]
  exact ContextualConditionalNaturality.solvable_extension_iff compiled.sourceFrame _

theorem returned_environment (value : Term (signature S (queryFamily queries before.declarations)) Γ sort) :
    instantiate compiled.sourceFrame.assignment
      (instantiate (ContextualClauseSourceState.continuationEnv queries locals before) value) =
      instantiate compiled.continuationEnv value :=
  (Assignment.instantiate_compose compiled.sourceFrame.assignment (queryEmbedding queries locals before.declarations) value).symm

theorem source_frame_on_captures :
    Assignment.compose compiled.sourceFrame.assignment (captureEmbedding queries locals before.declarations) =
      Assignment.compose (ContextualComputedFreshFrame.includeSource compiled.firing.update)
        (ContextualSelectionViews.capturedTarget (ContextualClauseFrames.bank queries locals) before.declarations) := by
  erw [compiled.sourceFrame_assignment, ← Assignment.compose_associative, ContextualClauseFrames.captures_square]
  rfl

theorem reusable_at (port : Fin picked.made.length) :
    compiled.firing.reusable (picked.made.get port) =
      plan.reusable.get ⟨port.val, compiled.source_admitted.output_shape.trans plan.shape.symm ▸ port.isLt⟩ := by
  have first : port.val < (picked.made.map compiled.firing.reusable).length := by
    simpa only [List.length_map] using port.isLt
  have second : port.val < plan.reusable.length :=
    compiled.source_admitted.output_shape.trans plan.shape.symm ▸ port.isLt
  have atPort := congrArg (fun bits : List Bool => bits[port.val]?) compiled.intents
  rw [List.getElem?_eq_getElem first, List.getElem?_eq_getElem second] at atPort
  simpa only [List.get_eq_getElem, List.getElem_map] using Option.some.inj atPort

theorem shared_value (port : Fin picked.made.length)
    (live : compiled.firing.reusable (picked.made.get port) = false) :
    compiled.firing.target.rows (picked.made.get port) = ofStored _ _ (.shared
      (instantiate compiled.continuationEnv
        (plan.rule.produce.get ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩))) := by
  have made : picked.made.get port ∈ compiled.firing.selection.made := by
    rw [compiled.selected]
    exact List.get_mem _ _
  rw [compiled.firing.shared_row _ made live, compiled.values]
  apply congrArg (fun value => ofStored _ _ (ContextualStoredRows.Row.shared value))
  change instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
    (ContextualClauseAdmission.outputs queries locals before.declarations occupied picked plan.rule
      (fun occurrence => (before.rows occurrence).value) (picked.made.get port)) = _
  erw [ContextualClausePublication.output_at_port queries locals before.declarations occupied picked plan.rule
    (fun occurrence => (before.rows occurrence).value) compiled.source_admitted.output_distinct
    compiled.source_admitted.output_shape port]
  erw [← Assignment.instantiate_compose, ← compiled.sourceFrame_assignment]
  exact (Assignment.instantiate_compose compiled.sourceFrame.assignment (queryEmbedding queries locals before.declarations) _).symm

theorem produced_matches (port : Fin picked.made.length) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows (picked.made.get port)) ↔
    Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows (picked.made.get port)) := by
  cases reusable : compiled.firing.reusable (picked.made.get port) with
  | true =>
      have sourceKind := (reusable_at compiled port).symm.trans reusable
      exact (ContextualClauseSourceState.ordinary_output_instances (source_is_admitted compiled) port sourceKind next _ pattern).trans
        (compiled.ordinary_body_instances port reusable next candidate pattern).symm
  | false =>
      have sourceKind := (reusable_at compiled port).symm.trans reusable
      rw [ContextualClauseSourceState.shared_output_row (source_is_admitted compiled) port sourceKind,
        shared_value compiled port reusable]
      rw [ofStored_matches_iff, ofStored_matches_iff, shared_matches_iff, shared_matches_iff]
      erw [Assignment.instantiate_compose, returned_environment compiled]

theorem retained_matches (occurrence : O) (notMade : occurrence ∉ picked.made)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows occurrence) ↔
    Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows occurrence) := by
  have native := compiled.firing.retained_matches occurrence
    (by rw [compiled.selected]; exact notMade) next candidate pattern
  have source := ContextualClauseSourceState.retained_matches (queries := queries) (locals := locals)
    (before := before) (plan := plan) (picked := picked) occurrence notMade next
    (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
  erw [← Assignment.compose_associative, source_frame_on_captures compiled] at source
  exact source.trans (native.trans
    (ContextualConditionalPublication.extendPrivate_matches_iff locals queries before.declarations _ _ pattern)).symm

theorem all_row_observations (occurrence : O) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows occurrence) ↔
    Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows occurrence) := by
  by_cases made : occurrence ∈ picked.made
  · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
    exact produced_matches compiled port next candidate pattern
  · exact retained_matches compiled occurrence made next candidate pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement
