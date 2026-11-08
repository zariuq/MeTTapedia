import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrameModels

/-!
# The clause state comparison preserves simultaneous row realizations

The source and native row witnesses stay in the same future family. Their
unused private arities are supplied by actual declarations in the resulting
capture frame. This strengthens single-row matching to the witness form
needed for dependent joins and subsequent source admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseRealizationRefinement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows
open ContextualConditionalRealizations

variable {S : Signature} {Local Query O Next : Type} {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq Local] [DecidableEq Query] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {queries : Query → MetaArity S} {locals : Local → MetaArity S}
    {before : ContextualClauseSourceState.World locals O Γ sort} {occupied : Finset Nat}
    {plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort)}
    {picked : Selection O}
    (compiled : ContextualConditionalClauses.Compiled queries locals (before := before.native occupied) plan picked)
    {next : Next → MetaArity S}

def bankImages (candidate : Assignment compiled.firing.target.declarations next) :
    Assignment (ContextualClauseFrames.bank queries locals) next :=
  fun name => candidate (.inl (.inl ⟨0, name⟩))

def helperImages (candidate : Assignment compiled.firing.target.declarations next) :
    Assignment compiled.firing.update.declaration next := fun name => candidate (.inr (.inl name))

def sourceImages (candidate : Assignment compiled.firing.target.declarations next) :
    Assignment (ContextualClauseSourceState.resultLocals queries locals before) next
  | .inl name => bankImages compiled candidate (.inl name)
  | .inr name => Assignment.compose candidate compiled.sourceFrame.assignment name

def nativeImages (candidate : Assignment compiled.firing.target.declarations next) :
    Assignment (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals)
      compiled.firing.update.declaration) next
  | .inl name => bankImages compiled candidate name
  | .inr name => helperImages compiled candidate name

private theorem answer_iff (port : Fin picked.made.length) (next : Next → MetaArity S)
    (pattern : Term (signature S next) Γ sort) :
    AnswerRealizes (ContextualConditionalAnswers.ofUpdate compiled.firing.update
      (compiled.firing.outputs (picked.made.get port))) next pattern ↔
    AnswerRealizes ⟨ContextualClauseSourceState.information queries locals before plan picked,
      queryView queries locals before.declarations
        (plan.rule.produce.get ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩)⟩ next pattern := by
  rw [answer_ofUpdate_iff]
  erw [compiled.native_information, compiled.values]
  change AnswerRealizes ⟨ContextualResidual.mapProblem
      (ContextualClauseFrames.frame queries locals before.declarations occupied).assignment
      (ContextualClauseSourceState.information queries locals before plan picked),
    ContextualClauseAdmission.outputs queries locals before.declarations occupied picked plan.rule
      (fun occurrence => (before.rows occurrence).value) (picked.made.get port)⟩ next pattern ↔ _
  erw [ContextualClausePublication.output_at_port queries locals before.declarations occupied picked plan.rule
    (fun occurrence => (before.rows occurrence).value) compiled.source_admitted.output_distinct
    compiled.source_admitted.output_shape port]
  exact ContextualClauseFrameModels.answer_frame_iff queries locals before.declarations occupied _ _ next pattern

theorem produced (port : Fin picked.made.length) (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Realizes (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows (picked.made.get port)) ↔
    Realizes (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows (picked.made.get port)) := by
  have made : picked.made.get port ∈ compiled.firing.selection.made := by
    rw [compiled.selected]
    exact List.get_mem _ _
  cases ordinary : compiled.firing.reusable (picked.made.get port) with
  | true =>
      have sourceKind := (ContextualClauseStateRefinement.reusable_at compiled port).symm.trans ordinary
      rw [ContextualClauseSourceState.produced_at (ContextualClauseStateRefinement.source_is_admitted compiled) port]
      unfold ContextualClauseSourceState.producedRow
      rw [sourceKind]
      have nativeRow : compiled.firing.target.rows (picked.made.get port) =
          ContextualConditionalPublication.ordinary (ContextualClauseFrames.bank queries locals)
            compiled.firing.update.declaration compiled.firing.target.declarations
            (ContextualConditionalAnswers.ofUpdate compiled.firing.update (compiled.firing.outputs (picked.made.get port))) := by
        change (if _ then (if _ then _ else _) else _) = _
        rw [if_pos made, ordinary]
        rfl
      rw [nativeRow]
      exact (realizes_ordinary_iff locals _ _ _
        (fun name => bankImages compiled candidate (.inl name)) _ pattern).trans
        ((realizes_ordinary_iff (ContextualClauseFrames.bank queries locals) _ _ candidate
          (bankImages compiled candidate) _ pattern).trans (answer_iff compiled port next pattern)).symm
  | false =>
      have sourceKind := (ContextualClauseStateRefinement.reusable_at compiled port).symm.trans ordinary
      rw [ContextualClauseSourceState.shared_output_row (ContextualClauseStateRefinement.source_is_admitted compiled) port sourceKind,
        ContextualClauseStateRefinement.shared_value compiled port ordinary]
      rw [realizes_shared_iff _ _ _ (sourceImages compiled candidate),
        realizes_shared_iff _ _ candidate (nativeImages compiled candidate)]
      erw [Assignment.instantiate_compose, ContextualClauseStateRefinement.returned_environment compiled]

theorem retained (occurrence : O) (notMade : occurrence ∉ picked.made)
    (next : Next → MetaArity S) (candidate : Assignment compiled.firing.target.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Realizes (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows occurrence) ↔
    Realizes (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows occurrence) := by
  have notActual : occurrence ∉ compiled.firing.selection.made := by rw [compiled.selected]; exact notMade
  have source := (realizes_extendPrivate_iff locals
    (ContextualClauseSourceState.resultFamily queries locals before)
    (ContextualClauseSourceState.resultFamily queries locals before)
    (Assignment.compose candidate compiled.sourceFrame.assignment)
    (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
    ((before.rows occurrence).map locals before.declarations (captureEmbedding queries locals before.declarations))).trans
      (realizes_map_iff locals before.declarations (captureEmbedding queries locals before.declarations)
        (Assignment.compose candidate compiled.sourceFrame.assignment) pattern (before.rows occurrence))
  rw [ContextualClauseSourceState.retained_at occurrence notMade]
  erw [← Assignment.compose_associative, ContextualClauseStateRefinement.source_frame_on_captures compiled] at source
  apply source.trans
  symm
  change Realizes _ _ _ _ (if _ then _ else _) ↔ _
  rw [if_neg notActual]
  exact (realizes_extendPrivate_iff (ContextualClauseFrames.bank queries locals)
    compiled.firing.target.declarations compiled.firing.update.declaration candidate (helperImages compiled candidate) pattern _).trans
    ((realizes_map_iff (ContextualClauseFrames.bank queries locals) before.declarations _ candidate pattern _).trans
      (realizes_extendPrivate_iff locals before.declarations queries _
        (fun name => bankImages compiled candidate (.inr name)) pattern (before.rows occurrence)))

theorem all_rows (occurrence : O) (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Realizes (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows occurrence) ↔
    Realizes (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern (compiled.firing.target.rows occurrence) := by
  by_cases made : occurrence ∈ picked.made
  · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
    exact produced compiled port next candidate pattern
  · exact retained compiled occurrence made next candidate pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseRealizationRefinement
