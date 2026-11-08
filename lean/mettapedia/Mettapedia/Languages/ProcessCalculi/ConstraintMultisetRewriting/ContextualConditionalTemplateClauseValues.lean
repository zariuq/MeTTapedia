import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses

/-!
# Constructed schema bodies decode from actual compiled outputs

The decoder recognizes the private template-query role in the actual
activation frame. Actor variables, incoming captures and solver helpers
retain their source identities. The output equality follows from the
clause compiler's prepared production list, independently of row metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses.Compiled

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualTemplateSource
open ContextualConditionalTemplateState

variable {S : Signature} {Query Inner Local O : Type} {Γ : Ctx S} {sort : S.Srt}
    {queries : Query → MetaArity S} {inners : Inner → MetaArity S} {locals : Local → MetaArity S}
    [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {before : ContextualClauseSourceState.World locals O Γ sort} {occupied : Finset Nat}
    {rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort}
    {picked : Selection O}
    (compiled : Compiled queries inners locals before occupied rule picked)

theorem output_source_value (port : Fin picked.made.length) :
    instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
        (compiled.firing.outputs (picked.made.get port)) =
      instantiate compiled.continuationEnv
        ((rawPlan queries inners locals before rule).rule.produce.get
          ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩) := by
  rw [compiled.values]
  change instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
    (ContextualClauseAdmission.outputs (expanded queries inners) locals before.declarations occupied picked
      (rawPlan queries inners locals before rule).rule (fun occurrence => (before.rows occurrence).value)
      (picked.made.get port)) = _
  erw [ContextualClausePublication.output_at_port (expanded queries inners) locals before.declarations occupied picked
    (rawPlan queries inners locals before rule).rule (fun occurrence => (before.rows occurrence).value)
    compiled.source_admitted.output_distinct compiled.source_admitted.output_shape port]
  erw [← Assignment.instantiate_compose, ← compiled.sourceFrame_assignment]
  exact (Assignment.instantiate_compose compiled.sourceFrame.assignment
    (queryEmbedding (expanded queries inners) locals before.declarations) _).symm

def decoder : Assignment compiled.firing.target.declarations
    (ContextualSelectionViews.source (expanded queries inners) compiled.firing.target.declarations)
  | .inl (.inl ⟨_, .inr (.inr entry)⟩) =>
      generator (ContextualSelectionViews.source (expanded queries inners) compiled.firing.target.declarations)
        (.inl (.inr entry))
  | identity =>
      generator (ContextualSelectionViews.source (expanded queries inners) compiled.firing.target.declarations)
        (.inr identity)

theorem continuation_query (name : Query ⊕ (Nat × Inner)) :
    compiled.continuationEnv (.inl name) = generator compiled.firing.target.declarations
      (.inl (.inl ⟨ContextualActivationScopes.start occupied, .inr name⟩)) := by
  change instantiate compiled.sourceFrame.assignment (generator _ (.inl name)) = _
  rw [instantiate_generator, compiled.sourceFrame_assignment]
  change instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
    ((ContextualClauseFrames.frame (expanded queries inners) locals before.declarations occupied).assignment (.inl name)) = _
  erw [ContextualClauseFrames.frame_query, instantiate_generator]
  exact ContextualFreshFrameScopeLedger.includeSource_image compiled.firing.update _

theorem continuation_capture (name : before.Names) :
    compiled.continuationEnv (.inr name) = generator compiled.firing.target.declarations
      (.inl (.inr name)) := by
  change instantiate compiled.sourceFrame.assignment (generator _ (.inr (.inr name))) = _
  rw [instantiate_generator, compiled.sourceFrame_assignment]
  change instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
    ((ContextualClauseFrames.frame (expanded queries inners) locals before.declarations occupied).assignment (.inr (.inr name))) = _
  erw [ContextualClauseFrames.frame_capture, instantiate_generator]
  exact ContextualFreshFrameScopeLedger.includeSource_image compiled.firing.update _

set_option maxHeartbeats 800000 in
theorem decoder_square (origin : Nat) :
    Assignment.compose (Assignment.compose (decoder compiled) compiled.continuationEnv)
        (templateInclusion queries inners before.declarations origin) =
      storedBody queries inners before.declarations (actorValues compiled) origin := by
  funext identity
  change instantiate (Assignment.compose (decoder compiled) compiled.continuationEnv)
    (templateInclusion queries inners before.declarations origin identity) = _
  rw [Assignment.instantiate_compose]
  cases identity with
  | inl name =>
      change instantiate (decoder compiled)
        (instantiate compiled.continuationEnv (generator _ (.inl (.inr (origin, name))))) = _
      erw [instantiate_generator, continuation_query, instantiate_generator]
      rfl
  | inr name =>
      cases name with
      | inl name =>
          change instantiate (decoder compiled)
            (instantiate compiled.continuationEnv (generator _ (.inl (.inl name)))) =
            instantiate (ContextualSelectionViews.capturedSource (expanded queries inners) compiled.firing.target.declarations)
              (instantiate compiled.continuationEnv (generator _ (.inl (.inl name))))
          erw [instantiate_generator, continuation_query, instantiate_generator, instantiate_generator]
          rfl
      | inr name =>
          change instantiate (decoder compiled)
            (instantiate compiled.continuationEnv (generator _ (.inr name))) =
            instantiate (ContextualSelectionViews.capturedSource (expanded queries inners) compiled.firing.target.declarations)
              (instantiate compiled.continuationEnv (generator _ (.inr name)))
          erw [instantiate_generator, continuation_capture, instantiate_generator, instantiate_generator]
          rfl

theorem schema_body_from_actual_output (port : Fin picked.made.length)
    (body : Term (signature S (Blueprint queries inners before.declarations)) Γ sort)
    (selected : rule.code.produce.get ⟨port.val, ContextualConditionalTemplateState.output_shape compiled.source_admitted ▸ port.isLt⟩ = .schema body) :
    instantiate (decoder compiled)
        (instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
          (compiled.firing.outputs (picked.made.get port))) =
      ContextualStoredRows.asTemplate (expanded queries inners) compiled.firing.target.declarations
        (ContextualTemplateSource.stored queries inners before.declarations (actorValues compiled) port.val body) := by
  have value : (rawPlan queries inners locals before rule).rule.produce.get
      ⟨port.val, compiled.source_admitted.output_shape ▸ port.isLt⟩ =
      instantiate (templateInclusion queries inners before.declarations port.val) body := by
    have actual := Rule.lower_at_port queries inners before.declarations rule.code
      ⟨port.val, ContextualConditionalTemplateState.output_shape compiled.source_admitted ▸ port.isLt⟩
    rw [selected] at actual
    exact actual
  rw [output_source_value, value]
  change instantiate (decoder compiled)
    (instantiate compiled.continuationEnv (instantiate (templateInclusion queries inners before.declarations port.val) body)) =
    instantiate (storedBody queries inners before.declarations (actorValues compiled) port.val) body
  rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, decoder_square]

theorem published_schema_body_from_actual_output (port : Fin picked.made.length)
    (body : Term (signature S (Blueprint queries inners before.declarations)) Γ sort)
    (conditions : ContextualResidual.Problem (Blueprint queries inners before.declarations))
    (selected : descriptor (rule := rule) (picked := picked) (picked.made.get port) =
      some (port.val, ⟨.schema body, conditions⟩)) :
    instantiate (Assignment.compose
        (ContextualConditionalRowPacking.inclusion (PrivateNames compiled) (privateDeclarations compiled)
          compiled.firing.target.declarations false) (decoder compiled))
        (instantiate (ContextualComputedFreshFrame.includeSource compiled.firing.update)
          (compiled.firing.outputs (picked.made.get port))) =
      ContextualStoredRows.asTemplate (resultLocals compiled) compiled.firing.target.declarations
        ((target compiled).rows (picked.made.get port)).value := by
  have source := rule.output_at_port picked.made compiled.source_admitted.output_distinct
    (ContextualConditionalTemplateState.output_shape compiled.source_admitted) port
  have same := Option.some.inj (source.symm.trans selected)
  have production := congrArg (fun entry => entry.2.1) same
  rw [Assignment.instantiate_compose, schema_body_from_actual_output compiled port body production]
  change _ = ContextualStoredRows.asTemplate _ _ (rows compiled (picked.made.get port)).value
  simp only [rows, selected]
  exact (ContextualConditionalRowPacking.template (PrivateNames compiled) (privateDeclarations compiled)
    compiled.firing.target.declarations false
    (ContextualConditionalTemplates.stored queries inners before.declarations (actorValues compiled)
      port.val ⟨.schema body, conditions⟩)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses.Compiled
