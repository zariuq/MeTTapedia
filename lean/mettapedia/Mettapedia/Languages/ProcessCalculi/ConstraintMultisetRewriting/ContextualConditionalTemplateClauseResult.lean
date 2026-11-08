import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauseValues

/-!
# Source and compiled conditional-template worlds agree

The observation comparison covers all produced and retained rows, actor
bindings, physical occurrences and every information model in both
directions. Schema conditions remain local to their rows. The source update
and the actual compiler result are constructed independently.
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

theorem produced_matches (port : Fin picked.made.length)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualConditionalTemplateState.resultLocals queries inners locals before)
      (ContextualConditionalTemplateState.resultFamily queries inners locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualConditionalTemplateState.target queries inners locals before rule picked).rows (picked.made.get port)) ↔
    Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern
      ((target compiled).rows (picked.made.get port)) := by
  let origin : Fin rule.code.produce.length :=
    ⟨port.val, ContextualConditionalTemplateState.output_shape compiled.source_admitted ▸ port.isLt⟩
  have sourceAt := ContextualConditionalTemplateState.produced_at compiled.source_admitted port
  have selectedDescriptor := rule.output_at_port picked.made compiled.source_admitted.output_distinct
    (ContextualConditionalTemplateState.output_shape compiled.source_admitted) port
  change descriptor (rule := rule) (picked := picked) (picked.made.get port) =
    some (port.val, ⟨rule.code.produce.get origin, rule.conditions origin⟩) at selectedDescriptor
  have old := ContextualClauseStateRefinement.produced_matches (before := before) compiled port next candidate pattern
  rw [ContextualClauseSourceState.produced_at compiled.source_admitted port] at old
  have raw := ContextualConditionalTemplateState.raw_produced_row (queries := queries) (inners := inners)
    (locals := locals) (before := before) (rule := rule) (picked := picked) origin
  erw [raw] at old
  generalize descriptionEq : (⟨rule.code.produce.get origin, rule.conditions origin⟩ :
    ContextualConditionalTemplateSource.Description queries inners before.declarations Γ sort) = description
      at sourceAt selectedDescriptor
  rcases description with ⟨production, conditions⟩
  have productionEq := congrArg Sigma.fst descriptionEq
  change rule.code.produce.get origin = production at productionEq
  change Matches _ _ _ _ (match rule.code.produce.get origin with
    | .ordinary value => _ | .shared value => _ | .schema body => _) ↔ _ at old
  rw [productionEq] at old
  cases production with
  | ordinary value =>
      cases conditions
      have nativeRow : (target compiled).rows (picked.made.get port) =
          packOrdinary compiled (compiled.firing.target.rows (picked.made.get port)) := by
        change rows compiled _ = _
        simp only [rows, selectedDescriptor]
      rw [sourceAt, nativeRow]
      exact (ContextualConditionalRowPacking.matches_iff
        (ContextualConditionalTemplateState.PrivateNames (Query := Query) (Inner := Inner) locals before)
        (ContextualConditionalTemplateState.privateDeclarations queries inners locals before)
        (ContextualConditionalTemplateState.resultFamily queries inners locals before) true _
        (Assignment.compose candidate compiled.sourceFrame.assignment) pattern).trans
        (old.trans (ContextualConditionalRowPacking.matches_iff (PrivateNames compiled) (privateDeclarations compiled)
          compiled.firing.target.declarations true _ candidate pattern).symm)
  | shared value =>
      cases conditions
      have nativeRow : (target compiled).rows (picked.made.get port) =
          packOrdinary compiled (compiled.firing.target.rows (picked.made.get port)) := by
        change rows compiled _ = _
        simp only [rows, selectedDescriptor]
      rw [sourceAt, nativeRow]
      exact (ContextualConditionalRowPacking.matches_iff
        (ContextualConditionalTemplateState.PrivateNames (Query := Query) (Inner := Inner) locals before)
        (ContextualConditionalTemplateState.privateDeclarations queries inners locals before)
        (ContextualConditionalTemplateState.resultFamily queries inners locals before) true _
        (Assignment.compose candidate compiled.sourceFrame.assignment) pattern).trans
        (old.trans (ContextualConditionalRowPacking.matches_iff (PrivateNames compiled) (privateDeclarations compiled)
          compiled.firing.target.declarations true _ candidate pattern).symm)
  | schema body =>
      rw [sourceAt]
      have native := schema_matches compiled (picked.made.get port) port.val body conditions selectedDescriptor next candidate pattern
      have square : Assignment.compose candidate (actorValues compiled) =
          Assignment.compose (Assignment.compose candidate compiled.sourceFrame.assignment)
            (actorEnv queries inners locals before) := by
        rw [actor_square]
        exact Assignment.compose_associative _ _ _
      exact (ContextualConditionalTemplateState.schema_description_matches port.val body conditions next
        (Assignment.compose candidate compiled.sourceFrame.assignment) pattern).trans (square ▸ native.symm)

theorem all_row_observations (occurrence : O)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualConditionalTemplateState.resultLocals queries inners locals before)
      (ContextualConditionalTemplateState.resultFamily queries inners locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualConditionalTemplateState.target queries inners locals before rule picked).rows occurrence) ↔
    Matches (resultLocals compiled) compiled.firing.target.declarations candidate pattern ((target compiled).rows occurrence) := by
  by_cases made : occurrence ∈ picked.made
  · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
    exact produced_matches compiled port next candidate pattern
  · have source := ContextualConditionalTemplateState.retained_matches (rule := rule) occurrence made next
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
    have native := retained_matches compiled occurrence made next candidate pattern
    erw [← Assignment.compose_associative, ContextualClauseStateRefinement.source_frame_on_captures compiled] at source
    exact source.trans native.symm

theorem source_world_equivalent :
    ContextualWorldComparison.Equivalent
      (ContextualConditionalTemplateState.target queries inners locals before rule picked)
      (actorEnv queries inners locals before)
      (ContextualWorldComparison.nativeWorld (resultLocals compiled) (target compiled)) (actorValues compiled) := by
  exact ContextualWorldComparison.equivalent_of_frame _ _ _ _ compiled.sourceFrame.name compiled.sourceFrame.injective
    compiled.sourceFrame.preserves (physical_exact compiled).symm (information_exact compiled) (actor_square compiled)
    (fun _ next candidate pattern occurrence _ => all_row_observations compiled occurrence next candidate pattern)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses.Compiled

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Query Inner Local O : Type} {Γ : Ctx S} {sort : S.Srt}
    (queries : Query → MetaArity S) (inners : Inner → MetaArity S) (locals : Local → MetaArity S)
    [DecidableEq Query] [DecidableEq Inner] [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (before : ContextualClauseSourceState.World locals O Γ sort) (occupied : Finset Nat)
    (rule : ContextualConditionalTemplateSource.Rule queries inners before.declarations Γ sort) (picked : Selection O)

theorem source_iff_compiled_at_fuel (fuel : Nat) :
    ContextualConditionalTemplateState.Admitted queries inners locals before rule picked ↔
      ∃ compiled : Compiled queries inners locals before occupied rule picked,
        compiled.firing.fuel = fuel ∧
        ContextualWorldComparison.Equivalent
          (ContextualConditionalTemplateState.target queries inners locals before rule picked)
          (ContextualConditionalTemplateState.actorEnv queries inners locals before)
          (ContextualWorldComparison.nativeWorld (Compiled.resultLocals compiled) (Compiled.target compiled))
          (Compiled.actorValues compiled) := by
  constructor
  · intro source
    obtain ⟨compiled, budget⟩ := realize source fuel
    exact ⟨compiled, budget, Compiled.source_world_equivalent compiled⟩
  · rintro ⟨compiled, _budget, _equivalent⟩
    exact compiled.source_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateClauses
