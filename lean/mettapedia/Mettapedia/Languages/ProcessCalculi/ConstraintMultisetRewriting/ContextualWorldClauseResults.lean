import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldClauseAdmission

/-!
# A resolved clause preserves the world comparison

Both worlds execute the same authored clause through their exposed
environments. Retained rows use the old model relation, shared outputs use
the returned environment, and reusable outputs use the proved equivalence
of complete conditional source instances. The resulting comparison has
the same form and can therefore be used by another clause.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalRealizations ContextualClauseWitnesses

variable {S : Signature} {Public Query Local Shared Left Right O Next : Type}
    {exposed : Public → MetaArity S} (queries : Query → MetaArity S)
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def resultEnv (environment : Assignment exposed captures) :
    Assignment (queryFamily queries exposed) (family queries locals captures) :=
  Assignment.compose (queryEmbedding queries locals captures) (ContextualStoredRows.liftCaptures queries environment)

theorem result_binding {next : Next → MetaArity S} (environment : Assignment exposed captures)
    (candidate : Assignment (family queries locals captures) next) :
    Assignment.compose candidate (resultEnv queries locals captures environment) =
      valuation queries exposed (queryBodies queries locals captures candidate)
        (Assignment.compose (caller queries locals captures candidate) environment) := by
  rw [resultEnv, Assignment.compose_associative, query_square, valuation_capture_map]

theorem result_value {next : Next → MetaArity S} (environment : Assignment exposed captures)
    (candidate : Assignment (family queries locals captures) next)
    (value : Term (signature S (queryFamily queries exposed)) Γ sort) :
    instantiate candidate (queryView queries locals captures
        (instantiate (ContextualStoredRows.liftCaptures queries environment) value)) =
      instantiate (Assignment.compose candidate (resultEnv queries locals captures environment)) value := by
  rw [Assignment.instantiate_compose, resultEnv, Assignment.instantiate_compose]
  rfl

theorem prepared_output (environment : Assignment exposed captures)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort))
    (port : Fin plan.rule.produce.length) :
    (preparedPlan queries environment plan).rule.produce.get
        ⟨port.val, by simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using port.isLt⟩ =
      instantiate (ContextualStoredRows.liftCaptures queries environment) (plan.rule.produce.get port) := by
  change (plan.rule.produce.map _).get ⟨port.val, by simpa only [List.length_map] using port.isLt⟩ = _
  erw [List.get_eq_getElem, List.getElem_map]
  rfl

variable {queries locals captures} {lefts : Left → MetaArity S} {rights : Right → MetaArity S}
    {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualClauseSourceState.World rights O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}
    {next : Next → MetaArity S}

theorem result_bindings (queries : Query → MetaArity S)
    (first : Assignment (family queries lefts left.declarations) next)
    (second : Assignment (family queries rights right.declarations) next)
    (related : Related left leftEnv right rightEnv (caller queries lefts left.declarations first)
      (caller queries rights right.declarations second))
    (queryEqual : queryBodies queries lefts left.declarations first = queryBodies queries rights right.declarations second) :
    Assignment.compose first (resultEnv queries lefts left.declarations leftEnv) =
      Assignment.compose second (resultEnv queries rights right.declarations rightEnv) := by
  rw [result_binding, result_binding, queryEqual, related.bindings]

variable [DecidableEq Query] [DecidableEq Left] [DecidableEq Right] [DecidableEq O]

theorem result_related (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort)) (picked : Selection O)
    (leftAdmitted : ContextualClauseSourceState.Admitted queries lefts left (preparedPlan queries leftEnv plan) picked)
    (rightAdmitted : ContextualClauseSourceState.Admitted queries rights right (preparedPlan queries rightEnv plan) picked)
    (first : Assignment (family queries lefts left.declarations) next)
    (second : Assignment (family queries rights right.declarations) next)
    (firstModel : ContextualResidual.Models first
      (ContextualClauseSourceState.information queries lefts left (preparedPlan queries leftEnv plan) picked))
    (secondModel : ContextualResidual.Models second
      (ContextualClauseSourceState.information queries rights right (preparedPlan queries rightEnv plan) picked))
    (related : Related left leftEnv right rightEnv (caller queries lefts left.declarations first)
      (caller queries rights right.declarations second))
    (queryEqual : queryBodies queries lefts left.declarations first = queryBodies queries rights right.declarations second) :
    Related (ContextualClauseSourceState.target queries lefts left (preparedPlan queries leftEnv plan) picked)
      (resultEnv queries lefts left.declarations leftEnv)
      (ContextualClauseSourceState.target queries rights right (preparedPlan queries rightEnv plan) picked)
      (resultEnv queries rights right.declarations rightEnv) first second := by
  have bindings := result_bindings queries first second related queryEqual
  have takeShape : plan.rule.take.length = picked.taken.length := by
    simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using leftAdmitted.take_shape
  have readShape : plan.rule.read.length = picked.read.length := by
    simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using leftAdmitted.read_shape
  have outputShape : picked.made.length = plan.rule.produce.length := by
    simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using leftAdmitted.output_shape
  refine ⟨firstModel, secondModel, bindings, ?_⟩
  intro later pattern occurrence member
  by_cases made : occurrence ∈ picked.made
  · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
    let output : Fin plan.rule.produce.length := ⟨port.val, outputShape ▸ port.isLt⟩
    cases kind : plan.reusable.get ⟨port.val, outputShape.trans plan.shape.symm ▸ port.isLt⟩ with
    | true =>
        have firstRows := ContextualClauseSourceState.ordinary_output_instances leftAdmitted port kind
          later.declarations (Assignment.compose later.assignment first) pattern
        have secondRows := ContextualClauseSourceState.ordinary_output_instances rightAdmitted port kind
          later.declarations (Assignment.compose later.assignment second) pattern
        erw [prepared_output queries left.declarations leftEnv plan output] at firstRows
        erw [prepared_output queries right.declarations rightEnv plan output] at secondRows
        have answers := clause_instances_iff equivalent queries picked plan.rule takeShape readShape
          leftAdmitted.taken_present leftAdmitted.read_present (plan.rule.produce.get output) pattern
        exact firstRows.trans (answers.symm.trans secondRows.symm)
    | false =>
        rw [ContextualClauseSourceState.shared_output_row leftAdmitted port kind,
          ContextualClauseSourceState.shared_output_row rightAdmitted port kind,
          ofStored_matches_iff, ofStored_matches_iff, shared_matches_iff, shared_matches_iff]
        erw [prepared_output queries left.declarations leftEnv plan output,
          prepared_output queries right.declarations rightEnv plan output,
          result_value, result_value, ← Assignment.compose_associative, ← Assignment.compose_associative, bindings]
  · have oldMember : occurrence ∈ left.present := by
      change occurrence ∈ (left.present \ picked.taken.toFinset) ∪ picked.made.toFinset at member
      rcases Finset.mem_union.mp member with kept | new
      · exact (Finset.mem_sdiff.mp kept).1
      · exact False.elim (made (List.mem_toFinset.mp new))
    have firstRows := ContextualClauseSourceState.retained_matches
      (queries := queries) (locals := lefts) (before := left)
      (plan := preparedPlan queries leftEnv plan) (picked := picked) occurrence made
      later.declarations (Assignment.compose later.assignment first) pattern
    have secondRows := ContextualClauseSourceState.retained_matches
      (queries := queries) (locals := rights) (before := right)
      (plan := preparedPlan queries rightEnv plan) (picked := picked) occurrence made
      later.declarations (Assignment.compose later.assignment second) pattern
    erw [← Assignment.compose_associative, captures_square] at firstRows
    erw [← Assignment.compose_associative, captures_square] at secondRows
    exact firstRows.trans ((related.rows later pattern occurrence oldMember).trans secondRows.symm)

theorem Equivalent.step (equivalent : Equivalent left leftEnv right rightEnv)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries exposed)) Γ sort)) (picked : Selection O)
    (leftAdmitted : ContextualClauseSourceState.Admitted queries lefts left (preparedPlan queries leftEnv plan) picked)
    (rightAdmitted : ContextualClauseSourceState.Admitted queries rights right (preparedPlan queries rightEnv plan) picked) :
    Equivalent (ContextualClauseSourceState.target queries lefts left (preparedPlan queries leftEnv plan) picked)
      (resultEnv queries lefts left.declarations leftEnv)
      (ContextualClauseSourceState.target queries rights right (preparedPlan queries rightEnv plan) picked)
      (resultEnv queries rights right.declarations rightEnv) := by
  have takeShape : plan.rule.take.length = picked.taken.length := by
    simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using leftAdmitted.take_shape
  have readShape : plan.rule.read.length = picked.read.length := by
    simpa only [preparedPlan, preparedRule, RuleInstance.map, List.length_map] using leftAdmitted.read_shape
  refine ⟨?_, ?_, ?_⟩
  · change (left.present \ picked.taken.toFinset) ∪ picked.made.toFinset =
      (right.present \ picked.taken.toFinset) ∪ picked.made.toFinset
    rw [equivalent.physical]
  · intro Future future candidate model
    obtain ⟨extension, other, solved, oldRelated, queriesEqual⟩ := transfer_clause_model equivalent queries picked plan.rule
      takeShape readShape leftAdmitted.taken_present leftAdmitted.read_present candidate model
    refine ⟨extension, other, result_related equivalent queries plan picked leftAdmitted rightAdmitted
      (Assignment.compose extension.assignment candidate) other
      (ContextualResidual.models_compose model extension.assignment) solved oldRelated ?_⟩
    exact queriesEqual.symm
  · intro Future future candidate model
    obtain ⟨extension, other, solved, oldRelated, queriesEqual⟩ := transfer_clause_model equivalent.symm queries picked plan.rule
      takeShape readShape rightAdmitted.taken_present rightAdmitted.read_present candidate model
    refine ⟨extension, other, result_related equivalent queries plan picked leftAdmitted rightAdmitted
      other (Assignment.compose extension.assignment candidate) solved
      (ContextualResidual.models_compose model extension.assignment)
      (oldRelated.symm equivalent.physical.symm) queriesEqual⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
