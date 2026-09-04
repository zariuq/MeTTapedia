import Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofClausificationBatchAgreement
import Mettapedia.GSLT.LanguageDef.TptpOfficialFofToNamedFormulaExecution

/-!
# Exact official-FOF metadata projection into clausification batches

This module gives the document-level projection language an independent
role-indexed derivation.  TPTP supplies formula identity, role, annotations,
occurrence and source span.  The projection contributes only the additional
clausification policy: conjectures are negated, already-negated conjectures
and premise-like FOF records are positive, and non-formula roles fail closed.

The target contains the source occurrence key, polarity and generated
Skolem/CNF payloads.  Formula names, formula bodies, annotations, refinements
and source spans occur in the source pattern but cannot occur in the target.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionLanguageDef

abbrev FormulaRole := TptpOfficialRoleSemantics.FormulaRole
abbrev SourceOccurrence :=
  TptpFofClausificationBatchLanguageDef.SourceOccurrence

private def atom (label : String) : Pattern := .apply label []

/-- The supported role/polarity relation is independent of the authored
rewrite table.  It is the semantic policy that the table must realize. -/
inductive SupportedRole : FormulaRole → Bool → Type where
  | axiom : SupportedRole .axiom true
  | hypothesis : SupportedRole .hypothesis true
  | definition : SupportedRole .definition true
  | assumption : SupportedRole .assumption true
  | lemma : SupportedRole .lemma true
  | theorem : SupportedRole .theorem true
  | corollary : SupportedRole .corollary true
  | conjecture : SupportedRole .conjecture false
  | negatedConjecture : SupportedRole .negatedConjecture true
  | plain : SupportedRole .plain true

/-- Roles that are syntactically official but do not denote a FOF formula to
be clausified by this projection. -/
inductive UnsupportedRole : FormulaRole → Type where
  | type : UnsupportedRole .type
  | interpretation : UnsupportedRole .interpretation
  | finiteInterpretationDomain : UnsupportedRole .finiteInterpretationDomain
  | finiteInterpretationFunctors :
      UnsupportedRole .finiteInterpretationFunctors
  | finiteInterpretationPredicates :
      UnsupportedRole .finiteInterpretationPredicates
  | unknown : UnsupportedRole .unknown

theorem SupportedRole.polarity_exact {role : FormulaRole} {polarity : Bool}
    (evidence : SupportedRole role polarity) :
    TptpOfficialFofClausificationBatchAgreement.rolePolarity? role =
      some polarity := by
  cases evidence <;> rfl

theorem UnsupportedRole.polarity_absent {role : FormulaRole}
    (evidence : UnsupportedRole role) :
    TptpOfficialFofClausificationBatchAgreement.rolePolarity? role = none := by
  cases evidence <;> rfl

def supportedRoleOfPolarityExact {role : FormulaRole} {polarity : Bool}
    (exact :
      TptpOfficialFofClausificationBatchAgreement.rolePolarity? role =
        some polarity) :
    SupportedRole role polarity := by
  cases role <;> cases polarity <;>
    simp [TptpOfficialFofClausificationBatchAgreement.rolePolarity?] at exact
  all_goals constructor

/-- A projection request with every source-owned field visible. -/
structure Input where
  occurrence : SourceOccurrence
  role : FormulaRole
  refinement : Option Pattern
  name : Pattern
  formula : Pattern
  annotations : Pattern
  span : Pattern
  skolem : Pattern
  cnf : Pattern

def Input.rolePattern (input : Input) : Pattern :=
  match input.refinement with
  | none => plainRole input.role.code
  | some refinement => refinedRole input.role.code refinement

def Input.officialOccurrence (input : Input) : Pattern :=
  TptpOfficialFofClausificationBatchAgreement.encodeOfficialOccurrence
    input.occurrence

def Input.officialSource (input : Input) : Pattern :=
  a "tptp-semantic:fof-input" [input.officialOccurrence,
    a "tptp92-ast:fof-annotated:alt-1"
      [input.name, input.rolePattern, input.formula, input.annotations],
    input.span]

def Input.encodedRequest (input : Input) : Pattern :=
  projectionRequest input.officialSource input.skolem input.cnf

def Input.encodedTarget (input : Input) (polarity : Bool) : Pattern :=
  targetRequest
    (TptpFofClausificationBatchLanguageDef.encodeOccurrence input.occurrence)
    (TptpFofClausificationBatchLanguageDef.encodePolarity polarity)
    input.skolem input.cnf

private theorem encodeOfficialOccurrence_mk (digest indexLexeme : String) :
    TptpOfficialFofClausificationBatchAgreement.encodeOfficialOccurrence
        ⟨digest, indexLexeme⟩ =
      sourceOccurrence (atom digest) (atom indexLexeme) := by
  rfl

private theorem encodeBatchOccurrence_mk (digest indexLexeme : String) :
    TptpFofClausificationBatchLanguageDef.encodeOccurrence
        ⟨digest, indexLexeme⟩ =
      batchOccurrence (atom digest) (atom indexLexeme) := by
  rfl

private theorem encodeBatchPolarity_eq (polarity : Bool) :
    TptpFofClausificationBatchLanguageDef.encodePolarity polarity =
      TptpOfficialFofBatchProjectionLanguageDef.encodePolarity polarity := by
  cases polarity <;> rfl

private def concreteSourceFofInput (occurrence role name formula annotations
    span : Pattern) : Pattern :=
  a "tptp-semantic:fof-input" [occurrence,
    a "tptp92-ast:fof-annotated:alt-1"
      [name, role, formula, annotations], span]

private theorem officialSource_mk_none
    (digest indexLexeme : String) (role : FormulaRole)
    (name formula annotations span skolem cnf : Pattern) :
    Input.officialSource
        ⟨⟨digest, indexLexeme⟩, role, none, name, formula, annotations,
          span, skolem, cnf⟩ =
      concreteSourceFofInput
        (sourceOccurrence (atom digest) (atom indexLexeme))
        (plainRole role.code) name formula annotations span := by
  rfl

private theorem officialSource_mk_some
    (digest indexLexeme : String) (role : FormulaRole)
    (refinement name formula annotations span skolem cnf : Pattern) :
    Input.officialSource
        ⟨⟨digest, indexLexeme⟩, role, some refinement, name, formula,
          annotations, span, skolem, cnf⟩ =
      concreteSourceFofInput
        (sourceOccurrence (atom digest) (atom indexLexeme))
        (refinedRole role.code refinement) name formula annotations span := by
  rfl

/-- Root dispatch removes the imported batch-generation rows before any
pattern matching is attempted. -/
theorem projection_request_root_rules :
    TptpOfficialFofBatchProjectionLanguageDef.language.rewrites.filter
        (TptpOfficialFofToNamedFormulaLanguageDef.rootMatches
          "tptp-fof-batch-project:request") =
      TptpOfficialFofBatchProjectionLanguageDef.projectionRules := by
  rfl

private def projectionPair
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry) :
    List RewriteRule :=
  [TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule entry false,
   TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule entry true]

private theorem projectionRules_eq_role_pairs :
    TptpOfficialFofBatchProjectionLanguageDef.projectionRules =
      TptpOfficialFofBatchProjectionLanguageDef.rolePolicy.flatMap
        projectionPair := by
  rfl

/-- A projection row for one role cannot match a request for a distinct
role.  This is a structural property of the authored left-hand side, not a
rule-name convention. -/
private theorem mismatched_projection_rule_has_no_match
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (withRefinement sourceWithRefinement : Bool)
    (code : String) (occurrence name formula annotations span refinement
      skolem cnf : Pattern)
    (different : entry.code ≠ code) :
    matchPatternForRule
      TptpOfficialFofBatchProjectionLanguageDef.language
      (TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule entry
        withRefinement)
      (projectionRequest
        (concreteSourceFofInput occurrence
          (if sourceWithRefinement then refinedRole code refinement
           else plainRole code)
          name formula annotations span)
        skolem cnf) = [] := by
  rw [matchPatternForRule_eq_syntactic]
  cases withRefinement <;> cases sourceWithRefinement <;>
  simp [TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule,
    concreteSourceFofInput, projectionRequest, sourceFofInput,
    sourceOccurrence, plainRole, refinedRole, tokenLowerWord,
    TptpOfficialFofBatchProjectionLanguageDef.a,
    TptpOfficialFofBatchProjectionLanguageDef.v,
    matchPattern, matchArgs, mergeBindings, different]

private theorem mismatched_projection_rule_has_no_reduct
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (withRefinement sourceWithRefinement : Bool)
    (code : String) (occurrence name formula annotations span refinement
      skolem cnf : Pattern)
    (different : entry.code ≠ code) :
    applyRuleUsing base
      TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep
      (TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule entry
        withRefinement)
      (projectionRequest
        (concreteSourceFofInput occurrence
          (if sourceWithRefinement then refinedRole code refinement
           else plainRole code)
          name formula annotations span)
        skolem cnf) = [] := by
  rw [applyRuleUsing,
    mismatched_projection_rule_has_no_match entry withRefinement
      sourceWithRefinement code occurrence name formula annotations span
      refinement skolem cnf different]
  rfl

private theorem mismatched_projection_pair_has_no_reducts
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (sourceWithRefinement : Bool)
    (code : String) (occurrence name formula annotations span refinement
      skolem cnf : Pattern)
    (different : entry.code ≠ code) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput occurrence
            (if sourceWithRefinement then refinedRole code refinement
             else plainRole code)
            name formula annotations span)
          skolem cnf)) = [] := by
  simp only [projectionPair, List.flatMap_cons, List.flatMap_nil]
  rw [mismatched_projection_rule_has_no_reduct base recursiveStep entry false
      sourceWithRefinement code occurrence name formula annotations span
      refinement skolem cnf different,
    mismatched_projection_rule_has_no_reduct base recursiveStep entry true
      sourceWithRefinement code occurrence name formula annotations span
      refinement skolem cnf different]
  rfl

private theorem mismatched_projection_pair_plain_has_no_reducts
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (code : String) (occurrence name formula annotations span skolem cnf : Pattern)
    (different : entry.code ≠ code) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput occurrence (plainRole code)
            name formula annotations span)
          skolem cnf)) = [] := by
  simpa using mismatched_projection_pair_has_no_reducts base recursiveStep
    entry false code occurrence name formula annotations span (atom "") skolem cnf
    different

private theorem mismatched_projection_pair_refined_has_no_reducts
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (code : String) (occurrence name formula annotations span refinement
      skolem cnf : Pattern)
    (different : entry.code ≠ code) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput occurrence (refinedRole code refinement)
            name formula annotations span)
          skolem cnf)) = [] := by
  simpa using mismatched_projection_pair_has_no_reducts base recursiveStep
    entry true code occurrence name formula annotations span refinement skolem cnf
    different

private theorem matching_projection_pair_plain_exact
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (digest index name formula annotations span skolem cnf : Pattern) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput (sourceOccurrence digest index)
            (plainRole entry.code) name formula annotations span)
          skolem cnf)) =
      [targetRequest (batchOccurrence digest index)
        (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
          entry.polarity) skolem cnf] := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;>
  simp [projectionPair,
    TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule,
    concreteSourceFofInput, projectionRequest, targetRequest,
    sourceFofInput, sourceOccurrence, sourceDigest, batchOccurrence, plainRole,
    refinedRole, tokenLowerWord,
    TptpOfficialFofBatchProjectionLanguageDef.a,
    TptpOfficialFofBatchProjectionLanguageDef.v,
    TptpFofClausificationBatchGenerationLanguageDef.request,
    TptpFofClausificationBatchGenerationLanguageDef.a,
    applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

private theorem matching_projection_pair_refined_exact
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (digest index name formula annotations span refinement skolem cnf : Pattern) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput (sourceOccurrence digest index)
            (refinedRole entry.code refinement) name formula annotations span)
          skolem cnf)) =
      [targetRequest (batchOccurrence digest index)
        (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
          entry.polarity) skolem cnf] := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;>
  simp [projectionPair,
    TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule,
    concreteSourceFofInput, projectionRequest, targetRequest,
    sourceFofInput, sourceOccurrence, sourceDigest, batchOccurrence, plainRole,
    refinedRole, tokenLowerWord,
    TptpOfficialFofBatchProjectionLanguageDef.a,
    TptpOfficialFofBatchProjectionLanguageDef.v,
    TptpFofClausificationBatchGenerationLanguageDef.request,
    TptpFofClausificationBatchGenerationLanguageDef.a,
    applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, matchPattern, matchArgs, mergeBindings,
    applyBindingsForRule, applyBindings]

private theorem projection_pair_plain_dispatch
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (code : String) (digest index name formula annotations span skolem cnf : Pattern) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput (sourceOccurrence digest index)
            (plainRole code) name formula annotations span)
          skolem cnf)) =
      if entry.code = code then
        [targetRequest (batchOccurrence digest index)
          (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
            entry.polarity) skolem cnf]
      else [] := by
  by_cases same : entry.code = code
  · subst code
    simpa using matching_projection_pair_plain_exact base recursiveStep entry
      digest index name formula annotations span skolem cnf
  · simpa [same] using mismatched_projection_pair_plain_has_no_reducts
      base recursiveStep entry code (sourceOccurrence digest index) name formula
      annotations span skolem cnf same

private theorem projection_pair_refined_dispatch
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (entry : TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (code : String) (digest index name formula annotations span refinement
      skolem cnf : Pattern) :
    (projectionPair entry).flatMap
      (fun rule => applyRuleUsing base
        TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
        (projectionRequest
          (concreteSourceFofInput (sourceOccurrence digest index)
            (refinedRole code refinement) name formula annotations span)
          skolem cnf)) =
      if entry.code = code then
        [targetRequest (batchOccurrence digest index)
          (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
            entry.polarity) skolem cnf]
      else [] := by
  by_cases same : entry.code = code
  · subst code
    simpa using matching_projection_pair_refined_exact base recursiveStep entry
      digest index name formula annotations span refinement skolem cnf
  · simpa [same] using mismatched_projection_pair_refined_has_no_reducts
      base recursiveStep entry code (sourceOccurrence digest index) name formula
      annotations span refinement skolem cnf same

private theorem projection_pairs_plain_dispatch
    (entries : List
      TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (code : String) (digest index name formula annotations span skolem cnf : Pattern) :
    entries.flatMap (fun entry =>
      (projectionPair entry).flatMap
        (fun rule => applyRuleUsing base
          TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
          (projectionRequest
            (concreteSourceFofInput (sourceOccurrence digest index)
              (plainRole code) name formula annotations span)
            skolem cnf))) =
      entries.flatMap (fun entry =>
        if entry.code = code then
          [targetRequest (batchOccurrence digest index)
            (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
              entry.polarity) skolem cnf]
        else []) := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.flatMap_cons]
      rw [projection_pair_plain_dispatch, inductionHypothesis]

private theorem projection_pairs_refined_dispatch
    (entries : List
      TptpOfficialFofBatchProjectionLanguageDef.RolePolicyEntry)
    (base : BasePremiseEvaluator) (recursiveStep : Pattern → List Pattern)
    (code : String) (digest index name formula annotations span refinement
      skolem cnf : Pattern) :
    entries.flatMap (fun entry =>
      (projectionPair entry).flatMap
        (fun rule => applyRuleUsing base
          TptpOfficialFofBatchProjectionLanguageDef.language recursiveStep rule
          (projectionRequest
            (concreteSourceFofInput (sourceOccurrence digest index)
              (refinedRole code refinement) name formula annotations span)
            skolem cnf))) =
      entries.flatMap (fun entry =>
        if entry.code = code then
          [targetRequest (batchOccurrence digest index)
            (TptpOfficialFofBatchProjectionLanguageDef.encodePolarity
              entry.polarity) skolem cnf]
        else []) := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [List.flatMap_cons]
      rw [projection_pair_refined_dispatch, inductionHypothesis]

private theorem projectionRequest_fold
    (source skolem cnf : Pattern) :
    Pattern.apply "tptp-fof-batch-project:request" [source, skolem, cnf] =
      projectionRequest source skolem cnf := by
  rfl

local syntax "projection_root" term : tactic

local macro_rules
  | `(tactic| projection_root $input:term) =>
  `(tactic|
    rcases ($input) with
      ⟨occurrence, role, refinement, name, formula, annotations, span,
        skolem, cnf⟩ <;>
    rcases occurrence with ⟨digest, indexLexeme⟩ <;>
    simp only at * <;>
    subst role <;>
    cases refinement <;>
    simp only [Input.encodedRequest, projectionRequest,
      TptpOfficialFofBatchProjectionLanguageDef.a] <;>
    rw [TptpOfficialFofToNamedFormulaLanguageDef.rewriteAt_eq_root_filter] <;>
    rw [projection_request_root_rules] <;>
    simp only [officialSource_mk_none, officialSource_mk_some] <;>
    rw [projectionRequest_fold] <;>
    rw [projectionRules_eq_role_pairs, List.flatMap_assoc] <;>
    (first
      | rw [projection_pairs_plain_dispatch]
      | rw [projection_pairs_refined_dispatch]) <;>
    simp only [TptpOfficialFofBatchProjectionLanguageDef.rolePolicy,
      List.flatMap_cons, List.flatMap_nil,
      TptpOfficialRoleSemantics.FormulaRole.code] <;>
    try simp only [
      TptpOfficialFofBatchProjectionLanguageDef.encodePolarity_true,
      TptpOfficialFofBatchProjectionLanguageDef.encodePolarity_false] <;>
    simp_all [
      matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpOfficialFofBatchProjectionLanguageDef.mkProjectionRule,
      projectionRequest, targetRequest, sourceFofInput,
      sourceOccurrence, sourceDigest, batchOccurrence, plainRole,
      refinedRole, tokenLowerWord,
      TptpOfficialFofBatchProjectionLanguageDef.a,
      TptpOfficialFofBatchProjectionLanguageDef.v,
      TptpFofClausificationBatchGenerationLanguageDef.request,
      TptpFofClausificationBatchGenerationLanguageDef.a,
      encodeBatchOccurrence_mk, encodeBatchPolarity_eq,
      Input.encodedRequest, Input.encodedTarget, atom,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

private theorem axiom_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .axiom) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem hypothesis_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .hypothesis) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem definition_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .definition) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem assumption_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .assumption) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem lemma_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .lemma) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem theorem_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .theorem) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem corollary_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .corollary) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem conjecture_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .conjecture) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget false] := by
  projection_root input

private theorem negatedConjecture_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .negatedConjecture) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem plain_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .plain) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [input.encodedTarget true] := by
  projection_root input

private theorem type_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .type) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

private theorem interpretation_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .interpretation) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

private theorem finiteInterpretationDomain_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .finiteInterpretationDomain) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

private theorem finiteInterpretationFunctors_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .finiteInterpretationFunctors) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

private theorem finiteInterpretationPredicates_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .finiteInterpretationPredicates) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

private theorem unknown_rewriteAt_exact (fuel : Nat) (input : Input)
    (roleExact : input.role = .unknown) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language (fuel + 1)
      input.encodedRequest = [] := by
  projection_root input

/-- Every supported official role has exactly one metadata-projection reduct. -/
theorem Input.rewriteAt_exact (input : Input) (polarity : Bool)
    (evidence : SupportedRole input.role polarity) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      input.encodedRequest = [input.encodedTarget polarity] := by
  generalize roleExact : input.role = role at evidence
  cases evidence
  · exact axiom_rewriteAt_exact 0 input roleExact
  · exact hypothesis_rewriteAt_exact 0 input roleExact
  · exact definition_rewriteAt_exact 0 input roleExact
  · exact assumption_rewriteAt_exact 0 input roleExact
  · exact lemma_rewriteAt_exact 0 input roleExact
  · exact theorem_rewriteAt_exact 0 input roleExact
  · exact corollary_rewriteAt_exact 0 input roleExact
  · exact conjecture_rewriteAt_exact 0 input roleExact
  · exact negatedConjecture_rewriteAt_exact 0 input roleExact
  · exact plain_rewriteAt_exact 0 input roleExact

/-- Exact singleton execution implies result-level no invention. -/
theorem Input.no_invention (input : Input) (polarity : Bool)
    (evidence : SupportedRole input.role polarity) (candidate : Pattern)
    (membership : candidate ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      input.encodedRequest) :
    candidate = input.encodedTarget polarity := by
  rw [input.rewriteAt_exact polarity evidence] at membership
  simpa using membership

/-- Unsupported official roles produce no projection reduct, in either the
plain or refined concrete role form. -/
theorem Input.unsupported_rewriteAt_exact (input : Input)
    (evidence : UnsupportedRole input.role) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      input.encodedRequest = [] := by
  generalize roleExact : input.role = role at evidence
  cases evidence
  · exact type_rewriteAt_exact 0 input roleExact
  · exact interpretation_rewriteAt_exact 0 input roleExact
  · exact finiteInterpretationDomain_rewriteAt_exact 0 input roleExact
  · exact finiteInterpretationFunctors_rewriteAt_exact 0 input roleExact
  · exact finiteInterpretationPredicates_rewriteAt_exact 0 input roleExact
  · exact unknown_rewriteAt_exact 0 input roleExact

/-! ## Composition with prepared official sources -/

def canonicalRolePattern (role : FormulaRole)
    (refinement : Option Pattern) : Pattern :=
  match refinement with
  | none => plainRole role.code
  | some payload => refinedRole role.code payload

/-- A prepared official source is projection-ready exactly when its retained
role syntax is one of the two official lower-word presentations implemented by
the projection LanguageDef.  This is representation evidence, not semantic
authority: the decoded `FormulaRole` and its polarity remain independently
established by `PreparedSource`. -/
structure PreparedProjection where
  source : TptpOfficialFofClausificationBatchAgreement.PreparedSource
  refinement : Option Pattern
  rolePresentation :
    source.sourceNode.role = canonicalRolePattern source.role refinement

def PreparedProjection.canonicalSourceView
    (projection : PreparedProjection) :
    TptpOfficialSemanticCarrier.AnnotatedInputView := {
  occurrence :=
    TptpOfficialFofClausificationBatchAgreement.encodeOfficialOccurrence
      projection.source.occurrence
  payload := .fof (.apply "tptp92-ast:fof-annotated:alt-1" [
    projection.source.sourceNode.name,
    projection.source.sourceNode.role,
    projection.source.sourceNode.formula,
    TptpOfficialDerivationSyntax.encodeAnnotations
      projection.source.sourceNode.annotation])
  span := projection.source.sourceNode.span
}

noncomputable def PreparedProjection.toInput
    (projection : PreparedProjection) (namingFrontier : Nat) : Input :=
  let batchInput := projection.source.toBatchInput namingFrontier
  {
    occurrence := projection.source.occurrence
    role := projection.source.role
    refinement := projection.refinement
    name := projection.source.sourceNode.name
    formula := projection.source.sourceNode.formula
    annotations := TptpOfficialDerivationSyntax.encodeAnnotations
      projection.source.sourceNode.annotation
    span := projection.source.sourceNode.span
    skolem := TptpFofSkolemLanguageDef.encodeOutput batchInput.skolemOutput
      batchInput.namingEvidence.existentialFree
    cnf := TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput
      batchInput.namedOutput batchInput.definitionQuantifierFree
  }

/-- The source side of the projection is the canonical semantic-carrier
encoding of the prepared official metadata. -/
theorem PreparedProjection.officialSource_eq_canonicalSourceView
    (projection : PreparedProjection) (namingFrontier : Nat) :
    (projection.toInput namingFrontier).officialSource =
      TptpOfficialSemanticCarrier.encodeAnnotatedInput
        projection.canonicalSourceView := by
  unfold PreparedProjection.toInput Input.officialSource
    Input.officialOccurrence PreparedProjection.canonicalSourceView
    TptpOfficialSemanticCarrier.encodeAnnotatedInput
  rw [projection.rolePresentation]
  cases projection.refinement <;> rfl

/-- The projection target is literally the request consumed by the already
verified batch-generation arrow. -/
theorem PreparedProjection.encodedTarget_eq_batchRequest
    (projection : PreparedProjection) (namingFrontier : Nat) :
    (projection.toInput namingFrontier).encodedTarget
        projection.source.polarity =
      (projection.source.toBatchInput namingFrontier).encodedRequest := by
  rfl

/-- A prepared source crosses the metadata projection in exactly one step and
lands on the exact request for the next authored GSLT arrow. -/
theorem PreparedProjection.rewriteAt_exact
    (projection : PreparedProjection) (namingFrontier : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (projection.toInput namingFrontier).encodedRequest =
        [(projection.source.toBatchInput namingFrontier).encodedRequest] := by
  calc
    _ = [(projection.toInput namingFrontier).encodedTarget
          projection.source.polarity] :=
      (projection.toInput namingFrontier).rewriteAt_exact
        projection.source.polarity
        (supportedRoleOfPolarityExact projection.source.polarityExact)
    _ = _ := by rw [projection.encodedTarget_eq_batchRequest namingFrontier]

theorem PreparedProjection.no_invention
    (projection : PreparedProjection) (namingFrontier : Nat)
    (candidate : Pattern)
    (membership : candidate ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (projection.toInput namingFrontier).encodedRequest) :
    candidate =
      (projection.source.toBatchInput namingFrontier).encodedRequest := by
  rw [projection.rewriteAt_exact namingFrontier] at membership
  simpa using membership

/-- Source metadata is absent from the target by construction. -/
theorem encodedTarget_independent_of_metadata
    (occurrence : SourceOccurrence) (role : FormulaRole)
    (leftRefinement rightRefinement : Option Pattern)
    (leftName rightName leftFormula rightFormula : Pattern)
    (leftAnnotations rightAnnotations leftSpan rightSpan : Pattern)
    (skolem cnf : Pattern) (polarity : Bool) :
    (Input.mk occurrence role leftRefinement leftName leftFormula
        leftAnnotations leftSpan skolem cnf).encodedTarget polarity =
      (Input.mk occurrence role rightRefinement rightName rightFormula
        rightAnnotations rightSpan skolem cnf).encodedTarget polarity := by
  rfl

namespace Canary

def occurrence : SourceOccurrence := ⟨"source-digest", "7"⟩

def input (role : FormulaRole) (refinement : Option Pattern := none) : Input := {
  occurrence
  role
  refinement
  name := atom "formula-name"
  formula := atom "formula-body"
  annotations := atom "annotations"
  span := atom "source-span"
  skolem := atom "skolem-output"
  cnf := atom "cnf-output"
}

noncomputable def preparedAxiomProjection : PreparedProjection := {
  source :=
    TptpOfficialFofClausificationBatchAgreement.Canary.preparedAxiom
  refinement := none
  rolePresentation := rfl
}

theorem prepared_axiom_crosses_to_batch_request :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (preparedAxiomProjection.toInput 0).encodedRequest =
        [(preparedAxiomProjection.source.toBatchInput 0).encodedRequest] := by
  exact preparedAxiomProjection.rewriteAt_exact 0

theorem conjecture_projects_negative :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (input .conjecture).encodedRequest =
        [(input .conjecture).encodedTarget false] := by
  exact (input .conjecture).rewriteAt_exact false .conjecture

theorem refined_axiom_projects_positive :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (input .axiom (some (atom "derived"))).encodedRequest =
        [(input .axiom (some (atom "derived"))).encodedTarget true] := by
  exact (input .axiom (some (atom "derived"))).rewriteAt_exact true .axiom

theorem type_role_is_rejected :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (input .type).encodedRequest = [] := by
  exact (input .type).unsupported_rewriteAt_exact .type

theorem unknown_role_is_rejected :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpOfficialFofBatchProjectionLanguageDef.language 1
      (input .unknown).encodedRequest = [] := by
  exact (input .unknown).unsupported_rewriteAt_exact .unknown

end Canary

#print axioms SupportedRole.polarity_exact
#print axioms UnsupportedRole.polarity_absent
#print axioms Input.rewriteAt_exact
#print axioms Input.no_invention
#print axioms Input.unsupported_rewriteAt_exact
#print axioms PreparedProjection.officialSource_eq_canonicalSourceView
#print axioms PreparedProjection.encodedTarget_eq_batchRequest
#print axioms PreparedProjection.rewriteAt_exact
#print axioms PreparedProjection.no_invention
#print axioms encodedTarget_independent_of_metadata
#print axioms Canary.prepared_axiom_crosses_to_batch_request
#print axioms Canary.conjecture_projects_negative
#print axioms Canary.refined_axiom_projects_positive
#print axioms Canary.type_role_is_rejected
#print axioms Canary.unknown_role_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionAgreement
