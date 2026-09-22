import Mettapedia.OSLF.Framework.WMCalculusScopeSortedBoundary

/-!
# Combined overlap and scope formation

The two guarded axes share the four-constructor WM core but add distinct
sorts, constructor rows, and rewrite rows. This module checks their first
combined vertex directly and exhibits a nested term using both operations.
It does not identify structural validation with semantic compatibility of
arbitrary overlap and forgetting models.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

def combinedVertex : WMExtVertex :=
  {wmExtVertexMinimal with overlap := .overlapAware, forgetting := .scopeBased}

theorem combined_types :
    (wmExtVertexLanguageDefGuarded combinedVertex).types =
      ["State", "Query", "BinaryEvidence", "Overlap", "Scope"] := rfl

theorem combined_terms :
    (wmExtVertexLanguageDefGuarded combinedVertex).terms =
      coreTerms ++ [overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl]
        ++ [forgetDecl] := rfl

/-- Constructor inversion for the one authored combined signature. No
semantic constructor is added outside this validated inventory. -/
theorem combined_declaration_cases {rule : GrammarRule}
    (member : rule ∈ (wmExtVertexLanguageDefGuarded combinedVertex).terms) :
    rule = reviseDecl ∨ rule = extractDecl ∨ rule = combineDecl ∨
      rule = evidenceZeroDecl ∨ rule = overlapMergeDecl ∨
      rule = overlapFactorDecl ∨ rule = overlapCorrectDecl ∨
      rule = forgetDecl := by
  rw [combined_terms] at member
  simpa only [coreTerms, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] using member

private def checkedLanguage : LanguageDef :=
  LanguageDef.ofCore "WMCalculusGuarded"
    ["State", "Query", "BinaryEvidence", "Overlap", "Scope"]
    (coreTerms ++ [overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl]
      ++ [forgetDecl]) []
    (coreRules ++ [ruleOverlapExtract] ++
      [ruleForgetOutsideGuarded, ruleForgetIdempotent])

private theorem checkedLanguage_eq :
    wmExtVertexLanguageDefGuarded combinedVertex = checkedLanguage := rfl

private theorem checked_evidenceAdd :
    checkedLanguage.validateRewrite ruleEvidenceAdd = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleEvidenceAdd, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_revisionComm :
    checkedLanguage.validateRewrite ruleRevisionComm = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleRevisionComm, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_revisionAssoc :
    checkedLanguage.validateRewrite ruleRevisionAssoc = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleRevisionAssoc, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_combineComm :
    checkedLanguage.validateRewrite ruleCombineComm = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleCombineComm, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_combineZero :
    checkedLanguage.validateRewrite ruleCombineZero = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleCombineZero, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_overlapExtract :
    checkedLanguage.validateRewrite ruleOverlapExtract = [] := by
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleOverlapExtract, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_forgetOutside :
    checkedLanguage.validateRewrite ruleForgetOutsideGuarded = [] := by
  simp only [LanguageDef.validateRewrite, ruleForgetOutsideGuarded,
    List.append_eq_nil_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try decide +kernel
  simp only [LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    List.flatMap_cons, List.flatMap_nil, List.nil_append]
  decide +kernel

private theorem checked_forgetIdempotent :
    checkedLanguage.validateRewrite ruleForgetIdempotent = [] := by
  simp only [LanguageDef.validateRewrite, ruleForgetIdempotent,
    List.append_eq_nil_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try decide +kernel
  simp only [LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

theorem combined_validation :
    (wmExtVertexLanguageDefGuarded combinedVertex).validate = [] := by
  rw [checkedLanguage_eq]
  have coreRows : coreRules.flatMap (LanguageDef.validateRewrite checkedLanguage) = [] := by
    simp only [coreRules, List.flatMap_cons, List.flatMap_nil,
      checked_evidenceAdd, checked_revisionComm, checked_revisionAssoc,
      checked_combineComm, checked_combineZero, List.nil_append]
  rw [LanguageDef.validate]
  simp only [List.append_eq_nil_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try decide +kernel
  change (coreRules ++ [ruleOverlapExtract] ++
    [ruleForgetOutsideGuarded, ruleForgetIdempotent]).flatMap
      (LanguageDef.validateRewrite checkedLanguage) = []
  simp only [List.flatMap_append, coreRows, List.flatMap_cons,
    checked_overlapExtract, checked_forgetOutside, checked_forgetIdempotent,
    List.flatMap_nil, List.nil_append]

/-- Validation of the authored combined language licenses deterministic
constructor lookup by label. -/
theorem combined_constructor_labels_nodup :
    ((wmExtVertexLanguageDefGuarded combinedVertex).terms.map (·.label)).Nodup :=
  LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ combined_validation

private theorem combined_simple_parameter_check :
    (wmExtVertexLanguageDefGuarded combinedVertex).terms.all
      (fun rule => rule.params.all fun parameter =>
        match parameter with
        | .simple _ _ => true
        | _ => false) = true := by
  rw [combined_terms]
  decide +kernel

/-- No authored combined-WM constructor binds an argument. This is the
precise scope fact needed when inverting first-order typed captures. -/
theorem combined_declaration_parameter_simple {rule : GrammarRule}
    (member : rule ∈ (wmExtVertexLanguageDefGuarded combinedVertex).terms)
    {parameter : TermParam} (parameterMember : parameter ∈ rule.params) :
    ∃ (parameterName : String) (parameterSort : TypeExpr),
      parameter = .simple parameterName parameterSort := by
  have ruleSimple :=
    (List.all_eq_true.mp combined_simple_parameter_check) rule member
  have parameterSimple := (List.all_eq_true.mp ruleSimple)
    parameter parameterMember
  cases parameter with
  | simple parameterName parameterSort =>
      exact ⟨parameterName, parameterSort, rfl⟩
  | abstractionNamed binder parameterName parameterSort =>
      simp at parameterSimple
  | multiAbstractionNamed binders parameterName parameterSort =>
      simp at parameterSimple

theorem combined_rewrites_checked :
    (wmExtVertexLanguageDefGuarded combinedVertex).rewrites.all
      (checkRewriteWellSorted
        (wmExtVertexLanguageDefGuarded combinedVertex)) = true := by
  decide +kernel

private def combinedFree : FreeTypeContext :=
  FreeTypeContext.ofList
    [("S", .base "Scope"), ("W1", .base "State"),
     ("W2", .base "State"), ("q", .base "Query")]

private def nestedObservation : Pattern :=
  pExtract (pForget (.fvar "S")
    (pOverlapMerge (.fvar "W1") (.fvar "W2"))) (.fvar "q")

/-- An observation can cross both newly declared operations in one term. -/
theorem nestedObservation_typed :
    HasType (wmExtVertexLanguageDefGuarded combinedVertex)
      combinedFree [] nestedObservation (.base "BinaryEvidence") := by
  exact (checkHasType_eq_true_iff (by decide +kernel)).1 (by decide +kernel)

/-- An overlap factor cannot masquerade as the scope argument of `Forget`. -/
theorem overlapFactor_not_scope :
    ¬ HasType (wmExtVertexLanguageDefGuarded combinedVertex)
      combinedFree []
      (pForget (pOverlapFactor (.fvar "W1") (.fvar "W2") (.fvar "q"))
        (.fvar "W1")) (.base "State") := by
  intro typed
  have accepted := (checkHasType_eq_true_iff (by decide +kernel)).2 typed
  have rejected :
      checkHasType (wmExtVertexLanguageDefGuarded combinedVertex)
        combinedFree []
        (pForget (pOverlapFactor (.fvar "W1") (.fvar "W2") (.fvar "q"))
          (.fvar "W1")) (.base "State") = false := by
    decide +kernel
  rw [rejected] at accepted
  cases accepted

#print axioms combined_validation
#print axioms combined_declaration_cases
#print axioms combined_constructor_labels_nodup
#print axioms combined_declaration_parameter_simple
#print axioms combined_rewrites_checked
#print axioms nestedObservation_typed
#print axioms overlapFactor_not_scope

end Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
