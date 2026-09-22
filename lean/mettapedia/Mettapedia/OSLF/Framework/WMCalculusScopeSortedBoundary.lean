import Mettapedia.OSLF.Framework.WMCalculusOverlapSortedBoundary

/-!
# A checked guarded forgetting vertex

The `Forget` constructor has a scope argument and a state argument. Its
outside-scope observation rule is guarded; declaring the constructor does not
erase that premise or turn forgetting into unconditional observation equality.
This module checks formation and rule sorting for the scope-only vertex, not
semantic soundness of an arbitrary relation environment.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Mettapedia.OSLF.Framework.WMCalculusScopeSortedBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

def scopeOnlyVertex : WMExtVertex :=
  {wmExtVertexMinimal with forgetting := .scopeBased}

theorem scopeOnly_types :
    (wmExtVertexLanguageDefGuarded scopeOnlyVertex).types =
      ["State", "Query", "BinaryEvidence", "Scope"] := rfl

theorem scopeOnly_terms :
    (wmExtVertexLanguageDefGuarded scopeOnlyVertex).terms =
      coreTerms ++ [forgetDecl] := rfl

private def checkedLanguage : LanguageDef :=
  LanguageDef.ofCore "WMCalculusGuarded"
    ["State", "Query", "BinaryEvidence", "Scope"]
    (coreTerms ++ [forgetDecl]) []
    (coreRules ++ [ruleForgetOutsideGuarded, ruleForgetIdempotent])

private theorem checkedLanguage_eq :
    wmExtVertexLanguageDefGuarded scopeOnlyVertex = checkedLanguage := rfl

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

theorem scopeOnly_validation :
    (wmExtVertexLanguageDefGuarded scopeOnlyVertex).validate = [] := by
  rw [checkedLanguage_eq]
  have coreRows : coreRules.flatMap (LanguageDef.validateRewrite checkedLanguage) = [] := by
    simp only [coreRules, List.flatMap_cons, List.flatMap_nil,
      checked_evidenceAdd, checked_revisionComm, checked_revisionAssoc,
      checked_combineComm, checked_combineZero, List.nil_append]
  rw [LanguageDef.validate]
  simp only [List.append_eq_nil_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try decide +kernel
  change (coreRules ++ [ruleForgetOutsideGuarded, ruleForgetIdempotent]).flatMap
    (LanguageDef.validateRewrite checkedLanguage) = []
  simp only [List.flatMap_append, coreRows, List.flatMap_cons,
    checked_forgetOutside, checked_forgetIdempotent,
    List.flatMap_nil, List.nil_append]

theorem scopeOnly_rewrites_checked :
    (wmExtVertexLanguageDefGuarded scopeOnlyVertex).rewrites.all
      (checkRewriteWellSorted
        (wmExtVertexLanguageDefGuarded scopeOnlyVertex)) = true := by
  decide +kernel

/-- The guard is part of the authored rule and is not discarded by the typed
signature extension. -/
theorem forgetOutside_has_guard :
    ruleForgetOutsideGuarded.premises =
      [.relationQuery "outsideScope" [.fvar "S", .fvar "q"]] := rfl

theorem forgetOutside_sorted :
    RewriteWellSorted (wmExtVertexLanguageDefGuarded scopeOnlyVertex)
      ruleForgetOutsideGuarded := by
  apply checkRewriteWellSorted_sound
  exact (List.all_eq_true.mp scopeOnly_rewrites_checked) _
    (by simp [wmExtVertexLanguageDefGuarded, scopeOnlyVertex,
      forgettingRulesGuarded])

/-- The no-forgetting vertex does not silently gain a state mutation. -/
theorem noForgettingVertex_has_no_forget :
    forgetDecl ∉ (wmExtVertexLanguageDefGuarded wmExtVertexMinimal).terms := by
  decide +kernel

#print axioms scopeOnly_validation
#print axioms scopeOnly_rewrites_checked
#print axioms forgetOutside_sorted
#print axioms noForgettingVertex_has_no_forget

end Mettapedia.OSLF.Framework.WMCalculusScopeSortedBoundary
