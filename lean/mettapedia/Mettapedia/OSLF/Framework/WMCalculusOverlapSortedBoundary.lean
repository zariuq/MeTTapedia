import Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# A checked overlap-aware WM vertex

The overlap correction carrier in the underlying `OverlapLayer` is independent
of the evidence carrier. The authored overlap-aware vertex therefore declares
an `Overlap` sort, along with `OverlapMerge`, `OverlapFactor`, and
`OverlapCorrect`. This module checks the smallest vertex that exercises that
axis, without asserting that the other WM extension axes are already sorted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.OSLF.Framework.WMCalculusOverlapSortedBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.RedexPosition

/-- The first guarded vertex whose grammar adds a genuinely new sort and
three constructors to the four-constructor core. -/
def overlapOnlyVertex : WMExtVertex :=
  {wmExtVertexMinimal with overlap := .overlapAware}

theorem overlapOnly_types :
    (wmExtVertexLanguageDefGuarded overlapOnlyVertex).types =
      ["State", "Query", "BinaryEvidence", "Overlap"] := rfl

theorem overlapOnly_terms :
    (wmExtVertexLanguageDefGuarded overlapOnlyVertex).terms =
      coreTerms ++ [overlapMergeDecl, overlapFactorDecl,
        overlapCorrectDecl] := rfl

private def checkedLanguage : LanguageDef :=
  LanguageDef.ofCore "WMCalculusGuarded"
    ["State", "Query", "BinaryEvidence", "Overlap"]
    (coreTerms ++ [overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl])
    [] (coreRules ++ [ruleOverlapExtract])

private theorem checkedLanguage_eq :
    wmExtVertexLanguageDefGuarded overlapOnlyVertex = checkedLanguage := rfl

set_option maxHeartbeats 2000000

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

theorem overlapOnly_validation :
    (wmExtVertexLanguageDefGuarded overlapOnlyVertex).validate = [] := by
  rw [checkedLanguage_eq]
  have coreRows : coreRules.flatMap (LanguageDef.validateRewrite checkedLanguage) = [] := by
    simp only [coreRules, List.flatMap_cons, List.flatMap_nil,
      checked_evidenceAdd, checked_revisionComm, checked_revisionAssoc,
      checked_combineComm, checked_combineZero, List.nil_append]
  rw [LanguageDef.validate]
  simp only [List.append_eq_nil_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try decide +kernel
  change (coreRules ++ [ruleOverlapExtract]).flatMap
    (LanguageDef.validateRewrite checkedLanguage) = []
  simp only [List.flatMap_append, coreRows, List.flatMap_cons,
    checked_overlapExtract, List.flatMap_nil, List.nil_append]

set_option maxHeartbeats 2000000 in
theorem overlapOnly_rewrites_checked :
    (wmExtVertexLanguageDefGuarded overlapOnlyVertex).rewrites.all
      (checkRewriteWellSorted
        (wmExtVertexLanguageDefGuarded overlapOnlyVertex)) = true := by
  decide +kernel

/-- The overlap rule's source and target share the authored evidence sort;
its correction subterm is separately typed as `Overlap`. -/
theorem overlapExtract_sorted :
    RewriteWellSorted (wmExtVertexLanguageDefGuarded overlapOnlyVertex)
      ruleOverlapExtract := by
  apply checkRewriteWellSorted_sound
  exact (List.all_eq_true.mp overlapOnly_rewrites_checked) _
    (by simp [wmExtVertexLanguageDefGuarded, overlapOnlyVertex,
      overlapRules])

private def overlapFree : FreeTypeContext :=
  FreeTypeContext.ofList
    [("w1", .base "State"), ("w2", .base "State"), ("q", .base "Query")]

/-- Treating the correction factor itself as evidence is rejected by the
declaration-derived checker; the `Ov = Ev` specialization is not forced. -/
theorem overlapFactor_not_evidence :
    ¬ HasType (wmExtVertexLanguageDefGuarded overlapOnlyVertex)
      overlapFree
      []
      (pOverlapFactor (.fvar "w1") (.fvar "w2") (.fvar "q"))
      (.base "BinaryEvidence") := by
  intro typed
  have accepted := (checkHasType_eq_true_iff (by decide +kernel)).2 typed
  have rejected :
      checkHasType (wmExtVertexLanguageDefGuarded overlapOnlyVertex)
        overlapFree
        [] (pOverlapFactor (.fvar "w1") (.fvar "w2") (.fvar "q"))
        (.base "BinaryEvidence") = false := by
    decide +kernel
  rw [rejected] at accepted
  cases accepted

/-- The additive vertex does not silently acquire an overlap constructor. -/
theorem additive_vertex_has_no_overlapFactor :
    overlapFactorDecl ∉ (wmExtVertexLanguageDefGuarded wmExtVertexMinimal).terms := by
  decide +kernel

#print axioms overlapOnly_validation
#print axioms overlapOnly_rewrites_checked
#print axioms overlapExtract_sorted
#print axioms overlapFactor_not_evidence

end Mettapedia.OSLF.Framework.WMCalculusOverlapSortedBoundary
