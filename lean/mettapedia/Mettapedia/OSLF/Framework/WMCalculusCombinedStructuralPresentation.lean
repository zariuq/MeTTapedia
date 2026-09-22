import Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport

/-!
# A structural-equation presentation of the guarded overlap/scope vertex

The directed combined vertex and the structural WM core have different rule
inventories. This presentation retains the combined typed grammar and guarded
extension rules, places the three evidence monoid laws in the equation list,
and keeps extraction computational. Core congruence rules and the complete
argument-position inventory for the four added constructors are retained.
This does not yet give a semantic reading of combined overlap and forgetting.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
open Mettapedia.OSLF.Framework.RedexPosition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The guarded extension computations, with the outside-scope premise
retained on its authored rule. -/
def extensionComputations : List RewriteRule :=
  [ruleOverlapExtract, ruleForgetOutsideGuarded, ruleForgetIdempotent]

def combinedStructuralLanguageDef : LanguageDef :=
  LanguageDef.ofCore "WMCalculusCombinedStructural"
    ["State", "Query", "BinaryEvidence", "Overlap", "Scope"]
    [reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
      overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl, forgetDecl]
    structuralEquations
    (computationalRules ++ extensionComputations ++ coreCongruenceRules ++
      combinedExtensionCongruenceRules)

private def checkedSignature : LanguageDef :=
  LanguageDef.ofCore "WMCalculusCombinedSignature"
    ["State", "Query", "BinaryEvidence", "Overlap", "Scope"]
    [reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
      overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl, forgetDecl] [] []

private theorem checkedSignature_typeNames :
    checkedSignature.typeNames =
      ["State", "Query", "BinaryEvidence", "Overlap", "Scope"] := rfl

private theorem checkedSignature_terms :
    checkedSignature.terms =
      [reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
        overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl, forgetDecl] := rfl

/-- The intended separation of equations from computations is literal in
the authored record, not inferred from a semantic commutative monoid. -/
theorem combinedStructural_inventory :
    combinedStructuralLanguageDef.equations = structuralEquations ∧
    combinedStructuralLanguageDef.rewrites =
      computationalRules ++ extensionComputations ++ coreCongruenceRules ++
        combinedExtensionCongruenceRules := ⟨rfl, rfl⟩

private theorem sameTermValidation (term : GrammarRule) :
    combinedStructuralLanguageDef.validateTerm term =
      (wmExtVertexLanguageDefGuarded combinedVertex).validateTerm term := rfl

private theorem sameEquationValidation (equation : Equation) :
    combinedStructuralLanguageDef.validateEquation equation =
      (wmExtVertexLanguageDefGuarded combinedVertex).validateEquation equation := rfl

private theorem sameRewriteValidation (rule : RewriteRule) :
    combinedStructuralLanguageDef.validateRewrite rule =
      (wmExtVertexLanguageDefGuarded combinedVertex).validateRewrite rule := rfl

private theorem sameEquationSignatureValidation (equation : Equation) :
    combinedStructuralLanguageDef.validateEquation equation =
      checkedSignature.validateEquation equation := rfl

private theorem sameRewriteSignatureValidation (rule : RewriteRule) :
    combinedStructuralLanguageDef.validateRewrite rule =
      checkedSignature.validateRewrite rule := rfl

private theorem checked_combineComm :
    combinedStructuralLanguageDef.validateEquation combineCommEquation = [] := by
  rw [sameEquationSignatureValidation]
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    checkedSignature_typeNames, checkedSignature_terms, combineCommEquation,
    LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_combineAssoc :
    combinedStructuralLanguageDef.validateEquation combineAssocEquation = [] := by
  rw [sameEquationSignatureValidation]
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    checkedSignature_typeNames, checkedSignature_terms, combineAssocEquation,
    LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_combineZero :
    combinedStructuralLanguageDef.validateEquation combineZeroEquation = [] := by
  rw [sameEquationSignatureValidation]
  simp only [LanguageDef.validateEquation, LanguageDef.validateRulePatterns,
    checkedSignature_typeNames, checkedSignature_terms, combineZeroEquation,
    LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private theorem checked_existingTerm (term : GrammarRule)
    (member : term ∈ combinedStructuralLanguageDef.terms) :
    combinedStructuralLanguageDef.validateTerm term = [] := by
  rw [sameTermValidation]
  exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _ combined_validation
    term (by
      change term ∈ [reviseDecl, extractDecl, combineDecl, evidenceZeroDecl,
        overlapMergeDecl, overlapFactorDecl, overlapCorrectDecl, forgetDecl] at member
      change term ∈ coreTerms ++ [overlapMergeDecl, overlapFactorDecl,
        overlapCorrectDecl] ++ [forgetDecl]
      exact member)

private theorem checked_existingRewrite (rule : RewriteRule)
    (member : rule ∈ (wmExtVertexLanguageDefGuarded combinedVertex).rewrites) :
    combinedStructuralLanguageDef.validateRewrite rule = [] := by
  rw [sameRewriteValidation]
  exact LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil _ combined_validation
    rule member

theorem combinedStructural_validation :
    combinedStructuralLanguageDef.validate = [] := by
  have termRows : combinedStructuralLanguageDef.terms.flatMap
      (LanguageDef.validateTerm combinedStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro term member
    exact checked_existingTerm term member
  have equationRows : combinedStructuralLanguageDef.equations.flatMap
      (LanguageDef.validateEquation combinedStructuralLanguageDef) = [] := by
    change [combineCommEquation, combineAssocEquation, combineZeroEquation].flatMap
      (LanguageDef.validateEquation combinedStructuralLanguageDef) = []
    simp only [List.flatMap_cons, List.flatMap_nil, checked_combineComm,
      checked_combineAssoc, checked_combineZero, List.nil_append]
  have computationalRows : computationalRules.flatMap
      (LanguageDef.validateRewrite combinedStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    apply checked_existingRewrite
    have memberCore : rule ∈ coreRules := by
      simp only [computationalRules, coreRules, List.mem_cons,
        List.not_mem_nil, or_false] at member ⊢
      tauto
    change rule ∈ coreRules ++ [ruleOverlapExtract] ++
      [ruleForgetOutsideGuarded, ruleForgetIdempotent]
    simp [memberCore]
  have extensionRows : extensionComputations.flatMap
      (LanguageDef.validateRewrite combinedStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    apply checked_existingRewrite
    change rule ∈ coreRules ++ [ruleOverlapExtract] ++
      [ruleForgetOutsideGuarded, ruleForgetIdempotent]
    simp only [extensionComputations, List.mem_cons,
      List.not_mem_nil, or_false] at member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false]
    tauto
  have coreCongruenceRows : coreCongruenceRules.flatMap
      (LanguageDef.validateRewrite combinedStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    rw [sameRewriteSignatureValidation]
    simp only [coreCongruenceRules, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [LanguageDef.validateRewrite,
        ruleReviseCongLeft, ruleReviseCongRight, ruleExtractCongLeft,
        ruleExtractCongRight, ruleCombineCongLeft, ruleCombineCongRight,
        congruencePatternChecks_eq] <;>
      decide +kernel
  have extensionCongruenceRows : combinedExtensionCongruenceRules.flatMap
      (LanguageDef.validateRewrite combinedStructuralLanguageDef) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    rw [sameRewriteSignatureValidation]
    simp only [combinedExtensionCongruenceRules, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [LanguageDef.validateRewrite,
        ruleOverlapMergeCongLeft, ruleOverlapMergeCongRight,
        ruleOverlapFactorCongFirst, ruleOverlapFactorCongSecond,
        ruleOverlapFactorCongQuery, ruleOverlapCorrectCongFirst,
        ruleOverlapCorrectCongSecond, ruleOverlapCorrectCongFactor,
        ruleForgetCongLeft, ruleForgetCongRight,
        congruencePatternChecks_eq] <;>
      decide +kernel
  have rewriteRows : combinedStructuralLanguageDef.rewrites.flatMap
      (LanguageDef.validateRewrite combinedStructuralLanguageDef) = [] := by
    change (computationalRules ++ extensionComputations ++ coreCongruenceRules ++
      combinedExtensionCongruenceRules).flatMap
        (LanguageDef.validateRewrite combinedStructuralLanguageDef) = []
    simp only [List.flatMap_append, computationalRows, extensionRows,
      coreCongruenceRows, extensionCongruenceRows, List.nil_append]
  unfold LanguageDef.validate
  simp only [termRows, equationRows, rewriteRows, List.append_nil]
  decide +kernel

def combinedStructuralValidated : ValidatedLanguageDef :=
  ⟨combinedStructuralLanguageDef, combinedStructural_validation⟩

/-- The structural WM core, including its authored evidence equations and
computational extraction, embeds literally in the structural combined vertex. -/
def structuralCoreToCombined :
    StructuralMorphism WMCalculusCombinedIntrinsicTransport.structuralValidated
      combinedStructuralValidated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration member
    simp only [mapTypeDecl_id]
    change List.Mem declaration (["State", "Query", "BinaryEvidence"] : List TypeDecl)
      at member
    change List.Mem declaration (["State", "Query", "BinaryEvidence", "Overlap", "Scope"] :
      List TypeDecl)
    cases member with
    | head => exact List.Mem.head _
    | tail _ rest =>
        cases rest with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ rest =>
            cases rest with
            | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
            | tail _ impossible => cases impossible
  mapsTerms := by
    intro rule member
    simp only [mapGrammarRule_id]
    change rule ∈ coreTerms at member
    change rule ∈ coreTerms ++ [overlapMergeDecl, overlapFactorDecl,
      overlapCorrectDecl] ++ [forgetDecl]
    simp only [List.mem_append]
    exact Or.inl (Or.inl member)
  mapsEquations := by
    intro equation member
    simp only [mapEquation_id]
    change equation ∈ structuralEquations at member
    change equation ∈ structuralEquations
    exact member
  mapsRewrites := by
    intro rewrite member
    simp only [mapRewriteRule_id]
    change rewrite ∈ computationalRules ++ coreCongruenceRules at member
    change rewrite ∈ computationalRules ++ extensionComputations ++
      coreCongruenceRules ++ combinedExtensionCongruenceRules
    simp only [List.mem_append] at member ⊢
    tauto

/-- Directed reduction of a structural-core term remains available in the
guarded structural extension. This is only a forward simulation. -/
theorem structuralCoreStep_in_combined
    {first second : Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      wmStructuralLanguageDef first second) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      combinedStructuralLanguageDef first second := by
  have transported :=
    Mettapedia.GSLT.LanguageDef.StructuralSimulation.langReduces_map_of_structuralMorphism
      structuralCoreToCombined (by intro a b equality; exact equality) rfl step
  change Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
    combinedStructuralLanguageDef
    (mapPattern LanguageDefSymbolMap.id first)
    (mapPattern LanguageDefSymbolMap.id second) at transported
  simpa only [mapPattern_id] using transported

#print axioms combinedStructural_validation
#print axioms structuralCoreToCombined
#print axioms structuralCoreStep_in_combined

end Mettapedia.OSLF.Framework.WMCalculusCombinedStructuralPresentation
