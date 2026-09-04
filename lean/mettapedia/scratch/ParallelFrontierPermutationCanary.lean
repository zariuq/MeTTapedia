import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ParallelFrontier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoCommonRestorationApex

example :
    sizeOf (.bvar 0 : Pattern) + sizeOf (.fvar "x" : Pattern) <
      sizeOf (.collection
        rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [.bvar 0, .apply
          rhoReflectivePresentation.toReflectivePresentationDecl.parallelUnitConstructor
          []] none : Pattern) + sizeOf (.fvar "x" : Pattern) := by
  apply pair_sizeOf_lt_of_mem_parallelLeaves_of_bareParallel
    rhoReflectivePresentation.toReflectivePresentationDecl
  · simp [parallelLeaves, parallelLeavesList]
  · simp [parallelLeaves]
  · exact Or.inl ⟨_, rfl⟩

/-- Without a bare-parallel wrapper the corresponding strict bound is false. -/
example : ¬ (sizeOf (.bvar 0 : Pattern) + sizeOf (.fvar "x" : Pattern) <
    sizeOf (.bvar 0 : Pattern) + sizeOf (.fvar "x" : Pattern)) := by omega

noncomputable def parallelLeaves_abstractPattern_permutation_of_foreign_canonical_eq_canary
    {color declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {leftOuter rightOuter : OneHoleContext}
    {leftPayload rightPayload : Pattern}
    (leftPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable leftOuter leftPayload (.base "Proc"))
    (rightPlan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable rightOuter rightPayload (.base "Proc"))
    (leftAdmission : leftPlan.RawAdmission)
    (rightAdmission : rightPlan.RawAdmission)
    (different : declarationColor ≠ color)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (targetDeclaration : ReflectivePresentationDecl) (depth : Nat)
    (leftFrame rightFrame : Pattern → Pattern)
    (close : ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
          LeafWitness sourceBound targetBound thinning sourceAvailable
            leftPlan.abstractPattern leftPlan.boundaryTable.entries leftRaw
              leftAbstract ∧
          leftFrame leftAbstract = leftEndpoint) →
      (∃ rightAbstract,
          LeafWitness sourceBound targetBound thinning sourceAvailable
            rightPlan.abstractPattern rightPlan.boundaryTable.entries rightRaw
              rightAbstract ∧
          rightFrame rightAbstract = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        targetDeclaration depth leftEndpoint rightEndpoint) :
    CostStaticAtomKeyCospan.CommonRestorationApex.Permutation
      (source := rhoCIGSLT) cospan
      targetDeclaration depth
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        leftPlan.abstractPattern).map leftFrame)
      ((parallelLeaves rhoReflectivePresentation.toReflectivePresentationDecl
        rightPlan.abstractPattern).map rightFrame) := by
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have leftTraversal := parallelLeaves_map_abstractPattern_forall2 leftPlan
    leftAdmission leftFrame
  have rightTraversal := parallelLeaves_map_abstractPattern_forall2 rightPlan
    rightAdmission rightFrame
  have leftTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable leftPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact leftAdmission.wellSorted.1.1
  have rightTyped : HasType rhoCIGSLT.costWholeLanguage targetFree
      sourceAvailable rightPayload
      (.base (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl).processSort) := by
    cases color <;> exact rightAdmission.wellSorted.1.1
  have permutation :=
    rhoProc_parallelLeaves_map_perm_of_foreign_canonical_eq
      (fun _ pattern => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode pattern)
      color declarationColor different leftTyped rightTyped canonical depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.Permutation.of_related_map_perm
    cospan targetDeclaration depth (canonicalize rawDeclaration)
      (canonicalize rawDeclaration) leftTraversal rightTraversal permutation
      close

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
