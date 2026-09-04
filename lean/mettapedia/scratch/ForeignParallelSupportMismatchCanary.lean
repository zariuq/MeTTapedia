import ForeignSupportMismatchOrderCanary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

/-!
# Foreign bare-parallel support-mismatch canary

Two base-colour process cells have the same wrapped-colour canonical image.
One exposes a wrapped shell as a boundary at the current availability, while
the other retains the corresponding base Quote structurally.  Putting the
cells in opposite orders under a base parallel supplies an exact foreign raw
stop at an admitted pair of same-colour static roots.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignParallelSupportMismatchCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.OSLF.Framework.ConstructorCategory
open CostCanonicalLaws
open ForeignSupportMismatchOrderCanary

def selectedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

@[simp] theorem selectedDeclaration_parallelCollection :
    selectedDeclaration.parallelCollection =
      rhoReflectivePresentation.parallelCollection := rfl

def leftParallel : Pattern :=
  .collection selectedDeclaration.parallelCollection
    [leftPattern, rightPattern] none

def rightParallel : Pattern :=
  .collection selectedDeclaration.parallelCollection
    [rightPattern, leftPattern] none

private theorem baseParallelRule_mem : rhoCalc.terms[3] ∈ rhoCalc.terms :=
  List.getElem_mem _

private theorem leftTyped :
    HasType rhoCIGSLT.costWholeLanguage
      CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
      available leftParallel processType := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps") (elementType := processType)
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ baseParallelRule_mem
  · exact rho_costBaseParallelConstructor_params
  · exact .cons ForeignSupportMismatchOrderCanary.leftWellSorted.1.1
      (.cons ForeignSupportMismatchOrderCanary.rightWellSorted.1.1
        (.nil available processType))

private theorem rightTyped :
    HasType rhoCIGSLT.costWholeLanguage
      CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
      available rightParallel processType := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps") (elementType := processType)
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ baseParallelRule_mem
  · exact rho_costBaseParallelConstructor_params
  · exact .cons ForeignSupportMismatchOrderCanary.rightWellSorted.1.1
      (.cons ForeignSupportMismatchOrderCanary.leftWellSorted.1.1
        (.nil available processType))

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
      available processType leftParallel := by
  refine ⟨⟨leftTyped, rfl, rfl, leftTyped.isWellScopedAt⟩, ?_⟩
  intro reflected _membership
  simp [leftParallel, selectedDeclaration, leftPattern, rightPattern,
    selectedShell, foreignQuote,
    CostTypedMixedColorApexCounterexample.typedApexForeignQuote,
    CostTypedMixedColorApexCounterexample.typedApexRaw,
    CostTypedMixedColorApexCounterexample.typedApexFirstAtom,
    CostTypedMixedColorApexCounterexample.typedApexSecondAtom,
    binderSafeAt, binderSafeListAt]

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
      available processType rightParallel := by
  refine ⟨⟨rightTyped, rfl, rfl, rightTyped.isWellScopedAt⟩, ?_⟩
  intro reflected _membership
  simp [rightParallel, selectedDeclaration, leftPattern, rightPattern,
    selectedShell, foreignQuote,
    CostTypedMixedColorApexCounterexample.typedApexForeignQuote,
    CostTypedMixedColorApexCounterexample.typedApexRaw,
    CostTypedMixedColorApexCounterexample.typedApexFirstAtom,
    CostTypedMixedColorApexCounterexample.typedApexSecondAtom,
    binderSafeAt, binderSafeListAt]

theorem foreignCanonicalEq :
    canonicalize declaration leftParallel =
      canonicalize declaration rightParallel := by
  change canonicalize declaration
      (.collection declaration.parallelCollection
        [leftPattern, rightPattern] none) =
    canonicalize declaration
      (.collection declaration.parallelCollection
        [rightPattern, leftPattern] none)
  exact canonicalize_parallel_permutation declaration
    (List.Perm.swap leftPattern rightPattern []).symm

noncomputable def leftTree : CostRegionTree rhoCIGSLT
    CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
    available [] leftParallel processType :=
  (CostRegionTree.build? available [] leftParallel processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree : CostRegionTree rhoCIGSLT
    CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
    available [] rightParallel processType :=
  (CostRegionTree.build? available [] rightParallel processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

theorem leftRootStatic : leftTree.rootIsStatic = true :=
  CostStaticRootShape.baseCollection.rootIsStatic leftTree

theorem rightRootStatic : rightTree.rootIsStatic = true :=
  CostStaticRootShape.baseCollection.rootIsStatic rightTree

noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftRootStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightRootStatic

theorem leftColor : leftViewPair.1 = .base := by
  apply CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting rhoCIGSLT
      leftViewPair.1 .base leftViewPair.2.node.sourceSort rhoProc
  · apply rho_collection_node_sourceSort_interacting leftViewPair.2.node
    simpa [leftParallel] using leftViewPair.2.patternEq
  · rfl
  · apply Subtype.ext
    exact TypeExpr.base.inj leftViewPair.2.typeEq

theorem rightColor : rightViewPair.1 = .base := by
  apply CostStaticColor.color_eq_of_mapLangSort_eq_of_interacting rhoCIGSLT
      rightViewPair.1 .base rightViewPair.2.node.sourceSort rhoProc
  · apply rho_collection_node_sourceSort_interacting rightViewPair.2.node
    simpa [rightParallel] using rightViewPair.2.patternEq
  · rfl
  · apply Subtype.ext
    exact TypeExpr.base.inj rightViewPair.2.typeEq

noncomputable def leftView : leftTree.StaticRootView .base :=
  leftColor ▸ leftViewPair.2

noncomputable def rightView : rightTree.StaticRootView .base :=
  rightColor ▸ rightViewPair.2

private theorem rootClass_collection_of_isStaticRoot
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning rhoCIGSLT color sourceBound
      targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan rhoCIGSLT color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (rootStatic : plan.isStaticRoot = true)
    (shape : pattern = .collection collectionType elements rest) :
    plan.rootClass = .collection collectionType := by
  cases plan with
  | collection =>
      exact congrArg CostStaticPlanRootClass.collection
        (Pattern.collection.inj shape).1
  | boundaryCollection =>
      simp [CostStaticRegionPlan.isStaticRoot] at rootStatic
  | application => cases shape
  | lambda => cases shape
  | multiLambda => cases shape
  | bvar => cases shape
  | fvar => cases shape
  | boundaryApplication => cases shape

theorem leftRootClass : leftView.node.plan.rootClass =
    .collection rhoReflectivePresentation.parallelCollection := by
  apply rootClass_collection_of_isStaticRoot leftView.node.plan
    (elements := [leftPattern, rightPattern]) (rest := none)
  · exact leftView.node.rootStatic
  · rw [leftView.patternEq]
    simp [leftParallel]

theorem rightRootClass : rightView.node.plan.rootClass =
    .collection rhoReflectivePresentation.parallelCollection := by
  apply rootClass_collection_of_isStaticRoot rightView.node.plan
    (elements := [rightPattern, leftPattern]) (rest := none)
  · exact rightView.node.rootStatic
  · rw [rightView.patternEq]
    simp [rightParallel]

private theorem thinning_heq_of_bounds_eq
    {leftSourceBound rightSourceBound leftTargetBound rightTargetBound :
      List TypeExpr}
    (sourceBoundEq : leftSourceBound = rightSourceBound)
    (targetBoundEq : leftTargetBound = rightTargetBound)
    (leftThinning : CostStaticBinderThinning rhoCIGSLT .base
      leftSourceBound leftTargetBound)
    (rightThinning : CostStaticBinderThinning rhoCIGSLT .base
      rightSourceBound rightTargetBound) :
    HEq leftThinning rightThinning := by
  subst rightSourceBound
  subst rightTargetBound
  exact heq_of_eq (Subsingleton.elim _ _)

noncomputable def stopMeasure : Nat :=
  sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 + 1

theorem rootRawStop :
    RhoCanonicalRawStop .wrapped stopMeasure leftView.node.term.1
      rightView.node.term.1 := by
  refine ⟨⟨Or.inl ?_, ?_⟩, ?_⟩
  · exact Or.inr ⟨[leftPattern, rightPattern], by
      rw [leftView.patternEq]
      rfl⟩
  · rw [leftView.patternEq, rightView.patternEq]
    exact foreignCanonicalEq
  · simp [stopMeasure]

noncomputable def leftRootReached : CostStaticPlanReached rhoCIGSLT .base
    CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
    leftView.node.term.1 leftView.node.plan.abstractPattern where
  sourceBound := leftView.node.sourceBound
  targetBound := leftView.node.targetBound
  thinning := leftView.node.thinning
  sourceAvailable := leftView.node.targetBound
  outer := .hole
  sourceType := .base leftView.node.sourceSort.1
  plan := leftView.node.plan
  skeletonContext := .hole
  abstract_eq := rfl

noncomputable def rightRootReached : CostStaticPlanReached rhoCIGSLT .base
    CostTypedMixedColorApexCounterexample.typedApexCospan.commonTargetFreeContext
    rightView.node.term.1 rightView.node.plan.abstractPattern where
  sourceBound := rightView.node.sourceBound
  targetBound := rightView.node.targetBound
  thinning := rightView.node.thinning
  sourceAvailable := rightView.node.targetBound
  outer := .hole
  sourceType := .base rightView.node.sourceSort.1
  plan := rightView.node.plan
  skeletonContext := .hole
  abstract_eq := rfl

theorem rootStopAtPayload :
    CostStaticPlanCanonicalStopAtPayload leftView.node.plan
      rightView.node.plan rhoReflectivePresentation declaration
      (RhoCanonicalRawStop .wrapped stopMeasure)
      leftView.node.term.1 rightView.node.term.1
      leftView.node.plan.abstractPattern rightView.node.plan.abstractPattern := by
  have sameBound := leftView.targetBound_eq_targetBound rightView
  have sameSort := leftView.sourceSort_eq_sourceSort rightView
  have sameSourceBound : leftRootReached.sourceBound =
      rightRootReached.sourceBound :=
    congrArg
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base)
      sameBound
  refine ⟨leftRootReached, rightRootReached,
    leftView.node.planRawAdmission, rightView.node.planRawAdmission,
    rfl, rfl, ?_, ?_, ?_, sameBound, ?_, ?_, ?_, ?_, ?_, Or.inl rootRawStop,
    le_rfl, le_rfl, .leaf rootRawStop⟩
  · exact congrArg (fun sort => (.base sort.1 : TypeExpr)) sameSort
  · exact sameBound
  · exact sameSourceBound
  · exact thinning_heq_of_bounds_eq sameSourceBound sameBound _ _
  · exact ⟨CostStaticPlanEntryEmbedding.refl _⟩
  · exact ⟨CostStaticPlanEntryEmbedding.refl _⟩
  · exact ⟨.refl⟩
  · exact ⟨.refl⟩

theorem rootPlanStop :
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
      rhoReflectivePresentation declaration
      (RhoCanonicalRawStop .wrapped stopMeasure)
      leftView.node.plan.abstractPattern rightView.node.plan.abstractPattern :=
  ⟨leftView.node.term.1, rightView.node.term.1, rootStopAtPayload⟩

end ForeignParallelSupportMismatchCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
