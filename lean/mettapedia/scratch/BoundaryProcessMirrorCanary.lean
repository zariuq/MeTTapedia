import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

noncomputable def procEscapeBoundaryPlanStops_sourcePatternLeafAligned_canary
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      leftNode.finiteBoundaryTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      rightNode.finiteBoundaryTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftNode.boundaryTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightNode.boundaryTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightNode.plan.abstractPattern)
    (leftProcess : leftReached.sourceType = .base "Proc")
    (rightBoundary : rightReached.BoundaryView)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightNode.sourceSort.1)))
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (escape : RhoDescendEscape color
      (canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPayload))
    (targetNeUnit : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPayload ≠
      .apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).parallelUnitConstructor [])
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation) rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftNode.term.1 + sizeOf rightNode.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey rhoReflectivePresentation availableDepth
        scopeDepth
        (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let target := canonicalize declaration leftPayload
  let leftProcessPlan := castCostStaticRegionPlanSourceType leftProcess
    leftReached.plan
  obtain ⟨descent⟩ := rhoProc_applyBoundaryDescent
    (sizeOf leftPayload) leftProcessPlan target (by omega) rfl escape
      targetNeUnit
  have leftProcessAbstract : leftProcessPlan.abstractPattern =
      leftReached.plan.abstractPattern :=
    castCostStaticRegionPlanSourceType_abstractPattern leftProcess
      leftReached.plan
  let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
      rightPayload rightReached.plan.abstractPattern :=
    { rightBoundary.stopped with
      skeletonContext := .hole
      abstract_eq := by
        simpa [OneHoleContext.fill] using rightBoundary.abstract_eq }
  have leftInnerEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        leftReached.plan.boundaryTable.entries := by
    rw [← castCostStaticRegionPlanSourceType_boundaryTable_entries
      leftProcess leftReached.plan]
    exact descent.entryEmbedding
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [descent.state.certified.typed]
        leftNode.plan.boundaryTable.entries :=
    leftInnerEmbedding.comp leftEmbedding
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightStopped.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    have retained : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
        [rightBoundary.stopped.certified.typed]
          rightNode.plan.boundaryTable.entries := by
      simpa only [rightBoundary.entries_eq] using rightEmbedding
    simpa [rightStopped] using retained
  have supportEq : descent.state.certified.typed.boundary.targetSupport =
      rightStopped.certified.typed.boundary.targetSupport := by
    calc
      descent.state.certified.typed.boundary.targetSupport =
          leftReached.sourceAvailable := descent.boundarySupport
      _ = rightReached.sourceAvailable := sourceAvailableEq
      _ = rightStopped.certified.typed.boundary.targetSupport := by
        simpa [rightStopped] using rightBoundary.targetSupport_eq.symm
  have typeEq : descent.state.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType := by
    calc
      descent.state.certified.typed.boundary.targetType =
          mapTypeExpr (color.symbols rhoCIGSLT) (.base "Proc") :=
        descent.boundaryType
      _ = mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType :=
        congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) leftProcess.symm
      _ = mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType :=
        congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq
      _ = rightStopped.certified.typed.boundary.targetType := by
        simpa [rightStopped] using rightBoundary.targetType_eq.symm
  have canonical : canonicalize declaration
        descent.state.certified.typed.boundary.content =
      canonicalize declaration
        rightStopped.certified.typed.boundary.content := by
    calc
      canonicalize declaration descent.state.certified.typed.boundary.content =
          canonicalize declaration leftPayload := by
        simpa [target, declaration] using descent.boundaryCanonical
      _ = canonicalize declaration rightPayload :=
        rawAligned.canonicalize_eq declaration stopCanonical
      _ = canonicalize declaration
          rightStopped.certified.typed.boundary.content := by
        rw [show rightStopped.certified.typed.boundary.content = rightPayload by
          simpa [rightStopped] using rightBoundary.content_eq]
  have leftMember : descent.state.certified.typed ∈
      leftNode.plan.boundaryTable.entries := leftEmbedding'.subset (by simp)
  have rightMember : rightStopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries := rightEmbedding'.subset (by simp)
  have leftSmaller := leftNode.plan.boundary_content_size_lt_of_isStaticRoot
    leftNode.rootStatic descent.state.certified.typed leftMember
  have rightSmaller := rightNode.plan.boundary_content_size_lt_of_isStaticRoot
    rightNode.rootStatic rightStopped.certified.typed rightMember
  have smaller :
      sizeOf descent.state.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by omega
  obtain ⟨rightRoute'⟩ := rightRoute
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType := by
    rw [show rightStopped.certified.typed.boundary.targetType =
        mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType by
      simpa [rightStopped] using rightBoundary.targetType_eq]
    exact CostCanonicalTypeRoute.rho_admissible rightRoute'
      rightRootAdmissible
  have leftRootEq : leftNode.skeleton.1 =
      leftReached.skeletonContext.fill leftProcessPlan.abstractPattern := by
    exact leftNode.skeleton_pattern.trans
      (leftReached.abstract_eq.trans
        (congrArg leftReached.skeletonContext.fill
          leftProcessAbstract.symm))
  have aligned := stoppedPair_sourcePatternLeafAligned_of_closeSmaller
    leftNode rightNode leftTrees rightTrees leftEnvironment rightEnvironment
    descent.state rightStopped leftReached.skeletonContext
    rightReached.skeletonContext leftRootEq
    (rightNode.skeleton_pattern.trans rightReached.abstract_eq)
    leftEmbedding' rightEmbedding' descent.contextCollapse
    (by simp [rightStopped, canonicalize]) (Or.inl supportEq) typeEq
    declaration canonical _ smaller rightAdmissible closeSmaller leftKey
    rightKey availableDepth scopeDepth
  simpa only [leftProcessAbstract] using aligned

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
