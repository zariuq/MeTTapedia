import scratch.RhoNodeCommonAssignmentShape
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignResidualSpine

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace ParallelFrontier

noncomputable def foreignReachedPair_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftView.node.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightView.node.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤
      sizeOf rightView.node.term.1)
    (smaller : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1) :
    ∀ callbackAvailable callbackScope callbackRoot,
      RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
        callbackScope callbackRoot leftReached.plan.abstractPattern
          rightReached.plan.abstractPattern := by
  intro callbackAvailable callbackScope callbackRoot
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have rawAligned : CanonicalStopAligned rawDeclaration
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
      leftPayload rightPayload :=
    canonicalStopAligned_of_canonicalize_eq_below rawDeclaration canonical
      smaller
  have aligned := rhoReachedPlan_canonicalStopAligned_of_rawAligned
    leftReached rightReached leftAdmission rightAdmission sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      rhoReflectivePresentation.toReflectivePresentationDecl rawDeclaration
      rawAligned
  apply RhoReachedPlanPairCommonApex.ofProvenancedAlignedAbstracts leftView
    rightView callbackAvailable callbackScope callbackRoot leftReached
      rightReached aligned
  intro availableDepth scopeDepth rootDepth stopLeft stopRight stopped
  rcases stopped with ⟨leftStopPayload, rightStopPayload, evidence⟩
  rcases evidence with
    ⟨leftStopReached, rightStopReached, leftStopAdmission,
      rightStopAdmission, leftStopAbstractEq, rightStopAbstractEq,
      stopSourceTypeEq, stopSourceAvailableEq, stopSourceBoundEq,
      stopTargetBoundEq, stopThinningEq, leftStopEmbedding,
      rightStopEmbedding, leftStopRoute, rightStopRoute, stopReason,
      leftStopPayloadSizeLe, rightStopPayloadSizeLe, stopRawAligned⟩
  obtain ⟨leftEmbedding'⟩ := leftEmbedding
  obtain ⟨rightEmbedding'⟩ := rightEmbedding
  obtain ⟨leftRoute'⟩ := leftRoute
  obtain ⟨rightRoute'⟩ := rightRoute
  obtain ⟨leftStopEmbedding'⟩ := leftStopEmbedding
  obtain ⟨rightStopEmbedding'⟩ := rightStopEmbedding
  obtain ⟨leftStopRoute'⟩ := leftStopRoute
  obtain ⟨rightStopRoute'⟩ := rightStopRoute
  have stopSmaller : sizeOf leftStopPayload + sizeOf rightStopPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 := by
    exact lt_of_le_of_lt
      (Nat.add_le_add leftStopPayloadSizeLe rightStopPayloadSizeLe) smaller
  by_cases bothBoundary :
      leftStopReached.plan.rootClass.IsCertifiedBoundary ∧
        rightStopReached.plan.rootClass.IsCertifiedBoundary
  · exact nestedBoundaryPairPlanStops_commonRestorationApex_of_closeSmaller
      leftView rightView declarationColor rightRootAdmissible closeSmaller
      leftReached rightReached leftEmbedding' rightEmbedding' rightRoute'
      availableDepth scopeDepth rootDepth leftStopReached rightStopReached
      leftStopAdmission rightStopAdmission leftStopAbstractEq
      rightStopAbstractEq stopSourceTypeEq stopSourceAvailableEq
      leftStopEmbedding' rightStopEmbedding' rightStopRoute' stopRawAligned
      bothBoundary.1 bothBoundary.2
  · have parallelCase :
        (leftStopReached.plan.rootClass =
            .collection rhoReflectivePresentation.parallelCollection ∨
          rightStopReached.plan.rootClass =
            .collection rhoReflectivePresentation.parallelCollection) →
        RhoReachedPlanPairCommonApex leftView rightView availableDepth
          scopeDepth rootDepth stopLeft stopRight := by
      intro parallel
      let leftStopAtRoot := leftStopReached.rebaseAbstractRoot
        leftReached.skeletonContext leftReached.abstract_eq
      let rightStopAtRoot := rightStopReached.rebaseAbstractRoot
        rightReached.skeletonContext rightReached.abstract_eq
      have rightStopAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT)
            rightStopReached.sourceType) :=
        CostCanonicalTypeRoute.rho_admissible
          (rightRoute'.prepend rightStopRoute') rightRootAdmissible
      have leftStopAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          (mapTypeExpr (color.symbols rhoCIGSLT)
            leftStopReached.sourceType) := by
        rw [stopSourceTypeEq]
        exact rightStopAdmissible
      have leftProcess : leftStopReached.sourceType = .base "Proc" := by
        rcases parallel with leftParallel | rightParallel
        · exact rho_collectionPlan_sourceType_eq_proc leftStopReached.plan
            ⟨rhoReflectivePresentation.parallelCollection, leftParallel⟩
            leftStopAdmissible
        · have rightProcess := rho_collectionPlan_sourceType_eq_proc
            rightStopReached.plan
            ⟨rhoReflectivePresentation.parallelCollection, rightParallel⟩
            rightStopAdmissible
          exact stopSourceTypeEq.trans rightProcess
      have stopCanonical := stopRawAligned.canonicalize_eq rawDeclaration
        (fun given => given.1.2)
      have parallelApex :=
        rho_reachedPlanPairCommonApex_of_foreignCanonical leftView rightView
          foreign availableDepth scopeDepth rootDepth leftStopAtRoot
          rightStopAtRoot leftStopAdmission rightStopAdmission
          stopSourceTypeEq stopSourceAvailableEq stopSourceBoundEq
          stopTargetBoundEq stopThinningEq
          ⟨leftStopEmbedding'.comp leftEmbedding'⟩
          ⟨rightStopEmbedding'.comp rightEmbedding'⟩ leftProcess
          stopCanonical (close := by
            dsimp only
            intro leftRaw leftEndpoint rightRaw rightEndpoint leftLeaf
              rightLeaf leafCanonical depth
            rcases leftLeaf with
              ⟨leftLeafAbstract, leftLeafMembership, leftLeafWitness,
                leftEndpointEq⟩
            rcases rightLeaf with
              ⟨rightLeafAbstract, rightLeafMembership, rightLeafWitness,
                rightEndpointEq⟩
            obtain ⟨leftLeafReached, leftLeafSourceBound,
                leftLeafTargetBound, leftLeafThinning, leftLeafAvailable,
                leftLeafProcess, leftLeafAbstractEq, leftLeafAdmission,
                ⟨leftLeafEmbedding⟩⟩ := leftLeafWitness.exists_reached
            obtain ⟨rightLeafReached, rightLeafSourceBound,
                rightLeafTargetBound, rightLeafThinning, rightLeafAvailable,
                rightLeafProcess, rightLeafAbstractEq, rightLeafAdmission,
                ⟨rightLeafEmbedding⟩⟩ := rightLeafWitness.exists_reached
            let leftLeafAtRoot := leftLeafReached.rebaseAbstractRoot
              leftStopAtRoot.skeletonContext leftStopAtRoot.abstract_eq
            let rightLeafAtRoot := rightLeafReached.rebaseAbstractRoot
              rightStopAtRoot.skeletonContext rightStopAtRoot.abstract_eq
            have leafSourceTypeEq : leftLeafReached.sourceType =
                rightLeafReached.sourceType :=
              leftLeafProcess.trans rightLeafProcess.symm
            have leafSourceAvailableEq : leftLeafReached.sourceAvailable =
                rightLeafReached.sourceAvailable :=
              leftLeafAvailable.trans
                (stopSourceAvailableEq.trans rightLeafAvailable.symm)
            have leafSourceBoundEq : leftLeafReached.sourceBound =
                rightLeafReached.sourceBound :=
              leftLeafSourceBound.trans
                (stopSourceBoundEq.trans rightLeafSourceBound.symm)
            have leafTargetBoundEq : leftLeafReached.targetBound =
                rightLeafReached.targetBound :=
              leftLeafTargetBound.trans
                (stopTargetBoundEq.trans rightLeafTargetBound.symm)
            have leafThinningEq : HEq leftLeafReached.thinning
                rightLeafReached.thinning :=
              leftLeafThinning.trans
                (stopThinningEq.trans rightLeafThinning.symm)
            have leftLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
                color
                (mapTypeExpr (color.symbols rhoCIGSLT)
                  (.base leftView.node.sourceSort.1))
                (mapTypeExpr (color.symbols rhoCIGSLT)
                  leftLeafReached.sourceType)) := ⟨
              CostCanonicalTypeRoute.castEndpoint
                (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
                  (leftProcess.trans leftLeafProcess.symm))
                (leftRoute'.prepend leftStopRoute')⟩
            have rightProcess : rightStopReached.sourceType = .base "Proc" :=
              stopSourceTypeEq.symm.trans leftProcess
            have rightLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
                color
                (mapTypeExpr (color.symbols rhoCIGSLT)
                  (.base rightView.node.sourceSort.1))
                (mapTypeExpr (color.symbols rhoCIGSLT)
                  rightLeafReached.sourceType)) := ⟨
              CostCanonicalTypeRoute.castEndpoint
                (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
                  (rightProcess.trans rightLeafProcess.symm))
                (rightRoute'.prepend rightStopRoute')⟩
            have bareParallel :
                (∃ elements, leftStopPayload = .collection
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation).parallelCollection elements
                    none) ∨
                ∃ elements, rightStopPayload = .collection
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation).parallelCollection elements
                    none := by
              rcases parallel with leftParallel | rightParallel
              · apply Or.inl
                apply _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
                  leftStopReached leftStopAdmission
                simpa only [costStaticReflectivePresentationDecl_parallelCollection]
                  using leftParallel
              · apply Or.inr
                apply _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
                  rightStopReached rightStopAdmission
                simpa only [costStaticReflectivePresentationDecl_parallelCollection]
                  using rightParallel
            have leafSmallerStop :=
              pair_sizeOf_lt_of_mem_parallelLeaves_of_bareParallel
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation)
                leftLeafMembership rightLeafMembership bareParallel
            have leafSmallerRoot : sizeOf leftRaw + sizeOf rightRaw <
                sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 :=
              lt_trans leafSmallerStop stopSmaller
            have leftLeafSizeLeRoot : sizeOf leftRaw ≤
                sizeOf leftView.node.term.1 :=
              le_trans
                (sizeOf_le_of_mem_parallelLeaves
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation)
                  leftStopPayload leftRaw leftLeafMembership)
                (le_trans leftStopPayloadSizeLe leftPayloadSizeLe)
            have rightLeafSizeLeRoot : sizeOf rightRaw ≤
                sizeOf rightView.node.term.1 :=
              le_trans
                (sizeOf_le_of_mem_parallelLeaves
                  (costStaticReflectivePresentationDecl rhoCIGSLT color
                    rhoReflectivePresentation)
                  rightStopPayload rightRaw rightLeafMembership)
                (le_trans rightStopPayloadSizeLe rightPayloadSizeLe)
            have leafApex := foreignReachedPair_commonRestorationApex
              leftView rightView declarationColor foreign rightRootAdmissible
              closeSmaller leftLeafAtRoot rightLeafAtRoot leftLeafAdmission
              rightLeafAdmission leafSourceTypeEq leafSourceAvailableEq
              leafSourceBoundEq leafTargetBoundEq leafThinningEq
              ⟨(leftLeafEmbedding.comp leftStopEmbedding').comp
                leftEmbedding'⟩
              ⟨(rightLeafEmbedding.comp rightStopEmbedding').comp
                rightEmbedding'⟩
              leftLeafRoute rightLeafRoute leafCanonical leftLeafSizeLeRoot
              rightLeafSizeLeRoot leafSmallerRoot availableDepth scopeDepth
              depth
            subst leftLeafAbstractEq
            subst rightLeafAbstractEq
            let leftEnvironment := CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            let rightEnvironment := CostStaticAtomEnvironment.ofInventory
              (rightView.node.semanticAtomEnvironment
                (rightView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
            let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
            have leftNaturality :=
              reached_parentCanonicalFrame_commonReify leftView.node
                leftEnvironment cospan cospan.leftSlot cospan.leftCommutes
                leftLeafAtRoot availableDepth scopeDepth
            have rightNaturality :=
              reached_parentCanonicalFrame_commonReify rightView.node
                rightEnvironment cospan cospan.rightSlot cospan.rightCommutes
                rightLeafAtRoot availableDepth scopeDepth
            have targetApex :=
              CostStaticAtomKeyCospan.CommonRestorationApex.reindex
                leftNaturality rightNaturality leafApex
            apply CostStaticAtomKeyCospan.CommonRestorationApex.reindex
              leftEndpointEq rightEndpointEq
            simpa only [leftEnvironment, rightEnvironment, cospan,
              leftLeafAtRoot, rightLeafAtRoot,
              CostStaticPlanReached.rebaseAbstractRoot,
              CostStaticAtomKeyCospan.reifyLeft,
              CostStaticAtomKeyCospan.reifyRight] using targetApex)
      simpa only [leftStopAtRoot, rightStopAtRoot,
        CostStaticPlanReached.rebaseAbstractRoot,
        RhoReachedPlanPairCommonApex, leftStopAbstractEq,
        rightStopAbstractEq] using parallelApex
    rcases RhoCanonicalRawStop.foreign_reached_stop_cases leftStopReached
        rightStopReached foreign stopReason bothBoundary with quote |
          leftBoundary | rightBoundary | leftParallel | rightParallel
    · let leftStopAtRoot := leftStopReached.rebaseAbstractRoot
        leftReached.skeletonContext leftReached.abstract_eq
      let rightStopAtRoot := rightStopReached.rebaseAbstractRoot
        rightReached.skeletonContext rightReached.abstract_eq
      have quoteApex := rho_quotePlanStops_commonRestorationApex_of_below leftView
        rightView foreign availableDepth scopeDepth rootDepth leftStopAtRoot
        rightStopAtRoot leftStopAdmission rightStopAdmission stopSourceTypeEq
        stopSourceAvailableEq stopSourceBoundEq stopTargetBoundEq
        stopThinningEq quote.1 quote.2 stopRawAligned (mapBelow := by
          dsimp only
          intro childAvailableDepth childScopeDepth childRootDepth
            leftArgument rightArgument stoppedBelow
          rcases stoppedBelow with
            ⟨leftArgumentPayload, rightArgumentPayload, argumentEvidence,
              argumentSmaller⟩
          rcases argumentEvidence with
            ⟨leftArgumentReached, rightArgumentReached,
              leftArgumentAdmission, rightArgumentAdmission,
              leftArgumentAbstractEq, rightArgumentAbstractEq,
              argumentSourceTypeEq, argumentSourceAvailableEq,
              argumentSourceBoundEq, argumentTargetBoundEq,
              argumentThinningEq, ⟨leftArgumentEmbedding'⟩,
              ⟨rightArgumentEmbedding'⟩, ⟨leftArgumentRoute'⟩,
              ⟨rightArgumentRoute'⟩, _argumentReason,
              leftArgumentSizeLe, rightArgumentSizeLe, argumentRawAligned⟩
          let leftArgumentAtRoot := leftArgumentReached.rebaseAbstractRoot
            leftStopAtRoot.skeletonContext leftStopAtRoot.abstract_eq
          let rightArgumentAtRoot := rightArgumentReached.rebaseAbstractRoot
            rightStopAtRoot.skeletonContext rightStopAtRoot.abstract_eq
          have argumentCanonical := argumentRawAligned.canonicalize_eq
            rawDeclaration (fun given => given.1.2)
          have argumentSmallerRoot :
              sizeOf leftArgumentPayload + sizeOf rightArgumentPayload <
                sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 :=
            lt_trans argumentSmaller stopSmaller
          have leftArgumentSizeLeRoot :
              sizeOf leftArgumentPayload ≤ sizeOf leftView.node.term.1 :=
            le_trans leftArgumentSizeLe
              (le_trans leftStopPayloadSizeLe leftPayloadSizeLe)
          have rightArgumentSizeLeRoot :
              sizeOf rightArgumentPayload ≤ sizeOf rightView.node.term.1 :=
            le_trans rightArgumentSizeLe
              (le_trans rightStopPayloadSizeLe rightPayloadSizeLe)
          have argumentApex := foreignReachedPair_commonRestorationApex
            leftView rightView declarationColor foreign rightRootAdmissible
            closeSmaller leftArgumentAtRoot rightArgumentAtRoot
            leftArgumentAdmission rightArgumentAdmission argumentSourceTypeEq
            argumentSourceAvailableEq argumentSourceBoundEq
            argumentTargetBoundEq argumentThinningEq
            ⟨(leftArgumentEmbedding'.comp leftStopEmbedding').comp
              leftEmbedding'⟩
            ⟨(rightArgumentEmbedding'.comp rightStopEmbedding').comp
              rightEmbedding'⟩
            ⟨leftRoute'.prepend
              (leftStopRoute'.prepend leftArgumentRoute')⟩
            ⟨rightRoute'.prepend
              (rightStopRoute'.prepend rightArgumentRoute')⟩
            argumentCanonical leftArgumentSizeLeRoot rightArgumentSizeLeRoot
            argumentSmallerRoot childAvailableDepth childScopeDepth
            childRootDepth
          subst leftArgumentAbstractEq
          subst rightArgumentAbstractEq
          exact argumentApex)
      simpa only [leftStopAtRoot, rightStopAtRoot,
        CostStaticPlanReached.rebaseAbstractRoot,
        RhoReachedPlanPairCommonApex, leftStopAbstractEq,
        rightStopAbstractEq] using quoteApex
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
        rightRootAdmissible closeSmaller leftReached rightReached
        leftEmbedding' rightEmbedding' leftRoute' rightRoute'
        leftPayloadSizeLe rightPayloadSizeLe availableDepth
        scopeDepth rootDepth leftStopReached rightStopReached
        leftStopAdmission rightStopAdmission leftStopAbstractEq
        rightStopAbstractEq stopSourceTypeEq stopSourceAvailableEq
        stopSourceBoundEq stopTargetBoundEq stopThinningEq leftStopEmbedding'
        rightStopEmbedding' leftStopRoute' rightStopRoute' stopReason
        leftStopPayloadSizeLe rightStopPayloadSizeLe stopRawAligned
        bothBoundary (Or.inl leftBoundary)
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor
        (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
        rightRootAdmissible closeSmaller leftReached rightReached
        leftEmbedding' rightEmbedding' leftRoute' rightRoute'
        leftPayloadSizeLe rightPayloadSizeLe availableDepth
        scopeDepth rootDepth leftStopReached rightStopReached
        leftStopAdmission rightStopAdmission leftStopAbstractEq
        rightStopAbstractEq stopSourceTypeEq stopSourceAvailableEq
        stopSourceBoundEq stopTargetBoundEq stopThinningEq leftStopEmbedding'
        rightStopEmbedding' leftStopRoute' rightStopRoute' stopReason
        leftStopPayloadSizeLe rightStopPayloadSizeLe stopRawAligned
        bothBoundary (Or.inr rightBoundary)
    · exact parallelCase (Or.inl leftParallel)
    · exact parallelCase (Or.inr rightParallel)

termination_by sizeOf leftPayload + sizeOf rightPayload

end ParallelFrontier
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
