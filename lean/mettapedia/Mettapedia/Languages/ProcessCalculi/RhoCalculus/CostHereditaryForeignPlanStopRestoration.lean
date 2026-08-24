import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignReachedPairApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open RhoStaticNonBoundaryPlanStopCommonApex

/-- A provenance-carrying stop strictly below a reached process pair restores
in the fixed semantic cospan of the enclosing static roots. -/
noncomputable def rho_strictPlanStop_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType)))
    (rightParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    {parentMeasure : Nat}
    (availableDepth scopeDepth rootDepth : Nat)
    {leftAbstract rightAbstract : Pattern}
    (stopped : CostStaticPlanCanonicalStopBelow leftParentReached.plan
      rightParentReached.plan rhoReflectivePresentation
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      (sizeOf leftParentPayload + sizeOf rightParentPayload)
      leftAbstract rightAbstract) :
    RhoReachedPlanPairCommonApex leftView rightView availableDepth scopeDepth
      rootDepth leftAbstract rightAbstract := by
  rcases stopped with
    ⟨leftPayload, rightPayload, evidence, smallerParent⟩
  rcases evidence with
    ⟨leftReached, rightReached, leftAdmission, rightAdmission,
      leftAbstractEq, rightAbstractEq, sourceTypeEq, sourceAvailableEq,
      sourceBoundEq, targetBoundEq, thinningEq, ⟨leftEmbedding⟩,
      ⟨rightEmbedding⟩, ⟨leftRoute⟩, ⟨rightRoute⟩,
      _stopReason, leftPayloadSizeLe, rightPayloadSizeLe, rawAligned⟩
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨leftParentRoute⟩ := leftParentRoute
  obtain ⟨rightParentRoute⟩ := rightParentRoute
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  have canonical := rawAligned.canonicalize_eq rawDeclaration
    (fun given => given.1.2)
  have smallerRoot : sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 :=
    lt_of_lt_of_le smallerParent
      (Nat.add_le_add leftParentSizeLe rightParentSizeLe)
  have leftSizeLeRoot : sizeOf leftPayload ≤ sizeOf leftView.node.term.1 :=
    le_trans leftPayloadSizeLe leftParentSizeLe
  have rightSizeLeRoot : sizeOf rightPayload ≤ sizeOf rightView.node.term.1 :=
    le_trans rightPayloadSizeLe rightParentSizeLe
  let leftAtRoot := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightAtRoot := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  have apex :=
    ParallelFrontier.foreignReachedPair_commonRestorationApex leftView
      rightView declarationColor foreign rightRootAdmissible closeSmaller
      leftAtRoot rightAtRoot leftAdmission rightAdmission sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      ⟨leftEmbedding.comp leftParentEmbedding⟩
      ⟨rightEmbedding.comp rightParentEmbedding⟩
      ⟨leftParentRoute.prepend leftRoute⟩
      ⟨rightParentRoute.prepend rightRoute⟩ canonical leftSizeLeRoot
      rightSizeLeRoot smallerRoot availableDepth scopeDepth rootDepth
  simpa only [leftAtRoot, rightAtRoot,
    CostStaticPlanReached.rebaseAbstractRoot,
    RhoReachedPlanPairCommonApex, leftAbstractEq, rightAbstractEq] using apex

/-- A paired authored quotation restores in the enclosing semantic cospan by
recursing only at strictly smaller argument stops. -/
noncomputable def rho_quoteReachedPair_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType)))
    (rightParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    (availableDepth scopeDepth rootDepth : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftParentReached.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightParentReached.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
        leftParentReached.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
        rightParentReached.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) leftParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) rightParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftParentPayload)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightParentPayload)
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload rightPayload)
    (leftQuote : leftReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor)
    (rightQuote : rightReached.plan.rootClass =
      .application rhoReflectivePresentation.quoteConstructor) :
    RhoReachedPlanPairCommonApex leftView rightView availableDepth scopeDepth
      rootDepth leftAbstract rightAbstract := by
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨leftParentRoute⟩ := leftParentRoute
  obtain ⟨rightParentRoute⟩ := rightParentRoute
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  obtain ⟨leftRoute⟩ := leftRoute
  obtain ⟨rightRoute⟩ := rightRoute
  let leftAtRoot := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightAtRoot := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  have leftSizeLeRoot : sizeOf leftPayload ≤ sizeOf leftView.node.term.1 :=
    le_trans leftPayloadSizeLe leftParentSizeLe
  have rightSizeLeRoot : sizeOf rightPayload ≤ sizeOf rightView.node.term.1 :=
    le_trans rightPayloadSizeLe rightParentSizeLe
  have apex := rho_quotePlanStops_commonRestorationApex_of_below leftView
    rightView foreign availableDepth scopeDepth rootDepth leftAtRoot
    rightAtRoot leftAdmission rightAdmission sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftQuote rightQuote rawAligned
    (mapBelow := by
      dsimp only
      intro childAvailableDepth childScopeDepth childRootDepth
        leftArgument rightArgument stoppedBelow
      exact rho_strictPlanStop_commonRestorationApex leftView rightView
        foreign rightRootAdmissible closeSmaller leftAtRoot rightAtRoot
        ⟨leftEmbedding.comp leftParentEmbedding⟩
        ⟨rightEmbedding.comp rightParentEmbedding⟩
        ⟨leftParentRoute.prepend leftRoute⟩
        ⟨rightParentRoute.prepend rightRoute⟩ leftSizeLeRoot
        rightSizeLeRoot childAvailableDepth childScopeDepth childRootDepth
        stoppedBelow)
  simpa only [leftAtRoot, rightAtRoot,
    CostStaticPlanReached.rebaseAbstractRoot,
    RhoReachedPlanPairCommonApex, leftAbstractEq, rightAbstractEq] using apex

/-- A reached pair with a bare-parallel side restores by flattening both
frontiers and recursively restoring only their strictly smaller leaves. -/
noncomputable def rho_parallelReachedPair_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType)))
    (rightParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    (availableDepth scopeDepth rootDepth : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftPayload leftParentReached.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightParentReached.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
    (rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
        leftParentReached.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
        rightParentReached.plan.boundaryTable.entries))
    (leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) leftParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
    (rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT) rightParentReached.sourceType)
      (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftParentPayload)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightParentPayload)
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload rightPayload)
    (parallel : leftReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection ∨
      rightReached.plan.rootClass =
        .collection rhoReflectivePresentation.parallelCollection) :
    RhoReachedPlanPairCommonApex leftView rightView availableDepth scopeDepth
      rootDepth leftAbstract rightAbstract := by
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨leftParentRoute⟩ := leftParentRoute
  obtain ⟨rightParentRoute⟩ := rightParentRoute
  obtain ⟨leftEmbedding⟩ := leftEmbedding
  obtain ⟨rightEmbedding⟩ := rightEmbedding
  obtain ⟨leftRoute⟩ := leftRoute
  obtain ⟨rightRoute⟩ := rightRoute
  let leftAtRoot := leftReached.rebaseAbstractRoot
    leftParentReached.skeletonContext leftParentReached.abstract_eq
  let rightAtRoot := rightReached.rebaseAbstractRoot
    rightParentReached.skeletonContext rightParentReached.abstract_eq
  have leftSizeLeRoot : sizeOf leftPayload ≤ sizeOf leftView.node.term.1 :=
    le_trans leftPayloadSizeLe leftParentSizeLe
  have rightSizeLeRoot : sizeOf rightPayload ≤ sizeOf rightView.node.term.1 :=
    le_trans rightPayloadSizeLe rightParentSizeLe
  have rightEndpointAdmissible :
      rhoCanonicalRecursiveTypeDomain.Admissible
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType) :=
    CostCanonicalTypeRoute.rho_admissible
      (rightParentRoute.prepend rightRoute) rightRootAdmissible
  have leftEndpointAdmissible :
      rhoCanonicalRecursiveTypeDomain.Admissible
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType) := by
    rw [sourceTypeEq]
    exact rightEndpointAdmissible
  have leftProcess : leftReached.sourceType = .base "Proc" := by
    rcases parallel with leftParallel | rightParallel
    · exact rho_collectionPlan_sourceType_eq_proc leftReached.plan
        ⟨rhoReflectivePresentation.parallelCollection, leftParallel⟩
        leftEndpointAdmissible
    · have rightProcess := rho_collectionPlan_sourceType_eq_proc
        rightReached.plan
        ⟨rhoReflectivePresentation.parallelCollection, rightParallel⟩
        rightEndpointAdmissible
      exact sourceTypeEq.trans rightProcess
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  have canonical := rawAligned.canonicalize_eq rawDeclaration
    (fun given => given.1.2)
  have apex := rho_reachedPlanPairCommonApex_of_foreignCanonical leftView
    rightView foreign availableDepth scopeDepth rootDepth leftAtRoot
    rightAtRoot leftAdmission rightAdmission sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq
    ⟨leftEmbedding.comp leftParentEmbedding⟩
    ⟨rightEmbedding.comp rightParentEmbedding⟩ leftProcess canonical
    (close := by
      dsimp only
      intro leftRaw leftEndpoint rightRaw rightEndpoint leftLeaf rightLeaf
        leafCanonical depth
      rcases leftLeaf with
        ⟨leftLeafAbstract, leftLeafMembership, leftLeafWitness,
          leftEndpointEq⟩
      rcases rightLeaf with
        ⟨rightLeafAbstract, rightLeafMembership, rightLeafWitness,
          rightEndpointEq⟩
      obtain ⟨leftLeafReached, leftLeafSourceBound, leftLeafTargetBound,
          leftLeafThinning, leftLeafAvailable, leftLeafProcess,
          leftLeafAbstractEq, leftLeafAdmission, ⟨leftLeafEmbedding⟩⟩ :=
        leftLeafWitness.exists_reached
      obtain ⟨rightLeafReached, rightLeafSourceBound, rightLeafTargetBound,
          rightLeafThinning, rightLeafAvailable, rightLeafProcess,
          rightLeafAbstractEq, rightLeafAdmission,
          ⟨rightLeafEmbedding⟩⟩ := rightLeafWitness.exists_reached
      let leftLeafAtRoot := leftLeafReached.rebaseAbstractRoot
        leftAtRoot.skeletonContext leftAtRoot.abstract_eq
      let rightLeafAtRoot := rightLeafReached.rebaseAbstractRoot
        rightAtRoot.skeletonContext rightAtRoot.abstract_eq
      have leafSourceTypeEq : leftLeafReached.sourceType =
          rightLeafReached.sourceType :=
        leftLeafProcess.trans rightLeafProcess.symm
      have leafSourceAvailableEq : leftLeafReached.sourceAvailable =
          rightLeafReached.sourceAvailable :=
        leftLeafAvailable.trans
          (sourceAvailableEq.trans rightLeafAvailable.symm)
      have leafSourceBoundEq : leftLeafReached.sourceBound =
          rightLeafReached.sourceBound :=
        leftLeafSourceBound.trans
          (sourceBoundEq.trans rightLeafSourceBound.symm)
      have leafTargetBoundEq : leftLeafReached.targetBound =
          rightLeafReached.targetBound :=
        leftLeafTargetBound.trans
          (targetBoundEq.trans rightLeafTargetBound.symm)
      have leafThinningEq : HEq leftLeafReached.thinning
          rightLeafReached.thinning :=
        leftLeafThinning.trans (thinningEq.trans rightLeafThinning.symm)
      have leftLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
          (mapTypeExpr (color.symbols rhoCIGSLT)
            (.base leftView.node.sourceSort.1))
          (mapTypeExpr (color.symbols rhoCIGSLT)
            leftLeafReached.sourceType)) := ⟨
        CostCanonicalTypeRoute.castEndpoint
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
            (leftProcess.trans leftLeafProcess.symm))
          (leftParentRoute.prepend leftRoute)⟩
      have rightProcess : rightReached.sourceType = .base "Proc" :=
        sourceTypeEq.symm.trans leftProcess
      have rightLeafRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
          (mapTypeExpr (color.symbols rhoCIGSLT)
            (.base rightView.node.sourceSort.1))
          (mapTypeExpr (color.symbols rhoCIGSLT)
            rightLeafReached.sourceType)) := ⟨
        CostCanonicalTypeRoute.castEndpoint
          (congrArg (mapTypeExpr (color.symbols rhoCIGSLT))
            (rightProcess.trans rightLeafProcess.symm))
          (rightParentRoute.prepend rightRoute)⟩
      have bareParallel :
          (∃ elements, leftPayload = .collection
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).parallelCollection elements none) ∨
          ∃ elements, rightPayload = .collection
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation).parallelCollection elements none := by
        rcases parallel with leftParallel | rightParallel
        · apply Or.inl
          apply _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
            leftReached leftAdmission
          simpa only [costStaticReflectivePresentationDecl_parallelCollection]
            using leftParallel
        · apply Or.inr
          apply _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelFrontier.CostStaticPlanReached.exists_payload_eq_bareCollection_of_rootClass
            rightReached rightAdmission
          simpa only [costStaticReflectivePresentationDecl_parallelCollection]
            using rightParallel
      have leafSmaller :=
        ParallelFrontier.pair_sizeOf_lt_of_mem_parallelLeaves_of_bareParallel
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation)
          leftLeafMembership rightLeafMembership bareParallel
      have leafSmallerRoot : sizeOf leftRaw + sizeOf rightRaw <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 :=
        lt_of_lt_of_le leafSmaller
          (Nat.add_le_add leftSizeLeRoot rightSizeLeRoot)
      have leftLeafSizeLeRoot : sizeOf leftRaw ≤
          sizeOf leftView.node.term.1 :=
        le_trans
          (ParallelFrontier.sizeOf_le_of_mem_parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            leftPayload leftRaw leftLeafMembership)
          leftSizeLeRoot
      have rightLeafSizeLeRoot : sizeOf rightRaw ≤
          sizeOf rightView.node.term.1 :=
        le_trans
          (ParallelFrontier.sizeOf_le_of_mem_parallelLeaves
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation)
            rightPayload rightRaw rightLeafMembership)
          rightSizeLeRoot
      have leafApex :=
        ParallelFrontier.foreignReachedPair_commonRestorationApex leftView
          rightView declarationColor foreign rightRootAdmissible closeSmaller
          leftLeafAtRoot rightLeafAtRoot leftLeafAdmission rightLeafAdmission
          leafSourceTypeEq leafSourceAvailableEq leafSourceBoundEq
          leafTargetBoundEq leafThinningEq
          ⟨(leftLeafEmbedding.comp leftEmbedding).comp leftParentEmbedding⟩
          ⟨(rightLeafEmbedding.comp rightEmbedding).comp rightParentEmbedding⟩
          leftLeafRoute rightLeafRoute leafCanonical leftLeafSizeLeRoot
          rightLeafSizeLeRoot leafSmallerRoot availableDepth scopeDepth depth
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
        ParallelFrontier.reached_parentCanonicalFrame_commonReify
          leftView.node leftEnvironment cospan cospan.leftSlot
          cospan.leftCommutes leftLeafAtRoot availableDepth scopeDepth
      have rightNaturality :=
        ParallelFrontier.reached_parentCanonicalFrame_commonReify
          rightView.node rightEnvironment cospan cospan.rightSlot
          cospan.rightCommutes rightLeafAtRoot availableDepth scopeDepth
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
  simpa only [leftAtRoot, rightAtRoot,
    CostStaticPlanReached.rebaseAbstractRoot,
    RhoReachedPlanPairCommonApex, leftAbstractEq, rightAbstractEq] using apex

/-- Every genuine foreign-colour stop of two reached source plans restores in
the fixed parent semantic cospan. -/
noncomputable def rho_foreignPlanStop_commonRestorationApex
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {leftParentPayload rightParentPayload : Pattern}
    (leftParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftParentPayload leftView.node.plan.abstractPattern)
    (rightParentReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightParentPayload rightView.node.plan.abstractPattern)
    (leftParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree leftParentReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
    (rightParentEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
      color targetFree rightParentReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
    (leftParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base leftView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        leftParentReached.sourceType)))
    (rightParentRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1))
      (mapTypeExpr (color.symbols rhoCIGSLT)
        rightParentReached.sourceType)))
    (leftParentSizeLe : sizeOf leftParentPayload ≤
      sizeOf leftView.node.term.1)
    (rightParentSizeLe : sizeOf rightParentPayload ≤
      sizeOf rightView.node.term.1)
    {parentMeasure : Nat}
    (availableDepth scopeDepth rootDepth : Nat)
    {leftAbstract rightAbstract : Pattern}
    (stopped : CostStaticPlanCanonicalStop leftParentReached.plan
      rightParentReached.plan rhoReflectivePresentation
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftAbstract rightAbstract) :
    RhoReachedPlanPairCommonApex leftView rightView availableDepth scopeDepth
      rootDepth leftAbstract rightAbstract := by
  rcases stopped with ⟨leftPayload, rightPayload, evidence⟩
  rcases evidence with
    ⟨leftReached, rightReached, leftAdmission, rightAdmission,
      leftAbstractEq, rightAbstractEq, sourceTypeEq, sourceAvailableEq,
      sourceBoundEq, targetBoundEq, thinningEq, ⟨leftEmbedding⟩,
      ⟨rightEmbedding⟩, ⟨leftRoute⟩, ⟨rightRoute⟩,
      stopReason, leftPayloadSizeLe, rightPayloadSizeLe, rawAligned⟩
  obtain ⟨leftParentEmbedding⟩ := leftParentEmbedding
  obtain ⟨rightParentEmbedding⟩ := rightParentEmbedding
  obtain ⟨leftParentRoute⟩ := leftParentRoute
  obtain ⟨rightParentRoute⟩ := rightParentRoute
  by_cases bothBoundary : leftReached.plan.rootClass.IsCertifiedBoundary ∧
      rightReached.plan.rootClass.IsCertifiedBoundary
  · exact nestedBoundaryPairPlanStops_commonRestorationApex_of_closeSmaller
      leftView rightView declarationColor rightRootAdmissible closeSmaller
      leftParentReached rightParentReached leftParentEmbedding
      rightParentEmbedding rightParentRoute availableDepth scopeDepth
      rootDepth leftReached rightReached leftAdmission rightAdmission
      leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
      leftEmbedding rightEmbedding rightRoute rawAligned bothBoundary.1
      bothBoundary.2
  · rcases RhoCanonicalRawStop.foreign_reached_stop_cases leftReached
        rightReached foreign stopReason bothBoundary with quote | leftBoundary |
          rightBoundary | leftParallel | rightParallel
    · exact rho_quoteReachedPair_commonRestorationApex leftView rightView
        foreign rightRootAdmissible closeSmaller leftParentReached
        rightParentReached ⟨leftParentEmbedding⟩ ⟨rightParentEmbedding⟩
        ⟨leftParentRoute⟩ ⟨rightParentRoute⟩ leftParentSizeLe
        rightParentSizeLe availableDepth scopeDepth rootDepth leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq
        rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
        targetBoundEq thinningEq ⟨leftEmbedding⟩ ⟨rightEmbedding⟩
        ⟨leftRoute⟩ ⟨rightRoute⟩ leftPayloadSizeLe rightPayloadSizeLe
        rawAligned quote.1 quote.2
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor
        parentMeasure
        rightRootAdmissible closeSmaller leftParentReached rightParentReached
        leftParentEmbedding rightParentEmbedding leftParentRoute
        rightParentRoute leftParentSizeLe rightParentSizeLe availableDepth
        scopeDepth rootDepth leftReached rightReached leftAdmission
        rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
        sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
        rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
        rightPayloadSizeLe rawAligned bothBoundary (Or.inl leftBoundary)
    · exact nestedBoundaryPlanStops_commonRestorationApex_of_closeSmaller
        leftView rightView declarationColor
        parentMeasure
        rightRootAdmissible closeSmaller leftParentReached rightParentReached
        leftParentEmbedding rightParentEmbedding leftParentRoute
        rightParentRoute leftParentSizeLe rightParentSizeLe availableDepth
        scopeDepth rootDepth leftReached rightReached leftAdmission
        rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
        sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
        rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
        rightPayloadSizeLe rawAligned bothBoundary (Or.inr rightBoundary)
    · exact rho_parallelReachedPair_commonRestorationApex leftView rightView
        foreign rightRootAdmissible closeSmaller leftParentReached
        rightParentReached ⟨leftParentEmbedding⟩ ⟨rightParentEmbedding⟩
        ⟨leftParentRoute⟩ ⟨rightParentRoute⟩ leftParentSizeLe
        rightParentSizeLe availableDepth scopeDepth rootDepth leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq
        rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
        targetBoundEq thinningEq ⟨leftEmbedding⟩ ⟨rightEmbedding⟩
        ⟨leftRoute⟩ ⟨rightRoute⟩ leftPayloadSizeLe rightPayloadSizeLe
        rawAligned (Or.inl leftParallel)
    · exact rho_parallelReachedPair_commonRestorationApex leftView rightView
        foreign rightRootAdmissible closeSmaller leftParentReached
        rightParentReached ⟨leftParentEmbedding⟩ ⟨rightParentEmbedding⟩
        ⟨leftParentRoute⟩ ⟨rightParentRoute⟩ leftParentSizeLe
        rightParentSizeLe availableDepth scopeDepth rootDepth leftReached
        rightReached leftAdmission rightAdmission leftAbstractEq
        rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
        targetBoundEq thinningEq ⟨leftEmbedding⟩ ⟨rightEmbedding⟩
        ⟨leftRoute⟩ ⟨rightRoute⟩ leftPayloadSizeLe rightPayloadSizeLe
        rawAligned (Or.inr rightParallel)

/-- The foreign residual is closed by the exact provenance-carrying plan-stop
restoration theorem; rigid free variables remain on the routed member path. -/
theorem rho_afterSameColorBoundarySideForeign_of_planStops
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)) :
    AfterSameColorBoundarySideForeign leftView rightView declarationColor := by
  apply rho_afterSameColorBoundarySideForeign_of_provenancedStopCallback
    leftView rightView declarationColor
  intro leftPayload rightPayload leftReached rightReached leftEmbedding
    rightEmbedding leftRoute rightRoute leftPayloadSizeLe rightPayloadSizeLe
    availableDepth scopeDepth rootDepth leftAbstract rightAbstract stopped
  exact rho_foreignPlanStop_commonRestorationApex leftView rightView foreign
    rightRootAdmissible closeSmaller leftReached rightReached leftEmbedding
    rightEmbedding leftRoute rightRoute leftPayloadSizeLe rightPayloadSizeLe
    availableDepth scopeDepth rootDepth stopped

/-- At a declaration colour foreign to both static views, the root plans
provide the provenance required by the general plan-stop restoration theorem,
independently of the raw-stop budget selected by the caller. -/
noncomputable def rho_staticPlanStopCommonApex_of_foreign
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1))
    {parentMeasure : Nat} :
    @RhoStaticPlanStopCommonApex targetFree available outer leftPattern
      rightPattern type left right color leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure) := by
  let leftRootReached : CostStaticPlanReached rhoCIGSLT color targetFree
      leftView.node.term.1 leftView.node.plan.abstractPattern :=
    { sourceBound := leftView.node.sourceBound
      targetBound := leftView.node.targetBound
      thinning := leftView.node.thinning
      sourceAvailable := leftView.node.targetBound
      outer := .hole
      sourceType := .base leftView.node.sourceSort.1
      plan := leftView.node.plan
      skeletonContext := .hole
      abstract_eq := rfl }
  let rightRootReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightView.node.term.1 rightView.node.plan.abstractPattern :=
    { sourceBound := rightView.node.sourceBound
      targetBound := rightView.node.targetBound
      thinning := rightView.node.thinning
      sourceAvailable := rightView.node.targetBound
      outer := .hole
      sourceType := .base rightView.node.sourceSort.1
      plan := rightView.node.plan
      skeletonContext := .hole
      abstract_eq := rfl }
  intro availableDepth scopeDepth rootDepth leftAbstract rightAbstract stopped
  exact rho_foreignPlanStop_commonRestorationApex leftView rightView foreign
    rightRootAdmissible closeSmaller leftRootReached rightRootReached
    ⟨CostStaticPlanEntryEmbedding.refl _⟩
    ⟨CostStaticPlanEntryEmbedding.refl _⟩
    ⟨CostCanonicalTypeRoute.refl⟩ ⟨CostCanonicalTypeRoute.refl⟩
    (Nat.le_refl _) (Nat.le_refl _) availableDepth scopeDepth rootDepth stopped

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
