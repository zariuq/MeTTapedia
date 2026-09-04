import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteBoundaryAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A reached authored Quote, interpreted in the enclosing static
environment, restores to the hereditary normal form of its payload tree. -/
noncomputable def CostStaticPlanReached.parentQuoteFrame_restoresToPayloadNormal
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    (parentTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      parentNode.finiteBoundaryTable)
    {parentInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable
      (parentTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      parentNode.skeleton.1}
    (parentEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      parentInventory)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (quoteRoot : reached.plan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries
      parentNode.plan.boundaryTable.entries)
    (tree : CostRegionTree rhoCIGSLT targetFree reached.sourceAvailable []
      payload (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType))
    (availableDepth scopeDepth restorationDepth : Nat) :
    parentEnvironment.restoreAt restorationDepth
        (parentNode.thinning.thickenAmbientBVars scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (canonicalizeByDepths
              (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
                parentEnvironment)
              rhoReflectivePresentation availableDepth scopeDepth
              (parentEnvironment.reify reached.plan.abstractPattern)))) =
      (tree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  obtain ⟨view⟩ :=
    CostStaticPlanReached.nonempty_staticRootView_of_quoteRoot reached
      quoteRoot tree
  let largePlan := CostStaticRegionPlan.reindexPatternSourceType
    view.patternEq.symm
      (CostRegionTree.StaticRootView.sourceType_eq view).symm
      (reached.plan.recontextualize .hole)
  have largeEntriesEq : largePlan.boundaryTable.entries =
      reached.plan.boundaryTable.entries := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_boundaryTable_entries]
    exact reached.plan.recontextualizeEntriesEq .hole
  let largeEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      largePlan.boundaryTable.entries parentNode.plan.boundaryTable.entries :=
    CostStaticPlanEntryEmbedding.castSource largeEntriesEq.symm embedding
  let largeTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      largePlan.boundaryTable :=
    CostRegionBoundaryTrees.restrictAlongEntryEmbedding largePlan.boundaryTable
      parentNode.boundaryTable largeEmbedding parentTrees
  obtain ⟨_sealed, planAligned, _entriesEq, _abstractEq⟩ :=
    CostStaticPlanReached.staticRootView_boundaryFibersAvailabilitySuffix
      reached admission tree view
  have smallQuote :=
    CostStaticPlanReached.staticRootView_rootClass_eq_quoteRoot reached
      quoteRoot tree view
  have largeQuote : largePlan.rootClass = .application
      rhoReflectivePresentation.quoteConstructor := by
    simp [largePlan, quoteRoot]
  have forestsAligned :=
    CostRegionBoundaryTrees.normalizedAvailabilitySuffixAcross_of_quoteRoots
      view.node.plan largePlan planAligned smallQuote largeQuote view.children
        largeTrees
  let reconstructedNode := CostStaticRegionNode.ofPlan
    view.node.term view.node.plan view.node.rootStatic
  let smallValues := view.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let smallPacked := reconstructedNode.semanticAtomEnvironment smallValues
  let smallInventory := smallPacked.1
  let smallEnvironment := CostStaticAtomEnvironment.ofInventory smallInventory
  let largePacked := CostStaticRegionPlan.semanticAtomEnvironmentOfTrees
    largePlan view.node.term.2.2.2.1 largeTrees
      rhoHereditaryNormalizationKernel
  let largeInventory := largePacked.1
  let largeEnvironment := CostStaticAtomEnvironment.ofInventory largeInventory
  have viewToRestricted :=
    CostStaticRegionPlan.quoteCanonicalRestoresTogether_of_normalizedSuffix
      view.node.plan largePlan view.node.term.2.2.2.1 planAligned smallQuote
        view.children largeTrees smallEnvironment largeEnvironment
          forestsAligned
  have largeAbstractEq : largePlan.abstractPattern =
      reached.plan.abstractPattern := by
    simp only [largePlan,
      CostStaticRegionPlan.reindexPatternSourceType_abstractPattern]
    exact reached.plan.recontextualizeAbstractEq .hole
  have parentRootEq : parentNode.skeleton.1 =
      reached.skeletonContext.fill reached.plan.abstractPattern :=
    parentNode.skeleton_pattern.trans reached.abstract_eq
  let liftLargeOccurrence : CostStaticFVarOccurrence
      largePlan.abstractPattern → CostStaticFVarOccurrence
        parentNode.skeleton.1 := fun occurrence =>
    CostStaticFVarOccurrence.castRoot parentRootEq.symm
      ((CostStaticFVarOccurrence.castRoot largeAbstractEq occurrence).inContext
        reached.skeletonContext)
  have liftLargeName : ∀ occurrence,
      (liftLargeOccurrence occurrence).name = occurrence.name := by
    intro occurrence
    simp [liftLargeOccurrence]
  have largeToParent :=
    CostStaticRegionPlan.restrictedQuoteCanonicalRestoresTogether
      largePlan view.node.term.2.2.2.1 largeQuote parentNode.boundaryTable
        largeEmbedding parentTrees parentEnvironment liftLargeOccurrence
          liftLargeName
  let sourceCanonical := canonicalizeByDepths
    (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
      parentEnvironment)
    rhoReflectivePresentation availableDepth scopeDepth
    (parentEnvironment.reify reached.plan.abstractPattern)
  have sourceAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (parentEnvironment.reify reached.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      reached.plan quoteRoot
  have sourceCanonicalSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0 sourceCanonical = true := by
    exact canonicalizeByDepths_binderSafeAt
      (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
        parentEnvironment)
      rhoReflectivePresentation rhoReflectivePresentation.quoteConstructor
      availableDepth scopeDepth 0
      (parentEnvironment.reify reached.plan.abstractPattern)
      sourceAbstractSafe
  have mappedSourceCanonicalSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT) sourceCanonical) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      sourceCanonicalSafe
  let frame := parentNode.thinning.thickenAmbientBVars scopeDepth
    (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
  have frameEq : frame =
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical := by
    exact parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      scopeDepth (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
      mappedSourceCanonicalSafe
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    color rhoReflectivePresentation
  let targetKey : Nat → Nat → Pattern → Nat :=
    fun current _ candidate =>
      CostStaticRegionNode.semanticPatternKeyAt parentEnvironment current
        candidate
  have mappedAbstractSafe : binderSafeAt
      ((color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor)
      0 (mapPattern (color.symbols rhoCIGSLT)
        (parentEnvironment.reify reached.plan.abstractPattern)) = true := by
    simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
      sourceAbstractSafe
  have sourceCanonicalEqExplicit : sourceCanonical =
      canonicalizeByDepths
        (fun current structural candidate =>
          CostStaticRegionNode.semanticPatternKeyAt parentEnvironment current
            (parentNode.thinning.thickenAmbientBVars structural
              (mapPattern (color.symbols rhoCIGSLT) candidate)))
        rhoReflectivePresentation availableDepth scopeDepth
        (parentEnvironment.reify reached.plan.abstractPattern) := by
    rfl
  have targetNaturality :
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
        canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    have naturality :=
      Mettapedia.GSLT.LanguageDef.CostHereditaryCanonical.mapThicken_canonicalizeByDepths
        parentNode.thinning targetKey rhoReflectivePresentation
          availableDepth scopeDepth
          (parentEnvironment.reify reached.plan.abstractPattern)
    have inputThin :=
      parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern))
        mappedAbstractSafe
    have outputThin :=
      parentNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor)
        scopeDepth (mapPattern (color.symbols rhoCIGSLT) sourceCanonical)
        mappedSourceCanonicalSafe
    calc
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
          parentNode.thinning.thickenAmbientBVars scopeDepth
            (mapPattern (color.symbols rhoCIGSLT) sourceCanonical) :=
        outputThin.symm
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (parentNode.thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols rhoCIGSLT)
                (parentEnvironment.reify
                  reached.plan.abstractPattern))) := by
        rw [sourceCanonicalEqExplicit]
        simpa [targetKey, targetDeclaration] using naturality
      _ = canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth
            (mapPattern (color.symbols rhoCIGSLT)
              (parentEnvironment.reify reached.plan.abstractPattern)) := by
        exact congrArg
          (canonicalizeByDepths targetKey targetDeclaration availableDepth
            scopeDepth) inputThin
  have targetIgnoreScope :
      canonicalizeByDepths targetKey targetDeclaration availableDepth
          scopeDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    simpa [targetKey] using
      canonicalizeByDepths_ignoreScope
        (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
        targetDeclaration availableDepth scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern))
  obtain ⟨quoteArguments, abstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot reached.plan
      quoteRoot
  have mappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (parentEnvironment.reify reached.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (quoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (parentEnvironment.reify argument)) := by
    rw [abstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have targetQuoteDepthIndependent :
      canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration availableDepth
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify reached.plan.abstractPattern)) := by
    rw [mappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have targetCanonicalEq :
      mapPattern (color.symbols rhoCIGSLT) sourceCanonical =
        canonicalizeByAt
          (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
          targetDeclaration 0
          (mapPattern (color.symbols rhoCIGSLT)
            (parentEnvironment.reify largePlan.abstractPattern)) := by
    rw [largeAbstractEq]
    exact targetNaturality.trans
      (targetIgnoreScope.trans targetQuoteDepthIndependent)
  let smallCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt smallEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (smallEnvironment.reify view.node.plan.abstractPattern))
  have smallSupportNil : ∀ slot,
      (smallEnvironment.atomValue slot).key.targetSupport = [] := by
    intro slot
    exact
      CostStaticRegionPlan.ofInventory_atomValue_targetSupport_eq_nil_of_quoteRoot
        view.node.plan
        (CostStaticRegionNode.CostStaticRegionPlan.rhoAbstractPattern_binderFree_of_base
          view.node.plan
          ⟨"Name", rho_applicationPlan_sourceType_eq_name_of_quoteRoot
            view.node.plan smallQuote⟩)
        smallQuote smallInventory slot
  have smallAbstractSafe : binderSafeAt
      rhoReflectivePresentation.quoteConstructor 0
      (smallEnvironment.reify view.node.plan.abstractPattern) = true := by
    rw [CostStaticAtomEnvironment.binderSafeAt_reify]
    exact CostStaticRegionPlan.abstractPattern_binderSafeAt_zero_of_quoteRoot
      view.node.plan smallQuote
  have smallMappedAbstractSafe : binderSafeAt targetDeclaration.quoteConstructor
      0 (mapPattern (color.symbols rhoCIGSLT)
        (smallEnvironment.reify view.node.plan.abstractPattern)) = true := by
    have mapped : binderSafeAt
        ((color.symbols rhoCIGSLT).constructor
          rhoReflectivePresentation.quoteConstructor) 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern)) = true := by
      simpa only [CostStaticColor.binderSafeAt_mapPattern_symbols] using
        smallAbstractSafe
    simpa [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation] using mapped
  have reconstructedTargetFrame :
      reconstructedNode.reifyTargetFrame smallEnvironment =
        mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern) := by
    rw [reconstructedNode.reifyTargetFrame_eq_map_reifiedSourceFrame
      smallEnvironment]
    exact
      reconstructedNode.thinning.thickenAmbientBVars_eq_self_of_binderSafeAt_zero
        targetDeclaration.quoteConstructor 0
        (mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern))
        smallMappedAbstractSafe
  obtain ⟨smallQuoteArguments, smallAbstractQuote⟩ :=
    CostStaticRegionPlan.abstractPattern_eq_quote_of_quoteRoot view.node.plan
      smallQuote
  have smallMappedQuote :
      mapPattern (color.symbols rhoCIGSLT)
          (smallEnvironment.reify view.node.plan.abstractPattern) =
        .apply targetDeclaration.quoteConstructor
          (smallQuoteArguments.map fun argument =>
            mapPattern (color.symbols rhoCIGSLT)
              (smallEnvironment.reify argument)) := by
    rw [smallAbstractQuote]
    simp [targetDeclaration, costStaticReflectivePresentationDecl_eq_map,
      mapReflectivePresentation, Pattern.renameFVars, mapPattern,
      mapPatternList_eq_map]
  have smallCanonicalEqReconstructed : smallCanonical =
      reconstructedNode.canonicalizeReifiedTargetFrame smallEnvironment
        targetDeclaration := by
    unfold smallCanonical
    unfold CostStaticRegionNode.canonicalizeReifiedTargetFrame
    rw [reconstructedTargetFrame, smallMappedQuote]
    simp only [canonicalizeByAt, beq_self_eq_true, if_true]
  have smallRestoreDepth :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        smallEnvironment.restoreAt reconstructedNode.targetBound.length
          smallCanonical := by
    exact smallEnvironment.restoreAt_eq_of_atomTargetSupport_eq_nil
      smallSupportNil smallCanonical restorationDepth
        reconstructedNode.targetBound.length
  have smallRestoreEqNormalize :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (CostStaticRegionNode.normalizeHereditary reconstructedNode
          smallValues).1 := by
    rw [smallRestoreDepth, smallCanonicalEqReconstructed]
    rfl
  have reconstructedNormalizeEqTree :
      (CostStaticRegionNode.normalizeHereditary reconstructedNode
        smallValues).1 =
        (tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    let reconstructedTree : CostRegionTree rhoCIGSLT targetFree
        reached.sourceAvailable [] payload
        (mapTypeExpr (color.symbols rhoCIGSLT) reached.sourceType) :=
      (((CostRegionTree.static (outer := []) reconstructedNode
          view.children).reindexPattern view.patternEq).reindexAvailable
            view.availableEq).reindexType view.typeEq
    let reconstructedView : reconstructedTree.StaticRootView color :=
      { node := reconstructedNode
        children := view.children
        patternEq := view.patternEq
        availableEq := view.availableEq
        typeEq := view.typeEq
        treeEq := rfl }
    have exposedNormal :=
      (reconstructedView.normalize_pattern rhoHereditaryStaticNormalizer).symm
    have treeNormal := CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel reconstructedTree tree admission.object
    exact exposedNormal.trans treeNormal
  have smallRestoreEqTree :
      smallEnvironment.restoreAt restorationDepth smallCanonical =
        (tree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    smallRestoreEqNormalize.trans reconstructedNormalizeEqTree
  let largeCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt largeEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (largeEnvironment.reify largePlan.abstractPattern))
  let parentCanonical := canonicalizeByAt
    (CostStaticRegionNode.semanticPatternKeyAt parentEnvironment)
    targetDeclaration 0
    (mapPattern (color.symbols rhoCIGSLT)
      (parentEnvironment.reify largePlan.abstractPattern))
  have smallToParentRaw :=
    (viewToRestricted restorationDepth).trans
      (largeToParent restorationDepth)
  have parentCanonicalEqFrame : parentCanonical = frame := by
    exact targetCanonicalEq.symm.trans frameEq.symm
  change parentEnvironment.restoreAt restorationDepth frame = _
  rw [← parentCanonicalEqFrame]
  exact smallToParentRaw.symm.trans smallRestoreEqTree

/-- Every atom name in a reached source frame remains covered after source
canonicalization, colour mapping, and ambient-binder reinsertion. -/
theorem CostStaticPlanReached.parentCanonicalFrame_atomCovered
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (parentNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      parentNode.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      parentNode.boundaryTable values parentNode.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      parentNode.plan.abstractPattern)
    (availableDepth scopeDepth : Nat) :
    environment.Covers
      (parentNode.thinning.thickenAmbientBVars scopeDepth
        (mapPattern (color.symbols rhoCIGSLT)
          (canonicalizeByDepths
            (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
              environment)
            rhoReflectivePresentation availableDepth scopeDepth
            (environment.reify reached.plan.abstractPattern)))) := by
  intro name membership
  have canonicalMembership : name ∈
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode
          environment)
        rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify reached.plan.abstractPattern)).freeFvarNames := by
    simpa [CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
      StructuralMorphism.mapPattern_freeFvarNames] using membership
  have reachedMembership : name ∈
      (environment.reify reached.plan.abstractPattern).freeFvarNames :=
    (CostStaticAtomKeyCospan.mem_freeFvarNames_canonicalizeByDepths_iff
      (CostStaticRegionNode.sourceSemanticPatternKeyAt parentNode environment)
      rhoReflectivePresentation name availableDepth scopeDepth
      (environment.reify reached.plan.abstractPattern)).mp
        canonicalMembership
  let reify : Pattern → Pattern := fun pattern => environment.reify pattern
  have filledMembership : name ∈
      (reify (reached.skeletonContext.fill
        reached.plan.abstractPattern)).freeFvarNames := by
    change name ∈
      (environment.reify (reached.skeletonContext.fill
        reached.plan.abstractPattern)).freeFvarNames
    rw [← environment.reifyContext_fill]
    exact Mettapedia.GSLT.LanguageDef.OneHoleContext.mem_freeFvarNames_fill
      (environment.reifyContext reached.skeletonContext) reachedMembership
  have rootEq : parentNode.skeleton.1 =
      reached.skeletonContext.fill reached.plan.abstractPattern :=
    parentNode.skeleton_pattern.trans reached.abstract_eq
  have reifiedRootEq : reify parentNode.skeleton.1 =
      reify (reached.skeletonContext.fill reached.plan.abstractPattern) :=
    congrArg reify rootEq
  have rootMembership : name ∈
      (reify parentNode.skeleton.1).freeFvarNames := by
    rw [reifiedRootEq]
    exact filledMembership
  have targetMembership : name ∈
      (parentNode.reifyTargetFrame environment).freeFvarNames := by
    rw [parentNode.reifyTargetFrame_eq_map_reifiedSourceFrame]
    simpa [reify, CostStaticRegionNode.reifiedSourceFrame,
      CostStaticBinderThinning.freeFvarNames_thickenAmbientBVars,
      StructuralMorphism.mapPattern_freeFvarNames] using rootMembership
  exact parentNode.reifyTargetFrame_atomCovered environment name
    targetMembership

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
