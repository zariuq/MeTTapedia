import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryQuoteParallelCells

/-!
Recorded kernel goal for `RhoPlanStopDelegatedSourceLeaf`, taken from the
elaborator after

  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary delegated
  subst leftAbstractEq; subst rightAbstractEq
  apply PatternLeafAligned.leaf
  intro sourceDepth

Abbreviations used below (all `let`-bound inside the definition):

  Lenv   := CostStaticAtomEnvironment.ofInventory
              (leftView.node.semanticAtomEnvironment
                (leftView.children.normalizeValues
                  (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  Renv   := the same with `rightView`
  cospan := Lenv.semanticKeyCospan Renv
  Lkey   := CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node Lenv
  Rkey   := CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node Renv

Goal:

  ReflectiveContextSupport.RestoresTogether rhoCIGSLT.costWholeReflectionProfile
    cospan.commonSupport cospan.commonAssignment
    (cospan.reifyWith Lenv.lookupAtom? cospan.leftSlot
      (leftView.node.thinning.thickenAmbientBVars sourceDepth
        (mapPattern (CostStaticColor.symbols rhoCIGSLT color)
          (canonicalizeByDepths Lkey
            rhoReflectivePresentation.toReflectivePresentationDecl
            callbackAvailable callbackScope
            (Lenv.reify leftReached.plan.abstractPattern)))))
    (cospan.reifyWith Renv.lookupAtom? cospan.rightSlot
      (rightView.node.thinning.thickenAmbientBVars sourceDepth
        (mapPattern (CostStaticColor.symbols rhoCIGSLT color)
          (canonicalizeByDepths Rkey
            rhoReflectivePresentation.toReflectivePresentationDecl
            callbackAvailable callbackScope
            (Renv.reify rightReached.plan.abstractPattern)))))

`callbackAvailable`, `callbackScope` and `sourceDepth` are three mutually
independent universally quantified naturals.  `PatternLeafAligned.leaf` is
forced whenever the two reached root shapes differ, which the cell permits.
-/
