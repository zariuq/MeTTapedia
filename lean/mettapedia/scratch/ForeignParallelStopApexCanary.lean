import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ParallelFrontier
open RhoCommonRestorationApex

example
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {color declarationColor : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (foreign : declarationColor ≠ color)
    (callbackAvailable callbackScope : Nat)
    {leftPayload rightPayload : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree rightPayload
      rightView.node.plan.abstractPattern)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
    (targetBoundEq : leftReached.targetBound = rightReached.targetBound)
    (thinningEq : HEq leftReached.thinning rightReached.thinning)
    (leftProcess : leftReached.sourceType = .base "Proc")
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPayload =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPayload)
    (close :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ {leftRaw leftEndpoint rightRaw rightEndpoint},
      (∃ leftAbstract,
        leftRaw ∈ parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPayload ∧
        LeafWitness leftReached.sourceBound leftReached.targetBound
          leftReached.thinning leftReached.sourceAvailable
          leftReached.plan.abstractPattern leftReached.plan.boundaryTable.entries
          leftRaw leftAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (leftView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (leftEnvironment.reify leftAbstract)))) = leftEndpoint) →
      (∃ rightAbstract,
        rightRaw ∈ parallelLeaves
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPayload ∧
        LeafWitness rightReached.sourceBound rightReached.targetBound
          rightReached.thinning rightReached.sourceAvailable
          rightReached.plan.abstractPattern rightReached.plan.boundaryTable.entries
          rightRaw rightAbstract ∧
        canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl)
          callbackAvailable
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (rightView.node.thinning.thickenAmbientBVars callbackScope
              (mapPattern (color.symbols rhoCIGSLT)
                (rightEnvironment.reify rightAbstract)))) = rightEndpoint) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) leftRaw =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl) rightRaw →
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        callbackAvailable leftEndpoint rightEndpoint) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackAvailable leftReached.plan.abstractPattern
        rightReached.plan.abstractPattern := by
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let targetDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have leftNaturality := reached_parentCanonicalFrame_commonReify leftView.node
    leftEnvironment cospan cospan.leftSlot cospan.leftCommutes leftReached
      callbackAvailable callbackScope
  have rightNaturality := reached_parentCanonicalFrame_commonReify rightView.node
    rightEnvironment cospan cospan.rightSlot cospan.rightCommutes rightReached
      callbackAvailable callbackScope
  obtain ⟨lsb, ltb, lth, lsa, lo, lst, lp, lsc, lae⟩ := leftReached
  obtain ⟨rsb, rtb, rth, rsa, ro, rst, rp, rsc, rae⟩ := rightReached
  cases sourceBoundEq
  cases targetBoundEq
  cases sourceAvailableEq
  cases thinningEq
  have rightProcess : rst = .base "Proc" := sourceTypeEq.symm.trans leftProcess
  subst leftProcess
  subst rightProcess
  have apex := processPlans_commonRestorationApex_of_foreignCanonical
    leftEnvironment rightEnvironment leftView.node.thinning
      rightView.node.thinning cospan cospan.leftSlot cospan.rightSlot lp rp
      leftAdmission rightAdmission foreign canonical targetDeclaration rfl
      callbackScope callbackAvailable (by
        intro leftRaw leftEndpoint rightRaw rightEndpoint leftWitness
          rightWitness rawCanonical
        simpa only [leftEnvironment, rightEnvironment, cospan,
          targetDeclaration, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using
            (close (leftRaw := leftRaw) (leftEndpoint := leftEndpoint)
              (rightRaw := rightRaw) (rightEndpoint := rightEndpoint)
              leftWitness rightWitness rawCanonical))
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftNaturality.symm rightNaturality.symm apex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
