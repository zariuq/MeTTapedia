import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesLeafClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProvenancedFVarRestoration
import Mettapedia.GSLT.LanguageDef.CostStaticPlanFVarSelection
import Mettapedia.GSLT.LanguageDef.CostCertifiedBoundaryShape
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryView

/-!
# Provenanced construction of matched rho frame alignment

This module connects the generic plan-stop descent to the matched-frame
restoration interface.  Membership-certified free variables are discharged
by the common source-or-boundary theorem; the caller supplies only the
semantic interpretation of an exact reached-plan stop.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- The sole semantic callback left after generic plan descent and
membership-certified free-variable restoration. -/
def RhoStaticPlanStopRestoration
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ sourceDepth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  ∀ callbackAvailable callbackScope {leftAbstract rightAbstract},
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
        rhoReflectivePresentation rawDeclaration rawStop leftAbstract
          rightAbstract →
      PatternLeafAligned relation
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (leftEnvironment.reify leftAbstract))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))

/-- The semantic stop obligation after every certified-boundary/boundary pair
has been removed.  The remaining cases are precisely those in which at least
one reached plan is an authored source plan. -/
def RhoStaticNonBoundaryPlanStopRestoration
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
    ∀ sourceDepth,
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.thinning.thickenAmbientBVars sourceDepth
              (mapPattern (color.symbols rhoCIGSLT) rightLeaf)))
  ∀ callbackAvailable callbackScope {leftAbstract rightAbstract}
      {leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
        targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT color
        (mapTypeExpr (color.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (color.symbols rhoCIGSLT) rightReached.sourceType)))
      (_stopReason : rawStop leftPayload rightPayload ∨
        CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
          rightReached.plan)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary)),
      PatternLeafAligned relation
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (leftEnvironment.reify leftAbstract))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))

namespace RhoStaticPlanStopRestoration

/-- Close one pair of reached boundary roots as a semantic leaf.

The reached-plan producer supplies equality of the active availability fibre.
The two singleton boundary certificates then select exact atoms in the root
environments. Recursive closure is invoked only for their strictly smaller
contents; the resulting depth-indexed apex is compressed to the uniform leaf
relation consumed by keyed canonical congruence. -/
noncomputable def boundaryPair_sourcePatternLeafAligned_of_closeSmaller
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
    (leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftNode.plan.abstractPattern)
    (rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightNode.plan.abstractPattern)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [leftStopped.certified.typed] leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [rightStopped.certified.typed] rightNode.plan.boundaryTable.entries)
    (supportEq : leftStopped.certified.typed.boundary.targetSupport =
      rightStopped.certified.typed.boundary.targetSupport)
    (typeEq : leftStopped.certified.typed.boundary.targetType =
      rightStopped.certified.typed.boundary.targetType)
    (childDeclaration : ReflectivePresentationDecl)
    (canonical :
      canonicalize childDeclaration
          leftStopped.certified.typed.boundary.content =
        canonicalize childDeclaration
          rightStopped.certified.typed.boundary.content)
    (parentMeasure : Nat)
    (smaller :
      sizeOf leftStopped.certified.typed.boundary.content +
          sizeOf rightStopped.certified.typed.boundary.content < parentMeasure)
    (rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightStopped.certified.typed.boundary.targetType)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild < parentMeasure →
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
        (leftEnvironment.reify
          (.fvar leftStopped.boundaryOccurrence.name)))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify
          (.fvar rightStopped.boundaryOccurrence.name))) := by
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
  let leftAtRoot := leftStopped.castRoot leftNode.skeleton_pattern.symm
  let rightAtRoot := rightStopped.castRoot rightNode.skeleton_pattern.symm
  obtain ⟨leftSlot, leftSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (leftEnvironment.slotOfName?_isSome_of_occurrence
      leftAtRoot.boundaryOccurrence)
  obtain ⟨rightSlot, rightSelectedAtRoot⟩ := Option.isSome_iff_exists.mp
    (rightEnvironment.slotOfName?_isSome_of_occurrence
      rightAtRoot.boundaryOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      leftStopped.boundaryOccurrence.name = some leftSlot := by
    simpa [leftAtRoot] using leftSelectedAtRoot
  have rightSelected : rightEnvironment.slotOfName?
      rightStopped.boundaryOccurrence.name = some rightSlot := by
    simpa [rightAtRoot] using rightSelectedAtRoot
  have leftSelectedBoundary : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftStopped.certified.typed.boundary) =
        some leftSlot := by
    simpa only [CostStaticPlanStopped.boundaryOccurrence_name] using leftSelected
  have rightSelectedBoundary : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightStopped.certified.typed.boundary) =
        some rightSlot := by
    simpa only [CostStaticPlanStopped.boundaryOccurrence_name] using rightSelected
  have leftEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftAtRoot.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa [leftAtRoot] using leftEmbedding
  have rightEmbeddingAtRoot : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightAtRoot.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa [rightAtRoot] using rightEmbedding
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
  apply PatternLeafAligned.leaf
  intro sourceDepth
  have restores :
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (.fvar (leftEnvironment.atomName leftSlot)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))) :=
    CostStaticAtomKeyCospan.CommonRestorationApex.restoresTogether_of_forall_apex
      (fun depth =>
        CostStaticPlanStopped.selectedAtoms_commonRestorationApex_of_closeSmaller
          leftAtRoot rightAtRoot leftEmbeddingAtRoot rightEmbeddingAtRoot
          leftTrees rightTrees leftEnvironment rightEnvironment leftSlot
          leftSelectedAtRoot rightSlot rightSelectedAtRoot (Or.inl (by
            simpa [leftAtRoot, rightAtRoot] using supportEq)) (by
            simpa [leftAtRoot, rightAtRoot] using typeEq) childDeclaration
          rhoReflectivePresentation (by
            simpa [leftAtRoot, rightAtRoot] using canonical) parentMeasure (by
            simpa [leftAtRoot, rightAtRoot] using smaller) (by
            simpa [rightAtRoot] using rightAdmissible) closeSmaller depth)
  simpa [relation, cospan, mapPattern,
    CostStaticBinderThinning.thickenAmbientBVars,
    CostStaticAtomEnvironment.reifyName,
    CostStaticPlanStopped.boundaryOccurrence_name,
    leftSelectedBoundary, rightSelectedBoundary] using restores

/-- Close any pair of reached certified boundary plans once their exact
boundary views have been exposed.  Applications and collections share this
semantic proof: the views identify the singleton entries, while the retained
type route supplies admissibility of the reached target fibre. -/
noncomputable def boundaryViews_sourcePatternLeafAligned_of_closeSmaller
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
    (leftBoundary : leftReached.BoundaryView)
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
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
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
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [leftBoundary.stopped.certified.typed]
        leftNode.plan.boundaryTable.entries := by
    simpa only [leftBoundary.entries_eq] using leftEmbedding
  have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree [rightBoundary.stopped.certified.typed]
        rightNode.plan.boundaryTable.entries := by
    simpa only [rightBoundary.entries_eq] using rightEmbedding
  have supportEq :
      leftBoundary.stopped.certified.typed.boundary.targetSupport =
        rightBoundary.stopped.certified.typed.boundary.targetSupport :=
    leftBoundary.targetSupport_eq.trans
      (sourceAvailableEq.trans rightBoundary.targetSupport_eq.symm)
  have targetTypeEq :
      leftBoundary.stopped.certified.typed.boundary.targetType =
        rightBoundary.stopped.certified.typed.boundary.targetType :=
    leftBoundary.targetType_eq.trans
      ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
        rightBoundary.targetType_eq.symm)
  have canonical : canonicalize childDeclaration
        leftBoundary.stopped.certified.typed.boundary.content =
      canonicalize childDeclaration
        rightBoundary.stopped.certified.typed.boundary.content := by
    rw [leftBoundary.content_eq, rightBoundary.content_eq]
    exact rawAligned.canonicalize_eq childDeclaration stopCanonical
  have leftMember : leftBoundary.stopped.certified.typed ∈
      leftNode.plan.boundaryTable.entries :=
    leftEmbedding'.subset (by simp)
  have rightMember : rightBoundary.stopped.certified.typed ∈
      rightNode.plan.boundaryTable.entries :=
    rightEmbedding'.subset (by simp)
  have leftSmaller :=
    leftNode.plan.boundary_content_size_lt_of_isStaticRoot
      leftNode.rootStatic leftBoundary.stopped.certified.typed leftMember
  have rightSmaller :=
    rightNode.plan.boundary_content_size_lt_of_isStaticRoot
      rightNode.rootStatic rightBoundary.stopped.certified.typed rightMember
  have smaller :
      sizeOf leftBoundary.stopped.certified.typed.boundary.content +
          sizeOf rightBoundary.stopped.certified.typed.boundary.content <
        sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
    omega
  obtain ⟨rightRoute⟩ := rightRoute
  have rightEndpointAdmissible :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalTypeRoute.rho_admissible
      rightRoute rightRootAdmissible
  have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      rightBoundary.stopped.certified.typed.boundary.targetType := by
    rw [rightBoundary.targetType_eq]
    exact rightEndpointAdmissible
  simpa only [leftBoundary.abstract_eq, rightBoundary.abstract_eq,
    CostStaticPlanStopped.boundaryOccurrence_name] using
    boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode rightNode
      leftTrees rightTrees leftEnvironment rightEnvironment
      leftBoundary.stopped rightBoundary.stopped leftEmbedding' rightEmbedding'
      supportEq targetTypeEq childDeclaration canonical
      (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
      rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth

/-- Close a pair of reached foreign-application plans.

At a foreign application the reached payload is itself the sole certified
boundary content, while the plan abstraction is the boundary atom.  The
retained application typing forces a base target fibre, so recursive-domain
admissibility is local and does not require a route witness from the root. -/
noncomputable def boundaryApplications_sourcePatternLeafAligned_of_closeSmaller
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
    (leftClass : leftReached.plan.rootClass = .boundaryApplication)
    (rightClass : rightReached.plan.rootClass = .boundaryApplication)
    (sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
    (sourceAvailableEq : leftReached.sourceAvailable =
      rightReached.sourceAvailable)
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries)
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
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
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  rcases leftReached with
    ⟨leftSourceBound, leftTargetBound, leftThinning, leftAvailable,
      leftOuter, leftSourceType, leftPlan, leftSkeletonContext,
      leftAbstractEq⟩
  rcases rightReached with
    ⟨rightSourceBound, rightTargetBound, rightThinning, rightAvailable,
      rightOuter, rightSourceType, rightPlan, rightSkeletonContext,
      rightAbstractEq⟩
  cases leftPlan with
  | @boundaryApplication _ _ _ _ _ leftWire leftArguments _
      leftConstructor leftRendered leftOutside leftCertified leftCertifies =>
    cases rightPlan with
    | @boundaryApplication _ _ _ _ _ rightWire rightArguments _
        rightConstructor rightRendered rightOutside rightCertified
          rightCertifies =>
      let leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.apply leftWire leftArguments) leftNode.plan.abstractPattern :=
        { boundarySupport := leftAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) leftSourceType
          content := .apply leftWire leftArguments
          certified := leftCertified
          certifies := leftCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := leftSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using leftAbstractEq }
      let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.apply rightWire rightArguments) rightNode.plan.abstractPattern :=
        { boundarySupport := rightAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) rightSourceType
          content := .apply rightWire rightArguments
          certified := rightCertified
          certifies := rightCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := rightSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using rightAbstractEq }
      have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [leftStopped.certified.typed]
            leftNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [leftCertified.typed] leftNode.plan.boundaryTable.entries at leftEmbedding
        exact leftEmbedding
      have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [rightStopped.certified.typed]
            rightNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [rightCertified.typed] rightNode.plan.boundaryTable.entries at rightEmbedding
        exact rightEmbedding
      have supportEq : leftStopped.certified.typed.boundary.targetSupport =
          rightStopped.certified.typed.boundary.targetSupport := by
        exact leftCertified.targetSupport_eq.trans
          (sourceAvailableEq.trans rightCertified.targetSupport_eq.symm)
      have targetTypeEq : leftStopped.certified.typed.boundary.targetType =
          rightStopped.certified.typed.boundary.targetType := by
        exact leftCertified.targetType_eq.trans
          ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
            rightCertified.targetType_eq.symm)
      have canonical : canonicalize childDeclaration
            leftStopped.certified.typed.boundary.content =
          canonicalize childDeclaration
            rightStopped.certified.typed.boundary.content := by
        rw [leftCertified.content_eq, rightCertified.content_eq]
        exact rawAligned.canonicalize_eq childDeclaration stopCanonical
      have leftMember : leftStopped.certified.typed ∈
          leftNode.plan.boundaryTable.entries :=
        leftEmbedding'.subset (by simp)
      have rightMember : rightStopped.certified.typed ∈
          rightNode.plan.boundaryTable.entries :=
        rightEmbedding'.subset (by simp)
      have leftSmaller :=
        leftNode.plan.boundary_content_size_lt_of_isStaticRoot
          leftNode.rootStatic leftStopped.certified.typed leftMember
      have rightSmaller :=
        rightNode.plan.boundary_content_size_lt_of_isStaticRoot
          rightNode.rootStatic rightStopped.certified.typed rightMember
      have smaller :
          sizeOf leftStopped.certified.typed.boundary.content +
              sizeOf rightStopped.certified.typed.boundary.content <
            sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
        omega
      obtain ⟨rightCategory, rightTypeBase⟩ :=
        rightCertified.exists_targetType_eq_base_of_application
      have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          rightStopped.certified.typed.boundary.targetType := by
        rw [rightTypeBase]
        exact rhoCanonicalRecursiveTypeDomain.base rightCategory
      exact boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode
        rightNode leftTrees rightTrees leftEnvironment rightEnvironment
        leftStopped rightStopped leftEmbedding' rightEmbedding' supportEq
        targetTypeEq childDeclaration canonical
        (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
        rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth
    | bvar | fvar | application | lambda | multiLambda | collection |
        boundaryCollection =>
      simp [CostStaticRegionPlan.rootClass] at rightClass
  | bvar | fvar | application | lambda | multiLambda | collection |
      boundaryCollection =>
    simp [CostStaticRegionPlan.rootClass] at leftClass

/-- Close a pair of reached foreign-collection plans.

Unlike a foreign application, a certified collection boundary may inhabit
either a structural collection fibre or an authored bare-collection base
fibre.  The retained type route is therefore the authoritative admissibility
witness: it transports the admissible root fibre to the exact reached source
type, and certification identifies that type with the boundary target. -/
noncomputable def boundaryCollections_sourcePatternLeafAligned_of_closeSmaller
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
    (leftClass : leftReached.plan.rootClass = .boundaryCollection)
    (rightClass : rightReached.plan.rootClass = .boundaryCollection)
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
      (mapTypeExpr (color.symbols rhoCIGSLT) (.base rightNode.sourceSort.1)))
    (childDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned childDeclaration rawStop leftPayload
      rightPayload)
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize childDeclaration left = canonicalize childDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize childDeclaration leftChild =
          canonicalize childDeclaration rightChild →
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
        scopeDepth (leftEnvironment.reify leftReached.plan.abstractPattern))
      (canonicalizeByDepths rightKey rhoReflectivePresentation availableDepth
        scopeDepth
        (rightEnvironment.reify rightReached.plan.abstractPattern)) := by
  rcases leftReached with
    ⟨leftSourceBound, leftTargetBound, leftThinning, leftAvailable,
      leftOuter, leftSourceType, leftPlan, leftSkeletonContext,
      leftAbstractEq⟩
  rcases rightReached with
    ⟨rightSourceBound, rightTargetBound, rightThinning, rightAvailable,
      rightOuter, rightSourceType, rightPlan, rightSkeletonContext,
      rightAbstractEq⟩
  cases leftPlan with
  | @boundaryCollection _ _ _ _ _ leftCollectionType leftElements leftRest
      leftSourceType leftCurrentRejected leftOppositeChoice
      leftOppositeSelected leftCertified leftCertifies =>
    cases rightPlan with
    | @boundaryCollection _ _ _ _ _ rightCollectionType rightElements
        rightRest rightSourceType rightCurrentRejected rightOppositeChoice
        rightOppositeSelected rightCertified rightCertifies =>
      let leftStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.collection leftCollectionType leftElements leftRest)
          leftNode.plan.abstractPattern :=
        { boundarySupport := leftAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) leftSourceType
          content := .collection leftCollectionType leftElements leftRest
          certified := leftCertified
          certifies := leftCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := leftSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using leftAbstractEq }
      let rightStopped : CostStaticPlanStopped rhoCIGSLT color targetFree
          (.collection rightCollectionType rightElements rightRest)
          rightNode.plan.abstractPattern :=
        { boundarySupport := rightAvailable
          boundaryType := mapTypeExpr (color.symbols rhoCIGSLT) rightSourceType
          content := .collection rightCollectionType rightElements rightRest
          certified := rightCertified
          certifies := rightCertifies
          residual := .hole
          content_eq := rfl
          skeletonContext := rightSkeletonContext
          abstract_eq := by
            simpa [CostStaticRegionPlan.abstractPattern] using rightAbstractEq }
      have leftEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [leftStopped.certified.typed]
            leftNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [leftCertified.typed] leftNode.plan.boundaryTable.entries at leftEmbedding
        exact leftEmbedding
      have rightEmbedding' : CostStaticPlanEntryEmbedding rhoCIGSLT color
          targetFree [rightStopped.certified.typed]
            rightNode.plan.boundaryTable.entries := by
        change CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
          [rightCertified.typed] rightNode.plan.boundaryTable.entries at rightEmbedding
        exact rightEmbedding
      have supportEq : leftStopped.certified.typed.boundary.targetSupport =
          rightStopped.certified.typed.boundary.targetSupport := by
        exact leftCertified.targetSupport_eq.trans
          (sourceAvailableEq.trans rightCertified.targetSupport_eq.symm)
      have targetTypeEq : leftStopped.certified.typed.boundary.targetType =
          rightStopped.certified.typed.boundary.targetType := by
        exact leftCertified.targetType_eq.trans
          ((congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq).trans
            rightCertified.targetType_eq.symm)
      have canonical : canonicalize childDeclaration
            leftStopped.certified.typed.boundary.content =
          canonicalize childDeclaration
            rightStopped.certified.typed.boundary.content := by
        rw [leftCertified.content_eq, rightCertified.content_eq]
        exact rawAligned.canonicalize_eq childDeclaration stopCanonical
      have leftMember : leftStopped.certified.typed ∈
          leftNode.plan.boundaryTable.entries :=
        leftEmbedding'.subset (by simp)
      have rightMember : rightStopped.certified.typed ∈
          rightNode.plan.boundaryTable.entries :=
        rightEmbedding'.subset (by simp)
      have leftSmaller :=
        leftNode.plan.boundary_content_size_lt_of_isStaticRoot
          leftNode.rootStatic leftStopped.certified.typed leftMember
      have rightSmaller :=
        rightNode.plan.boundary_content_size_lt_of_isStaticRoot
          rightNode.rootStatic rightStopped.certified.typed rightMember
      have smaller :
          sizeOf leftStopped.certified.typed.boundary.content +
              sizeOf rightStopped.certified.typed.boundary.content <
            sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
        omega
      obtain ⟨rightRoute⟩ := rightRoute
      have rightEndpointAdmissible :=
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalTypeRoute.rho_admissible
          rightRoute rightRootAdmissible
      have rightAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
          rightStopped.certified.typed.boundary.targetType := by
        rw [rightCertified.targetType_eq]
        exact rightEndpointAdmissible
      exact boundaryPair_sourcePatternLeafAligned_of_closeSmaller leftNode
        rightNode leftTrees rightTrees leftEnvironment rightEnvironment
        leftStopped rightStopped leftEmbedding' rightEmbedding' supportEq
        targetTypeEq childDeclaration canonical
        (sizeOf leftNode.term.1 + sizeOf rightNode.term.1) smaller
        rightAdmissible closeSmaller leftKey rightKey availableDepth scopeDepth
    | bvar | fvar | boundaryApplication | application | lambda | multiLambda |
        collection =>
      simp [CostStaticRegionPlan.rootClass] at rightClass
  | bvar | fvar | boundaryApplication | application | lambda | multiLambda |
      collection =>
    simp [CostStaticRegionPlan.rootClass] at leftClass

/-- Extend a restoration callback for stops with at least one authored-source
root to every plan stop.  The omitted certified-boundary/boundary quadrant is
closed internally from its exact boundary views and the recursive smaller-pair
provider. -/
noncomputable def of_nonBoundaryRemainder
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rawDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize rawDeclaration left = canonicalize rawDeclaration right)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize rawDeclaration leftChild =
          canonicalize rawDeclaration rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (remaining : RhoStaticNonBoundaryPlanStopRestoration leftView rightView
      rawDeclaration rawStop) :
    RhoStaticPlanStopRestoration leftView rightView rawDeclaration rawStop := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract stopped
  rcases stopped with
    ⟨leftPayload, rightPayload, leftReached, rightReached, leftAbstractEq,
      rightAbstractEq, sourceTypeEq, sourceAvailableEq, leftEmbedding,
      rightEmbedding, leftRoute, rightRoute, stopReason, rawAligned⟩
  by_cases leftBoundary :
      leftReached.plan.rootClass.IsCertifiedBoundary
  · by_cases rightBoundary :
        rightReached.plan.rootClass.IsCertifiedBoundary
    · obtain ⟨leftBoundaryView⟩ :=
        leftReached.nonempty_boundaryView_of_boundaryClass leftBoundary
      obtain ⟨rightBoundaryView⟩ :=
        rightReached.nonempty_boundaryView_of_boundaryClass rightBoundary
      obtain ⟨leftEmbedding⟩ := leftEmbedding
      obtain ⟨rightEmbedding⟩ := rightEmbedding
      have boundaryResult :=
        boundaryViews_sourcePatternLeafAligned_of_closeSmaller
        leftView.node rightView.node leftView.children rightView.children
        (CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        (CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        leftReached rightReached leftBoundaryView rightBoundaryView sourceTypeEq
        sourceAvailableEq leftEmbedding rightEmbedding rightRoute
        rightRootAdmissible rawDeclaration rawAligned stopCanonical closeSmaller
        (sourceSemanticPatternKeyAt leftView.node
          (CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
        (sourceSemanticPatternKeyAt rightView.node
          (CostStaticAtomEnvironment.ofInventory
            (rightView.node.semanticAtomEnvironment
              (rightView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
          callbackAvailable callbackScope
      simpa only [leftAbstractEq, rightAbstractEq] using boundaryResult
    · exact remaining callbackAvailable callbackScope leftReached rightReached
        leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
        leftEmbedding rightEmbedding leftRoute rightRoute stopReason rawAligned
        (fun both => rightBoundary both.2)
  · exact remaining callbackAvailable callbackScope leftReached rightReached
      leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason rawAligned
      (fun both => leftBoundary both.1)

end RhoStaticPlanStopRestoration

namespace RhoStaticFramesRestorationAligned

/-- Construct matched-frame restoration from a raw canonical stop descent.
All rigid free-variable leaves are internal consequences; the remaining
callback is indexed by the exact reached plans and their root embeddings. -/
noncomputable def ofProvenancedRawAlignment
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (rawDeclaration : ReflectivePresentationDecl)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop
      leftView.node.term.1 rightView.node.term.1)
    (planCallback : RhoStaticPlanStopRestoration leftView rightView
      rawDeclaration rawStop) :
    RhoStaticFramesRestorationAligned leftView rightView := by
  let leftValues := leftView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let rightValues := rightView.children.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  let leftInventory :=
    (leftView.node.semanticAtomEnvironment leftValues).1
  let rightInventory :=
    (rightView.node.semanticAtomEnvironment rightValues).1
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory leftInventory
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory rightInventory
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment leftView
    rightView
  rw [← leftView.targetBound_length_eq_targetBound_length rightView]
  exact reifiedSourceAlignment_of_rawAlignment leftView.node rightView.node
    leftView.children rightView.children leftEnvironment rightEnvironment
    (leftView.targetBound_eq_targetBound rightView)
    (leftView.sourceSort_eq_sourceSort rightView) rawDeclaration rawAligned
    (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
    (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
    leftView.node.targetBound.length 0 planCallback

end RhoStaticFramesRestorationAligned

namespace RhoCanonicalStaticPairSemanticCut

/-- The matched provider arm reduced to its sole plan-stop restoration
obligation.  Raw canonical descent, free-variable restoration, and the final
matched cut are assembled here. -/
noncomputable def matchedOfProvenancedPlanStops
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (roots : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern rightPattern)
    (_canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern)
    (planStops :
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl
      RhoStaticPlanStopRestoration leftView rightView declaration
        (fun candidateLeft candidateRight =>
          ((CollapsingRoot declaration candidateLeft ∨
              CollapsingRoot declaration candidateRight) ∧
            canonicalize declaration candidateLeft =
              canonicalize declaration candidateRight) ∧
          sizeOf candidateLeft + sizeOf candidateRight <
            sizeOf leftPattern + sizeOf rightPattern)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.aligned color leftView rightView roots) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation.toReflectivePresentationDecl
  have nodeRoots : CanonicalRootAligned declaration leftView.node.term.1
      rightView.node.term.1 := by
    rw [leftView.patternEq, rightView.patternEq]
    exact roots
  let rawAligned := canonicalStopAligned_of_root_aligned declaration nodeRoots
  exact matchedOfRestorationAligned leftView rightView roots
    (RhoStaticFramesRestorationAligned.ofProvenancedRawAlignment leftView
      rightView declaration (by
        simpa [declaration, leftView.patternEq, rightView.patternEq] using
          rawAligned)
      planStops)

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
