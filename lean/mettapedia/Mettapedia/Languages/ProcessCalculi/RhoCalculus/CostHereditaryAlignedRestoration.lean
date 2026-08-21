import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderLeftCollapsing

/-!
# The aligned arm of the rho static-pair provider

`RhoAlignedViewsRestorationAlignedInDomain` asks two same-colour static root
views of a root-aligned pair to be restoration-aligned.  This module reduces
that obligation to a single node-local statement about plan stops, and
records the exact relationship between the two interfaces the lane uses for
such statements.

## What is established here

* `canonicalize_eq_of_canonicalRootAligned` — a root alignment does yield
  equality of the two canonical forms.  Every constructor of
  `CanonicalRootAligned` either fixes a rigid root that canonicalization
  preserves, or supplies childwise canonical equality; the collapsing stop
  produced by `canonicalStopAligned_of_root_aligned` carries that equality in
  its own certificate.  Consequently the aligned obligation is implied by the
  unsplit restoration obligation, and any consumer of the aligned arm may
  help itself to raw canonical equality.

* `RhoStaticPlanStopSourceAligned` — the depth-uniform source form of the
  plan-stop obligation, and
  `rhoAlignedViewsRestorationAligned_of_planStopSourceAligned`, which
  discharges the whole aligned obligation from it.  The route is the intended
  one: `canonicalStopAligned_of_root_aligned` turns the root alignment into a
  stop descent whose every delegated pair is strictly smaller than the
  endpoint pair, `reifiedSourceAlignment_of_rawAlignment` performs the plan
  descent, membership-certified free-variable routing and semantic-atom
  reification, and `ofSourceCanonicalAlignment` transports the source
  certificate to the target frames.  Nothing of the root alignment survives
  past the first step, so the constructor list of `CanonicalRootAligned` is
  not the case analysis: the residual content is per plan-stop
  configuration.

* `RhoStaticPlanStopSourceAligned.of_nonBoundaryRemainder` — the
  certified-boundary/certified-boundary quadrant of that obligation is
  discharged outright by the existing boundary producer, leaving
  `RhoStaticNonBoundaryPlanStopSourceAligned`.

* `rhoAlignedViewsPlanStopApex_of_sourceAligned` — the depth-uniform source
  obligation implies the one-depth `RhoStaticPlanStopCommonApex` obligation
  at the same raw stop.  The converse does not hold definitionally: the apex
  interface canonicalizes and reinserts ambient binders at one and the same
  depth, whereas the source interface reinserts at an arbitrary depth while
  canonicalizing at the callback's own scope.  The residual left by this
  module is therefore strictly stronger than the residual the apex chain
  carries.

* `rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex` — the aligned
  bridge case of the semantic cut needs only the apex obligation.  Combined
  with the previous item this says the aligned arm of the provider does not
  require `RhoAlignedViewsRestorationAlignedInDomain` at all.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-! ## Root alignment is a canonical equality -/

/-- A structural root alignment determines equality of the two canonical
forms.  The stop descent forced by the root alignment delegates only pairs
that already carry canonical equality, so the eliminator recovers it at the
root. -/
theorem canonicalize_eq_of_canonicalRootAligned
    (declaration : ReflectivePresentationDecl) {left right : Pattern}
    (aligned : CanonicalRootAligned declaration left right) :
    canonicalize declaration left = canonicalize declaration right :=
  (canonicalStopAligned_of_root_aligned declaration aligned).canonicalize_eq
    declaration (fun given => given.1.2)

/-- The unsplit restoration obligation implies the aligned half.  The two
halves of the split are therefore a weakening chain after all. -/
theorem RhoStaticViewsRestorationAlignedInDomain.toAligned
    {declarationColor : CostStaticColor}
    (restoration : RhoStaticViewsRestorationAlignedInDomain declarationColor) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor :=
  fun leftView rightView _admissible _leftWellSorted _rightWellSorted
      _closeSmaller roots =>
    restoration leftView rightView
      (canonicalize_eq_of_canonicalRootAligned _ roots)

/-! ## The plan-stop obligation in depth-uniform source form -/

/-- The depth-uniform source form of the plan-stop obligation: every stop of
the raw descent must expose a semantic-leaf alignment of the two keyed,
reified, canonicalized abstractions, with the restoration depth universally
quantified. -/
def RhoStaticPlanStopSourceAligned
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
    (declarationColor : CostStaticColor)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  ∀ callbackAvailable callbackScope {leftAbstract rightAbstract},
    CostStaticPlanCanonicalStop leftView.node.plan rightView.node.plan
        rhoReflectivePresentation rawDeclaration rawStop leftAbstract
        rightAbstract →
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      PatternLeafAligned
        (fun leftLeaf rightLeaf => ∀ sourceDepth,
          ReflectiveContextSupport.RestoresTogether
            rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
              cospan.commonAssignment
              (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
                (leftView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
              (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
                (rightView.node.thinning.thickenAmbientBVars sourceDepth
                  (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (leftEnvironment.reify leftAbstract))
        (canonicalizeByDepths
          (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
          rhoReflectivePresentation callbackAvailable callbackScope
          (rightEnvironment.reify rightAbstract))

/-- **Obligation A1 from the depth-uniform plan-stop obligation alone.**

The root alignment is consumed once, by `canonicalStopAligned_of_root_aligned`;
what remains is the plan-stop callback at the strict measure the provider's
recursion already supplies. -/
theorem rhoAlignedViewsRestorationAligned_of_planStopSourceAligned
    {declarationColor : CostStaticColor}
    (planStops : ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer
        rightPattern type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      RhoStaticPlanStopSourceAligned leftView rightView declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller roots
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment leftView
    rightView
  have rawAligned := canonicalStopAligned_of_root_aligned
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation) roots
  have stops := planStops leftView rightView admissible leftWellSorted
    rightWellSorted closeSmaller
  have result := reifiedSourceAlignment_of_rawAlignment leftView.node
    rightView.node leftView.children rightView.children
    (CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (leftView.targetBound_eq_targetBound rightView)
    (leftView.sourceSort_eq_sourceSort rightView)
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    (rawStop := RhoCanonicalRawStop declarationColor
      (sizeOf leftPattern + sizeOf rightPattern))
    (by
      rw [leftView.patternEq, rightView.patternEq]
      exact rawAligned)
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
    leftView.node.targetBound.length 0
    (fun callbackAvailable callbackScope {_leftAbstract _rightAbstract} stop =>
      stops callbackAvailable callbackScope stop)
  rw [leftView.targetBound_length_eq_targetBound_length rightView] at result ⊢
  exact result

/-! ## The certified-boundary quadrant -/

/-- The non-boundary residual of the depth-uniform plan-stop obligation.  The
retained reached-plan evidence is exactly that of
`RhoStaticNonBoundaryPlanStopCommonApex`; only the conclusion differs. -/
def RhoStaticNonBoundaryPlanStopSourceAligned
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
    (declarationColor : CostStaticColor)
    (rawStop : Pattern → Pattern → Prop) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let leftEnvironment := CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  let rightEnvironment := CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1
  ∀ callbackAvailable callbackScope
      {leftAbstract rightAbstract leftPayload rightPayload}
      (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree
        leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
        rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceAvailableEq : leftReached.sourceAvailable =
        rightReached.sourceAvailable)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
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
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary)),
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    PatternLeafAligned
      (fun leftLeaf rightLeaf => ∀ sourceDepth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightView.node.thinning.thickenAmbientBVars sourceDepth
                (mapPattern (color.symbols rhoCIGSLT) rightLeaf))))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt leftView.node leftEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (leftEnvironment.reify leftAbstract))
      (canonicalizeByDepths
        (sourceSemanticPatternKeyAt rightView.node rightEnvironment)
        rhoReflectivePresentation callbackAvailable callbackScope
        (rightEnvironment.reify rightAbstract))

/-- The right-root admissibility consumed by the boundary quadrant is the
ambient admissibility of the obligation's typed fibre, transported along the
view's own result-type equation. -/
theorem rightRootAdmissible_of_admissible
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {rightPattern : Pattern}
    {type : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (rightView : right.StaticRootView color)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type) :
    rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)) := by
  have typeEq := rightView.typeEq
  simpa only [← typeEq, mapTypeExpr, CostStaticColor.mapLangSort_name]
    using admissible

/-- The certified-boundary/certified-boundary quadrant of the depth-uniform
plan-stop obligation is discharged by the existing boundary producer, which
consumes exactly the provider's strictly-smaller recursion callback. -/
noncomputable def RhoStaticPlanStopSourceAligned.of_nonBoundaryRemainder
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
    (declarationColor : CostStaticColor)
    {rawStop : Pattern → Pattern → Prop}
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
    (stopCanonical : ∀ {left right}, rawStop left right →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
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
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1 →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType))
    (remaining : RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
      declarationColor rawStop) :
    RhoStaticPlanStopSourceAligned leftView rightView declarationColor
      rawStop := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract stopped
  rcases stopped with
    ⟨leftPayload, rightPayload, leftReached, rightReached,
      leftAdmission, rightAdmission, leftAbstractEq, rightAbstractEq,
      sourceTypeEq, sourceAvailableEq, sourceBoundEq, targetBoundEq,
      thinningEq, leftEmbedding, rightEmbedding, leftRoute, rightRoute,
      stopReason, leftPayloadSizeLe, rightPayloadSizeLe, rawAligned⟩
  by_cases leftBoundary : leftReached.plan.rootClass.IsCertifiedBoundary
  · by_cases rightBoundary : rightReached.plan.rootClass.IsCertifiedBoundary
    · obtain ⟨leftBoundaryView⟩ :=
        leftReached.nonempty_boundaryView_of_boundaryClass leftBoundary
      obtain ⟨rightBoundaryView⟩ :=
        rightReached.nonempty_boundaryView_of_boundaryClass rightBoundary
      obtain ⟨leftEmbedding⟩ := leftEmbedding
      obtain ⟨rightEmbedding⟩ := rightEmbedding
      have boundaryResult :=
        RhoStaticPlanBoundaryRestoration.boundaryViews_sourcePatternLeafAligned_of_closeSmaller
          leftView.node rightView.node leftView.children rightView.children
          (CostStaticAtomEnvironment.ofInventory
            (leftView.node.semanticAtomEnvironment
              (leftView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          (CostStaticAtomEnvironment.ofInventory
            (rightView.node.semanticAtomEnvironment
              (rightView.children.normalizeValues
                (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
          leftReached rightReached leftBoundaryView rightBoundaryView
          sourceTypeEq sourceAvailableEq leftEmbedding rightEmbedding
          rightRoute rightRootAdmissible
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          rawAligned stopCanonical closeSmaller
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
        leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute rightRoute stopReason
        leftPayloadSizeLe rightPayloadSizeLe rawAligned
        (fun both => rightBoundary both.2)
  · exact remaining callbackAvailable callbackScope leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
      rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
      rightPayloadSizeLe rawAligned (fun both => leftBoundary both.1)

/-- **Obligation A1 from the non-boundary plan-stop residual alone.**

This is the whole remaining content of the aligned obligation: every plan
stop of the strict raw descent at which the two reached root classes are not
both certified boundaries. -/
theorem rhoAlignedViewsRestorationAligned_of_nonBoundaryRemainder
    {declarationColor : CostStaticColor}
    (remaining : ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer
        rightPattern type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
        declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor := by
  apply rhoAlignedViewsRestorationAligned_of_planStopSourceAligned
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller
  refine RhoStaticPlanStopSourceAligned.of_nonBoundaryRemainder leftView
    rightView declarationColor
    (rightRootAdmissible_of_admissible rightView admissible)
    (fun stopped => stopped.1.2) ?_
    (remaining leftView rightView admissible leftWellSorted rightWellSorted
      closeSmaller)
  intro childAvailable childOuter leftChild rightChild childType
    leftChildWellSorted rightChildWellSorted childCanonical smaller
    childAdmissible
  refine closeSmaller leftChildWellSorted rightChildWellSorted childCanonical
    ?_ childAdmissible
  rw [leftView.patternEq, rightView.patternEq] at smaller
  exact smaller

/-! ## Relation to the one-depth apex interface -/

/-- The depth-uniform source obligation implies the one-depth apex obligation
at the same raw stop.  The apex interface instantiates the restoration depth
to the callback's own scope depth; the source interface leaves it free. -/
theorem rhoAlignedViewsPlanStopApex_of_sourceAligned
    {declarationColor : CostStaticColor}
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
    {rawStop : Pattern → Pattern → Prop}
    (source : RhoStaticPlanStopSourceAligned leftView rightView
      declarationColor rawStop) :
    RhoStaticPlanStopCommonApex leftView rightView declarationColor rawStop :=
  fun callbackAvailable callbackScope callbackRoot
      {_leftAbstract _rightAbstract} stop =>
    RhoStaticPlanStopCommonApex.ofSourcePatternLeafAligned leftView.node
      rightView.node (leftView.targetBound_eq_targetBound rightView) _ _
      (source callbackAvailable callbackScope stop) callbackScope callbackRoot

/-- The aligned bridge case of the semantic cut from the one-depth apex
obligation alone.  No restoration alignment of the two static frames is
consumed. -/
noncomputable def rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex
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
    (apex : RhoStaticPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern))) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.aligned color leftView rightView roots) :=
  RhoCanonicalStaticPairSemanticCut.matchedOfProvenancedPlanStops leftView
    rightView roots (canonicalize_eq_of_canonicalRootAligned _ roots) apex

/-! ## The apex-form aligned obligation, and why it replaces A1

A1 asks for restoration alignment in *source* form: `PatternLeafAligned` over
a relation universally quantified in the ambient-reinsertion depth.  The
aligned arm does not need that.  It needs only
`RhoStaticPlanStopCommonApex`, which
`rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex` above converts
into the cut — the canonical-equality premise coming free from
`canonicalize_eq_of_canonicalRootAligned`.

The two are siblings, not ordered: both A1 and A1′ follow from the single
intermediate `RhoStaticPlanStopSourceAligned` — A1 by
`rhoAlignedViewsRestorationAligned_of_planStopSourceAligned`, A1′ by
`rhoAlignedViewsPlanStopApex_of_sourceAligned`.  No implication between A1
and A1′ is established here in either direction, and the apex ⟹ source
direction is blocked through the current interfaces:
`RhoReachedPlanPairCommonApex` reuses `callbackScope` for both the
canonicalization scope and the ambient-binder reinsertion, while the source
form leaves that reinsertion depth universally quantified, and
`CommonRestorationApex.restoresTogether_of_forall_apex` recovers only the
diagonal.  A1's residual is therefore *at least as strong* as the residual
the rest of the lane carries, with no route back.

That matters practically, because the tools built for this configuration all
conclude in apex form: `CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead`
and the whole `ofRecursiveSameColorQuotePair` chain serve the apex residual
and cannot be applied to A1's source residual.  Keeping A1 would duplicate
that work in a stronger form; taking the apex obligation inherits it. -/

/-- **Obligation A1′ — the aligned arm in apex form.**  Strictly weaker than
`RhoAlignedViewsRestorationAlignedInDomain`, and the form every existing tool
for this configuration already produces. -/
def RhoAlignedViewsPlanStopApexInDomain (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    CanonicalRootAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern rightPattern →
    RhoStaticPlanStopCommonApex leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern))

/-- **The provider from the apex-form obligations.** -/
theorem rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexObligations
    {declarationColor : CostStaticColor}
    (alignedApex : RhoAlignedViewsPlanStopApexInDomain declarationColor)
    (collapsingRestoration :
      RhoCollapsingViewsRestorationAlignedInDomain declarationColor)
    (exposure : RhoCollapsingLeafExposureInDomain declarationColor) :
    RhoCanonicalStaticPairSemanticCutProviderInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical _staticShape closeSmaller
    left right rootCase
  have close : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) := closeSmaller
  have closeSwapped : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf rightPattern + sizeOf leftPattern) := by
    rw [Nat.add_comm]; exact close
  cases rootCase with
  | leftCollapsing leftColor leftView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_leftCollapsing_of_restorationRoutes
          leftView collapsing
          (fun rightView =>
            collapsingRestoration leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inl collapsing) canonical)
          (fun rightStructural =>
            exposure leftView admissible leftWellSorted rightWellSorted close
              collapsing rightStructural canonical)
  | rightCollapsing rightColor rightView collapsing =>
      exact
        nonempty_rhoCanonicalStaticPairSemanticCut_rightCollapsing_of_restorationRoutes
          rightView collapsing
          (fun leftView =>
            collapsingRestoration leftView rightView admissible leftWellSorted
              rightWellSorted close (Or.inr collapsing) canonical)
          (fun leftStructural =>
            exposure rightView admissible rightWellSorted leftWellSorted
              closeSwapped collapsing leftStructural canonical.symm)
  | aligned color leftView rightView roots =>
      exact ⟨rhoCanonicalStaticPairSemanticCut_aligned_of_planStopApex
        leftView rightView roots
        (alignedApex leftView rightView admissible leftWellSorted
          rightWellSorted close roots)⟩

/-- **The rho Cost₁ domain object over the apex-form obligations.**

The operative seal statement.  Discharging A1′, A2 and B produces
`CostOneDomainObject` with no remaining hypotheses. -/
noncomputable def rhoHereditaryCostOneDomainObject_ofApexObligations
    (alignedApex : ∀ color, RhoAlignedViewsPlanStopApexInDomain color)
    (collapsingRestoration :
      ∀ color, RhoCollapsingViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeafExposureInDomain color) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexObligations
        (alignedApex color) (collapsingRestoration color) (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

/-- The Cost₁ object laws over the apex-form obligations. -/
noncomputable def rhoHereditaryCostOneObjectLaws_ofApexObligations
    (alignedApex : ∀ color, RhoAlignedViewsPlanStopApexInDomain color)
    (collapsingRestoration :
      ∀ color, RhoCollapsingViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeafExposureInDomain color) :
    CIGSLT.CostOneObjectLawsFor rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCostOneObjectLaws_ofSemanticLaws
    (fun color =>
      rhoCanonicalStaticPairSemanticCutProviderInDomain_of_apexObligations
        (alignedApex color) (collapsingRestoration color) (exposure color))
    rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
