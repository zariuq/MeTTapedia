import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace FablePrototype

/-- The parent-polymorphic semantic action retained by a recursively closed
pair. The recursive pair fixes only payloads, their visible availability, and
their target type. A caller later supplies the exact parent views, cospan,
reached plans, and requested restoration depth. -/
def RhoReachedPlanPairApexAction
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (childAvailable : List TypeExpr) (leftPayload rightPayload : Pattern)
    (childType : TypeExpr) : Prop :=
  ∀ {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
        type}
      (leftView : left.StaticRootView declarationColor)
      (rightView : right.StaticRootView declarationColor)
      (callbackAvailable callbackScope callbackRoot : Nat)
      {leftAbstract rightAbstract : Pattern}
      (leftReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree leftPayload leftView.node.plan.abstractPattern)
      (rightReached : CostStaticPlanReached rhoCIGSLT declarationColor
        targetFree rightPayload rightView.node.plan.abstractPattern)
      (_leftAdmission : leftReached.plan.RawAdmission)
      (_rightAdmission : rightReached.plan.RawAdmission)
      (_leftAbstractEq : leftReached.plan.abstractPattern = leftAbstract)
      (_rightAbstractEq : rightReached.plan.abstractPattern = rightAbstract)
      (_leftAvailableEq : leftReached.sourceAvailable = childAvailable)
      (_rightAvailableEq : rightReached.sourceAvailable = childAvailable)
      (_leftTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType = childType)
      (_rightTypeEq :
        mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType = childType)
      (_sourceTypeEq : leftReached.sourceType = rightReached.sourceType)
      (_sourceBoundEq : leftReached.sourceBound = rightReached.sourceBound)
      (_targetBoundEq : leftReached.targetBound = rightReached.targetBound)
      (_thinningEq : HEq leftReached.thinning rightReached.thinning)
      (_leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree leftReached.plan.boundaryTable.entries
        leftView.node.plan.boundaryTable.entries))
      (_rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT
        declarationColor targetFree rightReached.plan.boundaryTable.entries
        rightView.node.plan.boundaryTable.entries))
      (_leftRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base leftView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          leftReached.sourceType)))
      (_rightRoute : Nonempty (CostCanonicalTypeRoute rhoCIGSLT
        declarationColor
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          (.base rightView.node.sourceSort.1))
        (mapTypeExpr (declarationColor.symbols rhoCIGSLT)
          rightReached.sourceType))),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- Recursive closure retains the ordinary pair for generic consumers and the
strictly stronger, parent-polymorphic reached-plan semantic action. -/
structure RhoCanonicalPairRecursiveResult
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (available outer : List TypeExpr) (leftPattern rightPattern : Pattern)
    (type : TypeExpr) : Type where
  pair : CostCanonicalPairElaboration rhoCIGSLT
    rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type
  reachedApex : @RhoReachedPlanPairApexAction declarationColor targetFree
    available leftPattern rightPattern type

/-- One syntax-directed layer for the richer recursive result. Every recursive
call is constrained by the same symmetric size measure as the existing Cost
pair elaborator. -/
def RhoCanonicalPairRecursiveStep (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
      {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern →
    (∀ {childAvailable childOuter : List TypeExpr}
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
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
        childAvailable childOuter leftChild rightChild childType)) →
    Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
      available outer leftPattern rightPattern type)

/-- The richer step closes by the same well-founded measure as the existing
pair elaborator. Parent cospan parameters are absent from the measure and live
only in `reachedApex`, where a smaller result is instantiated. -/
noncomputable def RhoCanonicalPairRecursiveResult.nonempty_of_step
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairRecursiveStep declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern) :
    Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
      available outer leftPattern rightPattern type) := by
  apply step (targetFree := targetFree) admissible leftWellSorted
    rightWellSorted canonical
  intro childAvailable childOuter leftChild rightChild childType
    leftChildWellSorted rightChildWellSorted childCanonical smaller
    childAdmissible
  exact RhoCanonicalPairRecursiveResult.nonempty_of_step step childAdmissible
    leftChildWellSorted rightChildWellSorted childCanonical
termination_by sizeOf leftPattern + sizeOf rightPattern

/-- The actual same-colour raw-stop use: once the strictly smaller recursive
call returns the richer carrier for the two reached payloads, instantiate its
parent-polymorphic action at the current static-frame cospan. No elaboration is
inverted and no apex is reconstructed from an erased pair. -/
theorem RhoCanonicalPairRecursiveResult.reachedApex_sameColor
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (callbackAvailable callbackScope callbackRoot : Nat)
    {leftPayload rightPayload leftAbstract rightAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftView.node.plan.abstractPattern)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightView.node.plan.abstractPattern)
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
    (result : @RhoCanonicalPairRecursiveResult color targetFree
      leftReached.sourceAvailable [] leftPayload rightPayload
      (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)) :
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract := by
  exact result.reachedApex leftView rightView callbackAvailable callbackScope
    callbackRoot leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq rfl sourceAvailableEq.symm rfl
    (congrArg (mapTypeExpr (color.symbols rhoCIGSLT)) sourceTypeEq.symm)
    sourceTypeEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute

end FablePrototype

/-- The residual switchboard after the same-colour Quote/Quote arm has been
removed.  Foreign-colour Quote descent, mixed boundary/source collections,
parallel permutation, and non-Quote delegated stops remain explicit here. -/
def RhoStaticNonBoundaryPlanStopCommonApex.AfterSameColorQuotes
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
  ∀ callbackAvailable callbackScope callbackRoot
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
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_remaining : declarationColor ≠ color ∨
        leftReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor ∨
        rightReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- Consume the richer well-founded recursive result in the actual
same-colour Quote/Quote stop and delegate exactly the residual cases. -/
noncomputable def
    RhoStaticNonBoundaryPlanStopCommonApex.of_recursiveSameColorQuotes
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
    (stopCollapsing : ∀ {left right}, rawStop left right →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (stopSmaller : ∀ {left right}, rawStop left right →
      sizeOf left + sizeOf right <
        sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
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
      Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
        childAvailable childOuter leftChild rightChild childType))
    (remaining : AfterSameColorQuotes leftView rightView declarationColor
      rawStop) :
    RhoStaticNonBoundaryPlanStopCommonApex leftView rightView declarationColor
      rawStop := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    leftPayload rightPayload leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute stopReason rawAligned notBothBoundary
  by_cases sameColor : declarationColor = color
  · subst declarationColor
    by_cases leftQuote : leftReached.plan.rootClass =
        .application rhoReflectivePresentation.quoteConstructor
    · by_cases rightQuote : rightReached.plan.rootClass =
          .application rhoReflectivePresentation.quoteConstructor
      · rcases CanonicalStopAligned.reached_sourceQuotes_cases leftReached
            rightReached leftQuote rightQuote stopCollapsing rawAligned with
          same | foreign
        · have stopped : rawStop leftPayload rightPayload := same.2
          have rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
              rhoCIGSLT.costWholeReflectionProfile
              rhoCIGSLT.costWholeLanguage targetFree
              leftReached.sourceAvailable
              (mapTypeExpr (color.symbols rhoCIGSLT) leftReached.sourceType)
              rightPayload := by
            simpa only [sourceAvailableEq, sourceTypeEq] using
              rightAdmission.wellSorted
          obtain ⟨rightRoute⟩ := rightRoute
          have childAdmissible :=
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalTypeRoute.rho_admissible
              rightRoute rightRootAdmissible
          have childAdmissible' : rhoCanonicalRecursiveTypeDomain.Admissible
              (mapTypeExpr (color.symbols rhoCIGSLT)
                leftReached.sourceType) := by
            simpa only [sourceTypeEq] using childAdmissible
          obtain ⟨child⟩ := closeSmaller (childOuter := [])
            leftAdmission.wellSorted rightWellSorted
            (stopCanonical stopped) (stopSmaller stopped) childAdmissible'
          exact child.reachedApex_sameColor leftView rightView
            callbackAvailable callbackScope callbackRoot leftReached
            rightReached leftAdmission rightAdmission leftAbstractEq
            rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
            targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
            ⟨rightRoute⟩
        · exact False.elim (CostStaticColor.ne_flip color foreign.1)
      · exact remaining callbackAvailable callbackScope callbackRoot
          leftReached rightReached leftAdmission rightAdmission leftAbstractEq
          rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
          targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
          rightRoute stopReason rawAligned notBothBoundary
          (Or.inr (Or.inr rightQuote))
    · exact remaining callbackAvailable callbackScope callbackRoot
        leftReached rightReached leftAdmission rightAdmission leftAbstractEq
        rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
        targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
        rightRoute stopReason rawAligned notBothBoundary
        (Or.inr (Or.inl leftQuote))
  · exact remaining callbackAvailable callbackScope callbackRoot leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason rawAligned
      notBothBoundary (Or.inl sameColor)

/-- Specialization to the raw stop emitted by canonical root descent.  This is
the source-ready switchboard call: the three raw-stop projections are wired
here once, rather than being reproved at every provider site. -/
noncomputable def
    RhoStaticNonBoundaryPlanStopCommonApex.of_recursiveSameColorQuotesForCanonicalStop
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
    (rightRootAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)))
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
      Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
        childAvailable childOuter leftChild rightChild childType))
    (remaining :
      let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
        declarationColor rhoReflectivePresentation
      let rawStop := fun candidateLeft candidateRight =>
        ((CollapsingRoot declaration candidateLeft ∨
            CollapsingRoot declaration candidateRight) ∧
          canonicalize declaration candidateLeft =
            canonicalize declaration candidateRight) ∧
        sizeOf candidateLeft + sizeOf candidateRight <
          sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1
      AfterSameColorQuotes leftView rightView declarationColor rawStop) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT
      declarationColor rhoReflectivePresentation
    let rawStop := fun candidateLeft candidateRight =>
      ((CollapsingRoot declaration candidateLeft ∨
          CollapsingRoot declaration candidateRight) ∧
        canonicalize declaration candidateLeft =
          canonicalize declaration candidateRight) ∧
      sizeOf candidateLeft + sizeOf candidateRight <
        sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1
    RhoStaticNonBoundaryPlanStopCommonApex leftView rightView declarationColor
      rawStop := by
  dsimp only
  apply of_recursiveSameColorQuotes leftView rightView declarationColor
    rightRootAdmissible
  · intro left right stopped
    exact stopped.1.2
  · intro left right stopped
    exact stopped.1.1
  · intro left right stopped
    exact stopped.2
  · exact closeSmaller
  · exact remaining

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
