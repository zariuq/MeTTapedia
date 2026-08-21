import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

/-!
# Residual switchboard of the rho plan-stop apex

`RhoStaticNonBoundaryPlanStopCommonApex.AfterSameColorBoundarySide` is what
remains of the plan-stop obligation after the certified-boundary quadrant,
every delegated same-colour canonical leaf, the same-colour Quote terminal,
and every same-colour stop with one certified-boundary side have been
consumed.  Its name suggests two live halves, one per declaration colour.
Only one of them is live.

The generated Cost declarations do not rename collection types: both colour
images of the authored reflective presentation carry the *same* parallel
collection (`costStaticReflectivePresentationDecl_parallelCollection`).  A
bare parallel root is therefore the declaration's own parallel collection at
every colour, and the retained raw alignment has no structural constructor
there: `CanonicalStopAligned.collection` is explicitly guarded against the
declaration's parallel collection, and `collectionRest` needs an open tail
that plan admission forbids.  Only the delegated leaf remains, which the
residual's own retained disjunction excludes.

Consequences, all checked below:

* `not_parallelPair_nonDelegated` — a non-delegated bare-parallel reached-root
  pair does not exist, at either declaration colour;
* `not_sameColorResidual` — the same-colour half of the residual has
  contradictory hypotheses, since `sameColor_parallelRoots_of_residual` forces
  exactly that shape;
* `afterSameColorBoundarySide_of_foreign` — the residual is therefore carried
  entirely by its foreign-colour half.

`rawStop_of_leftParallelRoot` and `rawStop_of_rightParallelRoot` record what
survives on the foreign side, where the delegated leaf is *not* excluded: a
bare parallel root on either endpoint forces the retained raw stop, whose
second component is the strict payload descent below the parent measure.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- A plan whose root class is an ordinary collection has a collection root
pattern of exactly that collection type. -/
theorem CostStaticRegionPlan.collectionRoot_of_rootClass
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    {collectionType : CollType}
    (rootClass : plan.rootClass = .collection collectionType) :
    ∃ elements rest, pattern = .collection collectionType elements rest := by
  cases plan <;>
    simp only [CostStaticRegionPlan.rootClass, reduceCtorEq,
      CostStaticPlanRootClass.collection.injEq] at rootClass
  subst rootClass
  exact ⟨_, _, rfl⟩

/-- A collection plan root carrying raw admission has no open collection
tail. -/
theorem CostStaticRegionPlan.RawAdmission.collectionRest_eq_none
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {collectionType : CollType} {elements : List Pattern}
    {rest : Option String} {sourceType : TypeExpr}
    {plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer
      (.collection collectionType elements rest) sourceType}
    (admission : plan.RawAdmission) :
    rest = none := by
  have objectRoot : WellSorted.isObjectPattern
      (.collection collectionType elements rest) = true :=
    admission.wellSorted.1.2.2.1
  simp only [WellSorted.isObjectPattern, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at objectRoot
  exact objectRoot.1

end Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode
open ReflectionExtension

/-- Cost colouring renames constructors, not collection types: both generated
declarations retain the authored parallel collection.  A bare parallel root is
therefore the parallel collection of *every* generated declaration, not only
of the one that produced it. -/
theorem costStaticReflectivePresentationDecl_parallelCollection
    (color : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation).parallelCollection =
      rhoReflectivePresentation.parallelCollection := by
  cases color <;> rfl

namespace RhoStaticNonBoundaryPlanStopCommonApex

/-- A retained raw alignment of two bare parallel roots is necessarily the
delegated leaf.

The structural collection constructor is guarded against the declaration's own
parallel collection, and by
`costStaticReflectivePresentationDecl_parallelCollection` that guard fires at
both colours.  So a pair of bare parallel roots cannot be aligned
structurally, and excluding the delegated leaf leaves nothing. -/
theorem not_parallelPair_nonDelegated
    {declarationColor : CostStaticColor} {parentMeasure : Nat}
    {leftElements rightElements : List Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      (.collection rhoReflectivePresentation.parallelCollection leftElements
        none)
      (.collection rhoReflectivePresentation.parallelCollection rightElements
        none))
    (notDelegated : ¬ ∃ stopped,
      rawAligned = CanonicalStopAligned.leaf stopped) :
    False := by
  cases rawAligned with
  | leaf given => exact notDelegated ⟨given, rfl⟩
  | collection ne elements =>
      exact ne
        (costStaticReflectivePresentationDecl_parallelCollection
          declarationColor).symm

/-- A bare parallel root on the left endpoint forces the retained raw stop.

Its second component is the strict payload descent below the parent measure,
so this is the descent certificate available on the foreign side, where the
delegated leaf is not excluded. -/
theorem rawStop_of_leftParallelRoot
    {declarationColor : CostStaticColor} {parentMeasure : Nat}
    {leftElements : List Pattern} {rightPayload : Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      (.collection rhoReflectivePresentation.parallelCollection leftElements
        none)
      rightPayload) :
    RhoCanonicalRawStop declarationColor parentMeasure
      (.collection rhoReflectivePresentation.parallelCollection leftElements
        none)
      rightPayload := by
  cases rawAligned with
  | leaf given => exact given
  | collection ne elements =>
      exact absurd
        (costStaticReflectivePresentationDecl_parallelCollection
          declarationColor).symm ne

/-- A bare parallel root on the right endpoint forces the retained raw
stop. -/
theorem rawStop_of_rightParallelRoot
    {declarationColor : CostStaticColor} {parentMeasure : Nat}
    {leftPayload : Pattern} {rightElements : List Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure)
      leftPayload
      (.collection rhoReflectivePresentation.parallelCollection rightElements
        none)) :
    RhoCanonicalRawStop declarationColor parentMeasure leftPayload
      (.collection rhoReflectivePresentation.parallelCollection rightElements
        none) := by
  cases rawAligned with
  | leaf given => exact given
  | collection ne elements =>
      exact absurd
        (costStaticReflectivePresentationDecl_parallelCollection
          declarationColor).symm ne

/-- The same-colour half of the residual switchboard is empty.

`sameColor_parallelRoots_of_residual` forces both reached roots to be bare
parallel, plan admission removes the open collection tail, and
`not_parallelPair_nonDelegated` then contradicts the retained non-delegation
disjunct. -/
theorem not_sameColorResidual
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    {parentMeasure : Nat}
    (stopReason : RhoCanonicalRawStop color parentMeasure leftPayload
        rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation)
      (RhoCanonicalRawStop color parentMeasure) leftPayload rightPayload)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary))
    (notDelegated : ¬ ∃ stopped,
      rawAligned = CanonicalStopAligned.leaf stopped)
    (notQuote : leftReached.plan.rootClass ≠
        .application rhoReflectivePresentation.quoteConstructor ∨
      rightReached.plan.rootClass ≠
        .application rhoReflectivePresentation.quoteConstructor)
    (neitherBoundary :
      ¬ leftReached.plan.rootClass.IsCertifiedBoundary ∧
        ¬ rightReached.plan.rootClass.IsCertifiedBoundary) :
    False := by
  have parallelRoots := sameColor_parallelRoots_of_residual leftReached
    rightReached stopReason rawAligned notBothBoundary notDelegated notQuote
    neitherBoundary
  obtain ⟨leftElements, leftRest, leftShape⟩ :=
    CostStaticRegionPlan.collectionRoot_of_rootClass leftReached.plan
      parallelRoots.1
  obtain ⟨rightElements, rightRest, rightShape⟩ :=
    CostStaticRegionPlan.collectionRoot_of_rootClass rightReached.plan
      parallelRoots.2
  subst leftShape
  subst rightShape
  have leftRestNone :=
    CostStaticRegionPlan.RawAdmission.collectionRest_eq_none leftAdmission
  have rightRestNone :=
    CostStaticRegionPlan.RawAdmission.collectionRest_eq_none rightAdmission
  subst leftRestNone
  subst rightRestNone
  exact not_parallelPair_nonDelegated rawAligned notDelegated

/-- The foreign-colour half of the residual switchboard.

Each of the three disjunctions retained by `AfterSameColorBoundarySide` is
discharged by its left disjunct once the declaration colour differs from the
plan colour, so this is exactly that residual with the three carrying no
information. -/
def AfterSameColorBoundarySideForeign
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
    (declarationColor : CostStaticColor) : Prop :=
  let rawDeclaration := costStaticReflectivePresentationDecl rhoCIGSLT
    declarationColor rhoReflectivePresentation
  let rawStop := RhoCanonicalRawStop declarationColor
    (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1)
  declarationColor ≠ color →
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
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary)),
    RhoReachedPlanPairCommonApex leftView rightView callbackAvailable
      callbackScope callbackRoot leftAbstract rightAbstract

/-- The residual switchboard is carried entirely by its foreign-colour half.

The same-colour branch is discharged, not assumed: it is refuted by
`not_sameColorResidual`. -/
theorem afterSameColorBoundarySide_of_foreign
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
    (foreign : AfterSameColorBoundarySideForeign leftView rightView
      declarationColor) :
    AfterSameColorBoundarySide leftView rightView declarationColor := by
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    leftPayload rightPayload leftReached rightReached leftAdmission
    rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq
    sourceBoundEq targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute
    rightRoute stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned
    notBothBoundary afterAligned afterQuote afterBoundary
  by_cases sameColor : declarationColor = color
  · subst declarationColor
    have notDelegated : ¬ ∃ stopped,
        rawAligned = CanonicalStopAligned.leaf stopped := by
      rcases afterAligned with different | given
      · exact (different rfl).elim
      · exact given
    have notQuote : leftReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor ∨
        rightReached.plan.rootClass ≠
          .application rhoReflectivePresentation.quoteConstructor := by
      rcases afterQuote with different | given
      · exact (different rfl).elim
      · exact given
    have neitherBoundary :
        ¬ leftReached.plan.rootClass.IsCertifiedBoundary ∧
          ¬ rightReached.plan.rootClass.IsCertifiedBoundary := by
      rcases afterBoundary with different | given
      · exact (different rfl).elim
      · exact given
    exact (not_sameColorResidual leftReached rightReached leftAdmission
      rightAdmission stopReason rawAligned notBothBoundary notDelegated
      notQuote neitherBoundary).elim
  · exact foreign sameColor callbackAvailable callbackScope callbackRoot
      leftReached rightReached leftAdmission rightAdmission leftAbstractEq
      rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq
      thinningEq leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary

end RhoStaticNonBoundaryPlanStopCommonApex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
