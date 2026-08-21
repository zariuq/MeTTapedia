import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryNonBoundaryPlanStop

/-!
# The Quote and bare-parallel cells of the non-boundary plan-stop residual

`RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells` reconstructs the
whole residual from four reached-root families.  This module works on three
of them — the bare-parallel side, the paired authored Quote, and the
single same-colour Quote side — and establishes what they have in common.

Everything is stated for an arbitrary stop relation `rawStop`, because the
lane instantiates the residual at two different measures (`A1` at
`sizeOf leftPattern + sizeOf rightPattern`, `A2` at that plus one).

## What is established here

* `rho_rawStop_of_ownColorQuoteLeftPayload` / `..._rightPayload` — a payload
  headed by the canonicalizing declaration's *own* Quote constructor admits
  no structural constructor of `CanonicalStopAligned`, so the stop is
  delegated.  This is the Quote analogue of
  `rho_rawStop_of_leftParallelPayload`, and it needs no admission hypothesis:
  `CanonicalStopAligned.apply` is guarded against the declaration's quote
  constructor outright.

* `rho_planStop_rawStop_of_sameColorQuoteSide` — family 4's entry: at the
  declaration's own colour a single authored Quote endpoint forces the
  delegated stop, for any stop relation.

* `RhoPlanStopQuotePairCell.toSameColorQuoteSideCell` — the paired Quote
  terminal at the declaration's own colour is *literally a sub-cell* of
  family 4.  Consequently family 3 splits into family 4 and its foreign
  half alone (`RhoStaticNonBoundaryPlanStopSourceAlignedOn.quotePair_of_halves`),
  and no separate same-colour paired-Quote argument is required.

* `RhoPlanStopDelegatedCell` and `rho_planStop_rawStop_of_delegatedCell` —
  families 2 and 4 (hence the same-colour half of family 3) share one entry:
  the delegated stop is forced.

* The budget those two families consume, which is the delegated stop's own
  second component and therefore **measure-sensitive**.
  `rho_planStop_delegatedCell_size_lt` gives a strict descent below the stop
  measure; at A2's measure that is one above the endpoint pair, so
  `rho_planStop_delegatedCell_size_le_at_succ` gives only `≤` against the
  endpoint pair, and
  `rhoCanonicalRawStop_endpoints_at_succ_and_not_at_endpointMeasure` shows
  that weakening is sharp: the endpoint pair itself is a stop at A2's measure
  and a stop at no measure taken at itself.  Since both obligations carry
  `RhoPairCloseSmaller` at the *endpoint* measure, the callback covers every
  delegated payload pair of A1's instance and no more than the proper
  sub-pairs of A2's.

* `RhoPlanStopDelegatedSourceLeaf` — the residual content those two families
  share, stated over the delegated payload pair with the reached-root cell
  discarded and every other hypothesis of the residual retained;
  `RhoStaticNonBoundaryPlanStopSourceAlignedOn.of_delegated` and its two
  specializations produce both families from it.

* `RhoPlanStopForeignQuotePairCell` and
  `rho_planStop_foreignQuotePair_arguments` — the remaining half of family 3:
  at a foreign colour both payloads are generated Quotes of the *plan's*
  colour whose argument lists are aligned structurally.
  `RhoPlanStopForeignQuotePairSourceLeaf` resolves that half's stop-reason
  disjunction, since its delegated branch is already family 2/4 content.

* `RhoStaticNonBoundaryPlanStopSourceAligned.of_boundarySide_and_stops` —
  the net effect: where `of_liveCells` asks for four family residuals, the
  residual now follows from the certified-boundary family together with
  exactly two statements about stops.

## What is *not* established here

`RhoPlanStopDelegatedSourceLeaf` and `RhoPlanStopForeignQuotePairSourceLeaf`
are not discharged.  Both ask for a `PatternLeafAligned` between two whole
`canonicalizeByDepths` frames, and in both the reached abstractions are the
plan's own root shape — `Pattern.collection` at the authored parallel
collection, or `Pattern.apply` at the authored Quote — never a single
`Pattern.fvar`.  Two independent things are missing.

First, the recursion these obligations carry is `RhoPairCloseSmaller`, whose
value is a `CostCanonicalPairElaboration`.  Every route from a pair
elaboration to restoration evidence in the lane is gated on a certified
boundary occurrence, so none of them accepts an arbitrary reached payload
pair.  The apex lane meets the same configuration and closes it only by
carrying a strictly richer callback, whose value additionally supplies the
reached-plan apex action.

Second, the leaf relation quantifies the ambient reinsertion depth
independently of the canonicalization scope depth, whereas every apex
producer pins the two together and the naturality squares
`thickenAmbientBVars_canonicalizeByDepths` and
`mapThicken_canonicalizeByDepths` hold only on that diagonal;
`CommonRestorationApex.restoresTogether_of_forall_apex` then recovers the
depth family only for an already fixed pair.  The certified-boundary
producers escape this because ambient reinsertion is the identity on a free
variable, which is exactly the escape unavailable here.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-! ## The Quote endpoint at the declaration's own colour -/

/-- A left payload headed by the canonicalizing declaration's own Quote
constructor forces the delegated stop, for any stop relation.

`CanonicalStopAligned.apply` is explicitly guarded against the declaration's
quote constructor, and every other structural constructor fixes a different
root, so `leaf` is the only inhabitant. -/
theorem rho_rawStop_of_ownColorQuoteLeftPayload
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    {leftArguments : List Pattern} {rightPayload : Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor leftArguments)
      rightPayload) :
    rawStop
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor leftArguments)
      rightPayload := by
  cases rawAligned with
  | leaf given => exact given
  | apply ne arguments => exact absurd rfl ne

/-- Right-endpoint companion of
`rho_rawStop_of_ownColorQuoteLeftPayload`. -/
theorem rho_rawStop_of_ownColorQuoteRightPayload
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    {leftPayload : Pattern} {rightArguments : List Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor rightArguments)) :
    rawStop leftPayload
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation).quoteConstructor rightArguments) := by
  cases rawAligned with
  | leaf given => exact given
  | apply ne arguments => exact absurd rfl ne

/-- **In the same-colour Quote-side family the delegated stop is forced**, for
any stop relation.  This is family 4's entry, and unlike family 2's it
consumes no plan admission. -/
theorem rho_planStop_rawStop_of_sameColorQuoteSide
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (quoteSide : RhoPlanStopSameColorQuoteSideCell declarationColor color
      leftReached.plan.rootClass rightReached.plan.rootClass) :
    rawStop leftPayload rightPayload := by
  obtain ⟨colorEq, side⟩ := quoteSide
  subst colorEq
  rcases side with leftQuote | rightQuote
  · obtain ⟨leftArguments, leftShape⟩ :=
      CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote leftReached
        leftQuote
    subst leftShape
    exact rho_rawStop_of_ownColorQuoteLeftPayload rawAligned
  · obtain ⟨rightArguments, rightShape⟩ :=
      CostStaticPlanReached.payload_eq_generatedQuote_of_sourceQuote
        rightReached rightQuote
    subst rightShape
    exact rho_rawStop_of_ownColorQuoteRightPayload rawAligned

/-! ## The paired Quote terminal is not an independent family -/

/-- At the declaration's own colour the paired Quote terminal is a sub-cell of
the single-Quote-side family. -/
theorem RhoPlanStopQuotePairCell.toSameColorQuoteSideCell
    {declarationColor color : CostStaticColor}
    {leftClass rightClass : CostStaticPlanRootClass}
    (sameColor : declarationColor = color)
    (quotePair : RhoPlanStopQuotePairCell leftClass rightClass) :
    RhoPlanStopSameColorQuoteSideCell declarationColor color leftClass
      rightClass :=
  ⟨sameColor, Or.inl quotePair.1⟩

/-- The foreign half of the paired Quote terminal: the cell together with the
colour separation that makes it irreducible to family 4. -/
def RhoPlanStopForeignQuotePairCell (declarationColor color : CostStaticColor)
    (leftClass rightClass : CostStaticPlanRootClass) : Prop :=
  declarationColor ≠ color ∧ RhoPlanStopQuotePairCell leftClass rightClass

/-- **Family 3 from family 4 and the foreign paired terminal alone.**

No same-colour paired-Quote argument is needed anywhere: at the declaration's
own colour the paired cell is already a single-Quote-side cell. -/
theorem RhoStaticNonBoundaryPlanStopSourceAlignedOn.quotePair_of_halves
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    (sameColorQuoteSide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop
      (RhoPlanStopSameColorQuoteSideCell declarationColor color))
    (foreignQuotePair : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop
      (RhoPlanStopForeignQuotePairCell declarationColor color)) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop RhoPlanStopQuotePairCell := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    quotePair
  by_cases sameColor : declarationColor = color
  · exact sameColorQuoteSide callbackAvailable callbackScope leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      (quotePair.toSameColorQuoteSideCell sameColor)
  · exact foreignQuotePair callbackAvailable callbackScope leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      ⟨sameColor, quotePair⟩

/-! ## Families 2 and 4 share one entry -/

/-- The union of family 2 and family 4: exactly the reached-root cells whose
stop is delegated to `rawStop`. -/
def RhoPlanStopDelegatedCell (declarationColor color : CostStaticColor)
    (leftClass rightClass : CostStaticPlanRootClass) : Prop :=
  RhoPlanStopParallelSideCell leftClass rightClass ∨
    RhoPlanStopSameColorQuoteSideCell declarationColor color leftClass
      rightClass

/-- **The delegated stop is forced on the whole union**, for any stop
relation. -/
theorem rho_planStop_rawStop_of_delegatedCell
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (cell : RhoPlanStopDelegatedCell declarationColor color
      leftReached.plan.rootClass rightReached.plan.rootClass) :
    rawStop leftPayload rightPayload := by
  rcases cell with parallel | quoteSide
  · exact rho_planStop_rawStop_of_parallelSide leftReached rightReached
      leftAdmission rightAdmission rawAligned parallel
  · exact rho_planStop_rawStop_of_sameColorQuoteSide leftReached rightReached
      rawAligned quoteSide

/-- **The single budget both families consume.**

It is the delegated stop's own second component, so it is one weaker at A2's
measure than at A1's: at A1 the payload pair is strictly below
`sizeOf leftPattern + sizeOf rightPattern`, at A2 only weakly below it. -/
theorem rho_planStop_delegatedCell_size_lt
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor parentMeasure) leftPayload
      rightPayload)
    (cell : RhoPlanStopDelegatedCell declarationColor color
      leftReached.plan.rootClass rightReached.plan.rootClass) :
    sizeOf leftPayload + sizeOf rightPayload < parentMeasure :=
  (rho_planStop_rawStop_of_delegatedCell leftReached rightReached leftAdmission
    rightAdmission rawAligned cell).2

/-- **The same budget at A2's measure**, where it degrades to a weak
inequality against the endpoint pair.

A1 runs at `parentMeasure = sizeOf leftPattern + sizeOf rightPattern` and gets
a strict descent below it; A2 runs one above and gets only `≤`.  The
recursion callback `RhoPairCloseSmaller` both obligations carry is measured at
`sizeOf leftPattern + sizeOf rightPattern` in both cases, so it applies to
every delegated payload pair of A1's instance and to no more than the proper
sub-pairs of A2's. -/
theorem rho_planStop_delegatedCell_size_le_at_succ
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftAdmission : leftReached.plan.RawAdmission)
    (rightAdmission : rightReached.plan.RawAdmission)
    {parentMeasure : Nat}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      (RhoCanonicalRawStop declarationColor (parentMeasure + 1)) leftPayload
      rightPayload)
    (cell : RhoPlanStopDelegatedCell declarationColor color
      leftReached.plan.rootClass rightReached.plan.rootClass) :
    sizeOf leftPayload + sizeOf rightPayload ≤ parentMeasure :=
  Nat.lt_succ_iff.mp
    (rho_planStop_delegatedCell_size_lt leftReached rightReached leftAdmission
      rightAdmission rawAligned cell)

/-- **The weak inequality above cannot be strengthened.**

The endpoint pair of a collapsing arm *is* a delegated stop at A2's measure
and is outside every raw stop relation measured at itself, so a delegated
cell of A2's instance genuinely may carry the endpoint pair — at which point
the recursion callback, measured at the endpoint pair, has nothing to
offer. -/
theorem rhoCanonicalRawStop_endpoints_at_succ_and_not_at_endpointMeasure
    {declarationColor : CostStaticColor} {leftPattern rightPattern : Pattern}
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      leftPattern)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightPattern) :
    RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern + 1) leftPattern
        rightPattern ∧
      ¬ RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern) leftPattern rightPattern :=
  ⟨rhoCanonicalRawStop_endpoints_of_leftCollapsing collapsing canonical,
    not_rhoCanonicalRawStop_endpoints_at_endpointMeasure⟩

/-! ## The residual content shared by families 2 and 4 -/

/-- The residual restricted to *delegated* stops: the telescope of
`RhoStaticNonBoundaryPlanStopSourceAlignedOn` with the stop-reason
disjunction and the reached-root cell both replaced by the delegated stop
itself.  Every other hypothesis of the residual is retained, so this is the
weakest statement that carries the two families.

This is what families 2 and 4 have in common, and by
`RhoPlanStopQuotePairCell.toSameColorQuoteSideCell` it also carries the
same-colour half of family 3. -/
def RhoPlanStopDelegatedSourceLeaf
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
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_notBothBoundary :
        ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_delegated : rawStop leftPayload rightPayload),
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

/-- **Families 2 and 4 from the delegated obligation alone.**

The reached-root cell is used only to force the delegated stop; every other
hypothesis is passed through unchanged. -/
theorem RhoStaticNonBoundaryPlanStopSourceAlignedOn.of_delegated
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor rawStop) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop
      (RhoPlanStopDelegatedCell declarationColor color) := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  exact delegated callbackAvailable callbackScope leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute leftPayloadSizeLe rightPayloadSizeLe
    rawAligned notBothBoundary
    (rho_planStop_rawStop_of_delegatedCell leftReached rightReached
      leftAdmission rightAdmission rawAligned cell)

/-- Family 2 from the delegated obligation. -/
theorem RhoStaticNonBoundaryPlanStopSourceAlignedOn.parallelSide_of_delegated
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor rawStop) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop RhoPlanStopParallelSideCell :=
  (RhoStaticNonBoundaryPlanStopSourceAlignedOn.of_delegated
      (color := color) delegated).mono
    (fun _ _ parallel => Or.inl parallel)

/-- Family 4 from the delegated obligation. -/
theorem
    RhoStaticNonBoundaryPlanStopSourceAlignedOn.sameColorQuoteSide_of_delegated
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor rawStop) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop
      (RhoPlanStopSameColorQuoteSideCell declarationColor color) :=
  (RhoStaticNonBoundaryPlanStopSourceAlignedOn.of_delegated
      (color := color) delegated).mono
    (fun _ _ quoteSide => Or.inr quoteSide)

/-! ## The foreign half of the paired Quote terminal -/

/-- The shape retained by the foreign half of family 3: two generated Quotes
of the *plan's* colour, whose argument lists are aligned by the raw
descent. -/
theorem rho_planStop_foreignQuotePair_arguments
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {rawStop : Pattern → Pattern → Prop}
    (stopCollapsing : ∀ {left right}, rawStop left right →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload rightPayload)
    (cell : RhoPlanStopForeignQuotePairCell declarationColor color
      leftReached.plan.rootClass rightReached.plan.rootClass) :
    declarationColor = color.flip ∧
      ∃ leftArguments rightArguments,
        leftPayload = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor leftArguments ∧
        rightPayload = .apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation).quoteConstructor rightArguments ∧
        CanonicalStopAlignedList
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          rawStop leftArguments rightArguments := by
  obtain ⟨foreign, quotePair⟩ := cell
  rcases rho_planStop_quotePair_cases leftReached rightReached stopCollapsing
      rawAligned quotePair with ⟨sameColor, _⟩ | foreignCase
  · exact absurd sameColor foreign
  · exact foreignCase

/-- The residual restricted to a *structurally eligible* foreign paired Quote
stop: the telescope of `RhoStaticNonBoundaryPlanStopSourceAlignedOn` with the
stop-reason disjunction resolved to its structural half and the cell replaced
by the colour separation together with the paired Quote classes.

Splitting the reason is not cosmetic.  A foreign paired Quote whose reason is
the *delegated* stop is already carried by `RhoPlanStopDelegatedSourceLeaf`;
what is left here is exactly the configuration for which the raw descent is
`CanonicalStopAligned.apply`, so that
`rho_planStop_foreignQuotePair_arguments` supplies an argument-list
alignment. -/
def RhoPlanStopForeignQuotePairSourceLeaf
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
      (_eligible : CostStaticPlanStopEligible rhoReflectivePresentation
        leftReached.plan rightReached.plan)
      (_leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftView.node.term.1)
      (_rightPayloadSizeLe : sizeOf rightPayload ≤
        sizeOf rightView.node.term.1)
      (_rawAligned : CanonicalStopAligned rawDeclaration rawStop leftPayload
        rightPayload)
      (_foreign : declarationColor ≠ color)
      (_quotePair : RhoPlanStopQuotePairCell leftReached.plan.rootClass
        rightReached.plan.rootClass),
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

/-- **The foreign half of family 3 from the delegated obligation and the
structurally eligible foreign obligation.**

The stop-reason disjunction is resolved: its delegated half is already
family 2/4 content. -/
theorem
    RhoStaticNonBoundaryPlanStopSourceAlignedOn.foreignQuotePair_of_delegated
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    {leftView : left.StaticRootView color}
    {rightView : right.StaticRootView color}
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor rawStop)
    (foreignEligible : RhoPlanStopForeignQuotePairSourceLeaf leftView rightView
      declarationColor rawStop) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop
      (RhoPlanStopForeignQuotePairCell declarationColor color) := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  rcases stopReason with stopped | eligible
  · exact delegated callbackAvailable callbackScope leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
      rightEmbedding leftRoute rightRoute leftPayloadSizeLe rightPayloadSizeLe
      rawAligned notBothBoundary stopped
  · exact foreignEligible callbackAvailable callbackScope leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute eligible
      leftPayloadSizeLe rightPayloadSizeLe rawAligned cell.1 cell.2

/-! ## What the three families jointly reduce to -/

/-- **Families 2, 3 and 4 from two obligations.**

Where `RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells` asks for four
family residuals, this asks for the certified-boundary family and exactly two
statements about delegated and foreign paired-Quote stops.  The same-colour
paired Quote disappears entirely. -/
theorem RhoStaticNonBoundaryPlanStopSourceAligned.of_boundarySide_and_stops
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
    (declarationColor : CostStaticColor) (rawStop : Pattern → Pattern → Prop)
    (stopCollapsing : ∀ {left right}, rawStop left right →
      CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) left ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) right)
    (boundarySide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop RhoPlanStopBoundarySideCell)
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor rawStop)
    (foreignEligible : RhoPlanStopForeignQuotePairSourceLeaf leftView rightView
      declarationColor rawStop) :
    RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
      declarationColor rawStop :=
  RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells leftView rightView
    declarationColor rawStop stopCollapsing boundarySide
    (RhoStaticNonBoundaryPlanStopSourceAlignedOn.parallelSide_of_delegated
      (color := color) delegated)
    (RhoStaticNonBoundaryPlanStopSourceAlignedOn.quotePair_of_halves
      (RhoStaticNonBoundaryPlanStopSourceAlignedOn.sameColorQuoteSide_of_delegated
        (color := color) delegated)
      (RhoStaticNonBoundaryPlanStopSourceAlignedOn.foreignQuotePair_of_delegated
        delegated foreignEligible))
    (RhoStaticNonBoundaryPlanStopSourceAlignedOn.sameColorQuoteSide_of_delegated
      (color := color) delegated)

/-- The canonical-raw-stop instance, at any measure: both obligations are
stated over an arbitrary `rawStop`, so the same proof serves A1's measure and
A2's. -/
theorem RhoStaticNonBoundaryPlanStopSourceAligned.of_boundarySide_and_stops_rawStop
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
    (declarationColor : CostStaticColor) (parentMeasure : Nat)
    (boundarySide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopBoundarySideCell)
    (delegated : RhoPlanStopDelegatedSourceLeaf leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure))
    (foreignEligible : RhoPlanStopForeignQuotePairSourceLeaf leftView rightView
      declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)) :
    RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
      declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure) :=
  RhoStaticNonBoundaryPlanStopSourceAligned.of_boundarySide_and_stops leftView
    rightView declarationColor (RhoCanonicalRawStop declarationColor
      parentMeasure) rhoCanonicalRawStop_collapsingEndpoint boundarySide
    delegated foreignEligible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
