import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryResidualSwitchboard

/-!
# Reached-root cells of the non-boundary plan-stop residual

`RhoStaticNonBoundaryPlanStopSourceAligned` is what obligations A1 and A2 both
leave after the certified-boundary/certified-boundary quadrant.  It takes the
stop relation as a parameter, and the two obligations instantiate that
parameter at different measures, so everything here is stated for an arbitrary
`rawStop` together with the single property the analysis consumes: a stop
exhibits a collapsing root on one of its endpoints.

The remaining content of the residual is indexed by the pair of *reached* root
classes.  This module settles which of those cells can occur at all, splits
the residual into the four families that survive, and records which family
descends by a measure-insensitive certificate.

## What is established here

* `RhoCollapsibleRootClass` — the reached root classes at which a rho payload
  can be a collapsing root of *either* generated Cost declaration: the two
  certified boundary classes, the authored Quote application, and the bare
  parallel collection.  A rigid root, an ordinary application and a
  non-parallel collection are each refuted (`not_rhoCollapsibleRootClass_*`).

* `rho_planStop_collapsibleSide` — at every plan stop of the residual at least
  one endpoint has a collapsible reached root class.  This is the colour-free
  strengthening of `RhoCanonicalRawStop.foreign_reached_stop_cases`, which
  needs `declarationColor ≠ color`; the same-colour instance is what the
  aligned arm actually meets.

* `rho_planStop_sharpCell` — the colour-refined form.  A *single* authored
  Quote endpoint is admissible only at the declaration's own colour, because a
  reached source Quote that collapses under a generated declaration belongs to
  that declaration's colour; at a foreign colour the Quote class survives only
  as the paired structural stop.

* `RhoStaticNonBoundaryPlanStopSourceAlignedOn` — the residual with an
  arbitrary reached-root cell predicate retained, and
  `RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells`, which reconstructs
  the residual from the four live families alone: one certified boundary side,
  one bare parallel side, the paired Quote terminal, and a single same-colour
  Quote side.  Every reached-root pair outside those four has contradictory
  hypotheses, so nothing is assumed about it.  The A1 and A2 instances are
  `rhoAlignedViewsRestorationAligned_of_liveCells` and
  `rhoCollapsingViewsPlanStopSourceAligned_of_liveCells`.

* Descent budgets per family, which do *not* agree.  The certified-boundary
  family descends strictly below the *endpoint* pair size with no reference to
  the stop measure at all (`rho_planStop_boundarySide_size_lt`), because the
  certificate is the node's own boundary table.  The bare-parallel family
  descends only below the stop measure (`rho_planStop_parallelSide_size_lt`),
  since its certificate is the delegated raw stop; that budget is therefore
  one larger at A2's measure than at A1's.

## What is *not* established here

The four live families are not discharged.  In the certified-boundary family
the alignment is forced to its `leaf` constructor
(`canonicalizeByDepths_reify_abstractPattern_of_isCertifiedBoundary` together
with `PatternLeafAligned.of_fvar_left`): the boundary endpoint's reached
abstract pattern is a single `Pattern.fvar`, which both `reify` and
`canonicalizeByDepths` leave as a free variable, so no structural congruence
step is available.  What remains there is a bare `RestoresTogether` between a
single semantic atom — whose `commonAssignment` value is a *hereditary normal
form* — and a whole `canonicalizeByDepths` frame with its atoms restored in
place.  Closing it needs a normal-form/canonical-form bridge that the
atom/atom producers of `RhoStaticPlanBoundaryRestoration` do not supply.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-! ## Which reached root classes can collapse -/

/-- The reached-plan root classes at which a rho payload can be a collapsing
root of some generated Cost declaration: the two certified boundary classes,
the authored Quote application, and the bare parallel collection. -/
def RhoCollapsibleRootClass (rootClass : CostStaticPlanRootClass) : Prop :=
  rootClass.IsCertifiedBoundary ∨
    rootClass = .application rhoReflectivePresentation.quoteConstructor ∨
    rootClass = .collection rhoReflectivePresentation.parallelCollection

/-- A collapsing raw root of either generated declaration forces a collapsible
reached root class. -/
theorem rhoCollapsibleRootClass_of_collapsingRoot
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached rhoCIGSLT color targetFree payload
      rootAbstract)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      payload) :
    RhoCollapsibleRootClass state.plan.rootClass := by
  rcases CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor state
      collapsing with boundaryApplication | boundaryCollection | quote |
      parallel
  · exact Or.inl (Or.inl boundaryApplication)
  · exact Or.inl (Or.inr boundaryCollection)
  · exact Or.inr (Or.inl quote)
  · exact Or.inr (Or.inr parallel)

/-- Positive control: a certified application boundary is collapsible. -/
theorem rhoCollapsibleRootClass_boundaryApplication :
    RhoCollapsibleRootClass .boundaryApplication := Or.inl (Or.inl rfl)

/-- Positive control: a certified collection boundary is collapsible. -/
theorem rhoCollapsibleRootClass_boundaryCollection :
    RhoCollapsibleRootClass .boundaryCollection := Or.inl (Or.inr rfl)

/-- Positive control: the authored Quote application is collapsible. -/
theorem rhoCollapsibleRootClass_quoteApplication :
    RhoCollapsibleRootClass
      (.application rhoReflectivePresentation.quoteConstructor) :=
  Or.inr (Or.inl rfl)

/-- Positive control: the bare parallel collection is collapsible. -/
theorem rhoCollapsibleRootClass_parallelCollection :
    RhoCollapsibleRootClass
      (.collection rhoReflectivePresentation.parallelCollection) :=
  Or.inr (Or.inr rfl)

/-- Negative control: a rigid reached root never collapses. -/
theorem not_rhoCollapsibleRootClass_rigid :
    ¬ RhoCollapsibleRootClass .rigid := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary]

/-- Negative control: an ordinary, non-Quote application root never
collapses. -/
theorem not_rhoCollapsibleRootClass_application
    {constructor : String}
    (ne : constructor ≠ rhoReflectivePresentation.quoteConstructor) :
    ¬ RhoCollapsibleRootClass (.application constructor) := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary,
    ne]

/-- Negative control: an ordinary, non-parallel collection root never
collapses. -/
theorem not_rhoCollapsibleRootClass_collection
    {collectionType : CollType}
    (ne : collectionType ≠ rhoReflectivePresentation.parallelCollection) :
    ¬ RhoCollapsibleRootClass (.collection collectionType) := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary,
    ne]

/-- The only property of the stop relation this module consumes: a delegated
stop exhibits a collapsing root on one of its endpoints.  Both measures used
by the lane satisfy it. -/
theorem rhoCanonicalRawStop_collapsingEndpoint
    {declarationColor : CostStaticColor} {parentMeasure : Nat}
    {left right : Pattern}
    (stopped : RhoCanonicalRawStop declarationColor parentMeasure left right) :
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) left ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) right :=
  stopped.1.1

/-! ## The reached-root cells the residual can actually meet -/

/-- **Colour-free reached-root switchboard of the residual.**

At every plan stop outside the certified-boundary quadrant at least one
endpoint has a collapsible reached root class, whatever the declaration colour
and whatever the stop measure.  Both stop reasons contribute: a delegated stop
supplies a collapsing root on one side, and every structurally eligible
non-boundary stop already exhibits a Quote, a certified collection boundary or
a bare parallel on one side. -/
theorem rho_planStop_collapsibleSide
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
    (stopReason : rawStop leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary)) :
    RhoCollapsibleRootClass leftReached.plan.rootClass ∨
      RhoCollapsibleRootClass rightReached.plan.rootClass := by
  rcases stopReason with stopped | eligible
  · rcases stopCollapsing stopped with leftCollapsing | rightCollapsing
    · exact Or.inl (rhoCollapsibleRootClass_of_collapsingRoot leftReached
        leftCollapsing)
    · exact Or.inr (rhoCollapsibleRootClass_of_collapsingRoot rightReached
        rightCollapsing)
  · rcases CostStaticPlanStopEligible.nonBoundary_cases rhoReflectivePresentation
        leftReached.plan rightReached.plan eligible notBothBoundary with
        quote | mixedLeft | mixedRight | parallel
    · exact Or.inl (Or.inr (Or.inl quote.1))
    · exact Or.inl (Or.inl (Or.inr mixedLeft.1))
    · exact Or.inr (Or.inl (Or.inr mixedRight.2))
    · exact Or.inl (Or.inr (Or.inr parallel.1))

/-- The reached-root cells a non-boundary plan stop can occupy, refined by the
declaration colour.  A single authored Quote endpoint is admissible only at the
plan's own colour; at a foreign colour the Quote class survives only as the
paired structural stop. -/
def RhoPlanStopCell (declarationColor color : CostStaticColor)
    (leftClass rightClass : CostStaticPlanRootClass) : Prop :=
  leftClass.IsCertifiedBoundary ∨
    rightClass.IsCertifiedBoundary ∨
    leftClass = .collection rhoReflectivePresentation.parallelCollection ∨
    rightClass = .collection rhoReflectivePresentation.parallelCollection ∨
    (leftClass = .application rhoReflectivePresentation.quoteConstructor ∧
      rightClass = .application rhoReflectivePresentation.quoteConstructor) ∨
    (declarationColor = color ∧
      (leftClass = .application rhoReflectivePresentation.quoteConstructor ∨
        rightClass = .application rhoReflectivePresentation.quoteConstructor))

/-- **Colour-refined reached-root switchboard of the residual.** -/
theorem rho_planStop_sharpCell
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
    (stopReason : rawStop leftPayload rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary)) :
    RhoPlanStopCell declarationColor color leftReached.plan.rootClass
      rightReached.plan.rootClass := by
  rcases stopReason with stopped | eligible
  · rcases stopCollapsing stopped with leftCollapsing | rightCollapsing
    · rcases CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor
          leftReached leftCollapsing with
          boundaryApplication | boundaryCollection | quote | parallel
      · exact Or.inl (Or.inl boundaryApplication)
      · exact Or.inl (Or.inr boundaryCollection)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            leftReached quote leftCollapsing, Or.inl quote⟩))))
      · exact Or.inr (Or.inr (Or.inl parallel))
    · rcases CostStaticPlanReached.rootClass_of_rhoCostCollapsingRootFor
          rightReached rightCollapsing with
          boundaryApplication | boundaryCollection | quote | parallel
      · exact Or.inr (Or.inl (Or.inl boundaryApplication))
      · exact Or.inr (Or.inl (Or.inr boundaryCollection))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨CostStaticPlanReached.declarationColor_eq_of_sourceQuote_collapsing
            rightReached quote rightCollapsing, Or.inr quote⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl parallel)))
  · rcases CostStaticPlanStopEligible.nonBoundary_cases rhoReflectivePresentation
        leftReached.plan rightReached.plan eligible notBothBoundary with
        quote | mixedLeft | mixedRight | parallel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl quote))))
    · exact Or.inl (Or.inr mixedLeft.1)
    · exact Or.inr (Or.inl (Or.inr mixedRight.2))
    · exact Or.inr (Or.inr (Or.inl parallel.1))

/-! ## The four live families -/

/-- Family 1: exactly one endpoint is a certified boundary.  (`notBothBoundary`
is already part of the residual telescope, so this is the mixed quadrant.) -/
def RhoPlanStopBoundarySideCell (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  leftClass.IsCertifiedBoundary ∨ rightClass.IsCertifiedBoundary

/-- Family 2: some endpoint is a bare parallel collection. -/
def RhoPlanStopParallelSideCell (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  leftClass = .collection rhoReflectivePresentation.parallelCollection ∨
    rightClass = .collection rhoReflectivePresentation.parallelCollection

/-- Family 3: the paired authored Quote terminal. -/
def RhoPlanStopQuotePairCell (leftClass rightClass :
    CostStaticPlanRootClass) : Prop :=
  leftClass = .application rhoReflectivePresentation.quoteConstructor ∧
    rightClass = .application rhoReflectivePresentation.quoteConstructor

/-- Family 4: a single authored Quote endpoint, at the declaration's own
colour.  At a foreign colour this family is empty. -/
def RhoPlanStopSameColorQuoteSideCell (declarationColor color :
    CostStaticColor) (leftClass rightClass : CostStaticPlanRootClass) : Prop :=
  declarationColor = color ∧
    (leftClass = .application rhoReflectivePresentation.quoteConstructor ∨
      rightClass = .application rhoReflectivePresentation.quoteConstructor)

/-- The four families cover every admissible cell. -/
theorem rhoPlanStopCell_cases {declarationColor color : CostStaticColor}
    {leftClass rightClass : CostStaticPlanRootClass}
    (cell : RhoPlanStopCell declarationColor color leftClass rightClass) :
    RhoPlanStopBoundarySideCell leftClass rightClass ∨
      RhoPlanStopParallelSideCell leftClass rightClass ∨
      RhoPlanStopQuotePairCell leftClass rightClass ∨
      RhoPlanStopSameColorQuoteSideCell declarationColor color leftClass
        rightClass := by
  rcases cell with leftBoundary | rightBoundary | leftParallel | rightParallel |
      quotePair | sameColorQuote
  · exact Or.inl (Or.inl leftBoundary)
  · exact Or.inl (Or.inr rightBoundary)
  · exact Or.inr (Or.inl (Or.inl leftParallel))
  · exact Or.inr (Or.inl (Or.inr rightParallel))
  · exact Or.inr (Or.inr (Or.inl quotePair))
  · exact Or.inr (Or.inr (Or.inr sameColorQuote))

/-! ### Descent budgets, which differ by family -/

/-- **The certified-boundary family descends without reference to the stop
measure.**

The certificate is the *node's own* boundary table, not the delegated stop, so
this budget is identical at A1's and A2's measures: the reached pair is
strictly smaller than the endpoint pair. -/
theorem rho_planStop_boundarySide_size_lt
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode rhoCIGSLT color targetFree)
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    (leftEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree leftReached.plan.boundaryTable.entries
      leftNode.plan.boundaryTable.entries))
    (rightEmbedding : Nonempty (CostStaticPlanEntryEmbedding rhoCIGSLT color
      targetFree rightReached.plan.boundaryTable.entries
      rightNode.plan.boundaryTable.entries))
    (leftPayloadSizeLe : sizeOf leftPayload ≤ sizeOf leftNode.term.1)
    (rightPayloadSizeLe : sizeOf rightPayload ≤ sizeOf rightNode.term.1)
    (boundary : RhoPlanStopBoundarySideCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    sizeOf leftPayload + sizeOf rightPayload <
      sizeOf leftNode.term.1 + sizeOf rightNode.term.1 := by
  rcases boundary with leftBoundary | rightBoundary
  · obtain ⟨leftBoundaryView⟩ :=
      leftReached.nonempty_boundaryView_of_boundaryClass leftBoundary
    obtain ⟨leftEmbedding⟩ := leftEmbedding
    exact CostStaticPlanReached.mixed_pair_size_lt_of_left_boundary leftNode
      rightNode leftReached leftBoundaryView leftEmbedding rightPayloadSizeLe
  · obtain ⟨rightBoundaryView⟩ :=
      rightReached.nonempty_boundaryView_of_boundaryClass rightBoundary
    obtain ⟨rightEmbedding⟩ := rightEmbedding
    exact CostStaticPlanReached.mixed_pair_size_lt_of_right_boundary leftNode
      rightNode rightReached rightBoundaryView rightEmbedding leftPayloadSizeLe

/-- A bare parallel root on the left endpoint forces the delegated stop, for
any stop relation.  The structural collection constructor of
`CanonicalStopAligned` is guarded against the declaration's own parallel
collection, and colouring does not rename collection types, so the guard fires
at both colours. -/
theorem rho_rawStop_of_leftParallelPayload
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    {leftElements : List Pattern} {rightPayload : Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop
      (.collection rhoReflectivePresentation.parallelCollection leftElements
        none)
      rightPayload) :
    rawStop
      (.collection rhoReflectivePresentation.parallelCollection leftElements
        none)
      rightPayload := by
  cases rawAligned with
  | leaf given => exact given
  | collection ne elements =>
      exact absurd
        (costStaticReflectivePresentationDecl_parallelCollection
          declarationColor).symm ne

/-- Right-endpoint companion of `rho_rawStop_of_leftParallelPayload`. -/
theorem rho_rawStop_of_rightParallelPayload
    {declarationColor : CostStaticColor} {rawStop : Pattern → Pattern → Prop}
    {leftPayload : Pattern} {rightElements : List Pattern}
    (rawAligned : CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation)
      rawStop leftPayload
      (.collection rhoReflectivePresentation.parallelCollection rightElements
        none)) :
    rawStop leftPayload
      (.collection rhoReflectivePresentation.parallelCollection rightElements
        none) := by
  cases rawAligned with
  | leaf given => exact given
  | collection ne elements =>
      exact absurd
        (costStaticReflectivePresentationDecl_parallelCollection
          declarationColor).symm ne

/-- **In the bare-parallel family the delegated stop is forced**, for any stop
relation. -/
theorem rho_planStop_rawStop_of_parallelSide
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
    (parallel : RhoPlanStopParallelSideCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    rawStop leftPayload rightPayload := by
  rcases parallel with leftParallel | rightParallel
  · obtain ⟨leftElements, leftRest, leftShape⟩ :=
      CostStaticRegionPlan.collectionRoot_of_rootClass leftReached.plan
        leftParallel
    subst leftShape
    have leftRestNone :=
      CostStaticRegionPlan.RawAdmission.collectionRest_eq_none leftAdmission
    subst leftRestNone
    exact rho_rawStop_of_leftParallelPayload rawAligned
  · obtain ⟨rightElements, rightRest, rightShape⟩ :=
      CostStaticRegionPlan.collectionRoot_of_rootClass rightReached.plan
        rightParallel
    subst rightShape
    have rightRestNone :=
      CostStaticRegionPlan.RawAdmission.collectionRest_eq_none rightAdmission
    subst rightRestNone
    exact rho_rawStop_of_rightParallelPayload rawAligned

/-- **The bare-parallel family descends only below the stop measure.**

Unlike `rho_planStop_boundarySide_size_lt`, this budget is the delegated
stop's own second component, so it is one larger at A2's measure than at
A1's. -/
theorem rho_planStop_parallelSide_size_lt
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
    (parallel : RhoPlanStopParallelSideCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    sizeOf leftPayload + sizeOf rightPayload < parentMeasure :=
  (rho_planStop_rawStop_of_parallelSide leftReached rightReached leftAdmission
    rightAdmission rawAligned parallel).2

/-- The paired-Quote family splits by colour: at the declaration's own colour
the delegated stop is forced, and at the foreign colour the two payloads are
generated Quotes of the plan's colour whose argument lists are aligned
structurally. -/
theorem rho_planStop_quotePair_cases
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
    (quotePair : RhoPlanStopQuotePairCell leftReached.plan.rootClass
      rightReached.plan.rootClass) :
    (declarationColor = color ∧ rawStop leftPayload rightPayload) ∨
      (declarationColor = color.flip ∧
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
            rawStop leftArguments rightArguments) :=
  CanonicalStopAligned.reached_sourceQuotes_cases leftReached rightReached
    quotePair.1 quotePair.2 stopCollapsing rawAligned

/-! ### The certified-boundary family has only the leaf constructor -/

/-- A semantic-leaf alignment whose left endpoint is a free variable is a
leaf. -/
theorem PatternLeafAligned.of_fvar_left
    {relation : Pattern → Pattern → Prop} {name : String} {right : Pattern}
    (aligned : PatternLeafAligned relation (.fvar name) right) :
    relation (.fvar name) right := by
  cases aligned with
  | leaf related => exact related

/-- Right-endpoint companion of `PatternLeafAligned.of_fvar_left`. -/
theorem PatternLeafAligned.of_fvar_right
    {relation : Pattern → Pattern → Prop} {left : Pattern} {name : String}
    (aligned : PatternLeafAligned relation left (.fvar name)) :
    relation left (.fvar name) := by
  cases aligned with
  | leaf related => exact related

/-- A certified boundary plan abstracts its whole root to one source
variable. -/
theorem abstractPattern_eq_fvar_of_isCertifiedBoundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) :
    ∃ name, plan.abstractPattern = .fvar name := by
  cases plan <;>
    first
      | exact ⟨_, rfl⟩
      | simp [CostStaticPlanRootClass.IsCertifiedBoundary,
          CostStaticRegionPlan.rootClass] at boundaryClass

/-- **No structural congruence is available on a certified-boundary
endpoint.**

Reification and keyed canonicalization both leave a free variable alone, so
the residual's `PatternLeafAligned` obligation is forced to its `leaf`
constructor on that side. -/
theorem canonicalizeByDepths_reify_abstractPattern_of_isCertifiedBoundary
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (availableDepth scopeDepth : Nat)
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound
      targetBound thinning sourceAvailable outer pattern sourceType)
    (boundaryClass : plan.rootClass.IsCertifiedBoundary) :
    ∃ name, canonicalizeByDepths key declaration availableDepth scopeDepth
      (environment.reify plan.abstractPattern) = .fvar name := by
  obtain ⟨abstractName, abstractEq⟩ :=
    abstractPattern_eq_fvar_of_isCertifiedBoundary plan boundaryClass
  refine ⟨environment.reifyName abstractName, ?_⟩
  rw [abstractEq]
  simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]

/-! ## The residual restricted to a family of reached-root cells -/

/-- The non-boundary plan-stop residual restricted to the reached-root pairs
satisfying `cell`.  The telescope is that of
`RhoStaticNonBoundaryPlanStopSourceAligned`, with the cell hypothesis
retained; the stop relation stays a parameter, so the same statement serves
A1's and A2's measures. -/
def RhoStaticNonBoundaryPlanStopSourceAlignedOn
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
    (rawStop : Pattern → Pattern → Prop)
    (cell : CostStaticPlanRootClass → CostStaticPlanRootClass → Prop) : Prop :=
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
          rightReached.plan.rootClass.IsCertifiedBoundary))
      (_cell : cell leftReached.plan.rootClass rightReached.plan.rootClass),
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

/-- Weakening a cell predicate weakens the restricted residual. -/
theorem RhoStaticNonBoundaryPlanStopSourceAlignedOn.mono
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
    {weak strong : CostStaticPlanRootClass → CostStaticPlanRootClass → Prop}
    (implication : ∀ leftClass rightClass, strong leftClass rightClass →
      weak leftClass rightClass)
    (residual : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop weak) :
    RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
      declarationColor rawStop strong := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
    cell
  exact residual callbackAvailable callbackScope leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
    rightPayloadSizeLe rawAligned notBothBoundary (implication _ _ cell)

/-- **The residual is carried by its four live families**, at any stop
relation whose delegated stops exhibit a collapsing endpoint.

Every reached-root pair outside the four families has contradictory
hypotheses: `rho_planStop_sharpCell` supplies the cell certificate from the
residual's own stop evidence, so no assumption is made about those pairs. -/
theorem RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells
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
    (parallelSide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop RhoPlanStopParallelSideCell)
    (quotePair : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop RhoPlanStopQuotePairCell)
    (sameColorQuoteSide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor rawStop
      (RhoPlanStopSameColorQuoteSideCell declarationColor color)) :
    RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
      declarationColor rawStop := by
  intro callbackAvailable callbackScope leftAbstract rightAbstract leftPayload
    rightPayload leftReached rightReached leftAdmission rightAdmission
    leftAbstractEq rightAbstractEq sourceTypeEq sourceAvailableEq sourceBoundEq
    targetBoundEq thinningEq leftEmbedding rightEmbedding leftRoute rightRoute
    stopReason leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
  rcases rhoPlanStopCell_cases
      (rho_planStop_sharpCell leftReached rightReached stopCollapsing stopReason
        notBothBoundary) with
      boundary | parallel | quote | sameColorQuote
  · exact boundarySide callbackAvailable callbackScope leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
      rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
      rightPayloadSizeLe rawAligned notBothBoundary boundary
  · exact parallelSide callbackAvailable callbackScope leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
      rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
      rightPayloadSizeLe rawAligned notBothBoundary parallel
  · exact quotePair callbackAvailable callbackScope leftReached rightReached
      leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
      sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
      rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
      rightPayloadSizeLe rawAligned notBothBoundary quote
  · exact sameColorQuoteSide callbackAvailable callbackScope leftReached
      rightReached leftAdmission rightAdmission leftAbstractEq rightAbstractEq
      sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
      leftEmbedding rightEmbedding leftRoute rightRoute stopReason
      leftPayloadSizeLe rightPayloadSizeLe rawAligned notBothBoundary
      sameColorQuote

/-- The canonical-raw-stop instance of `of_liveCells`, at any measure. -/
theorem RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells_rawStop
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
    (parallelSide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopParallelSideCell)
    (quotePair : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure)
      RhoPlanStopQuotePairCell)
    (sameColorQuoteSide : RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView
      rightView declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure)
      (RhoPlanStopSameColorQuoteSideCell declarationColor color)) :
    RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
      declarationColor
      (RhoCanonicalRawStop declarationColor parentMeasure) :=
  RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells leftView rightView
    declarationColor (RhoCanonicalRawStop declarationColor parentMeasure)
    rhoCanonicalRawStop_collapsingEndpoint boundarySide parallelSide quotePair
    sameColorQuoteSide

/-- **Obligation A1 from the four live families alone**, at A1's measure. -/
theorem rhoAlignedViewsRestorationAligned_of_liveCells
    {declarationColor : CostStaticColor}
    (families : ∀ {targetFree : WellSorted.FreeTypeContext}
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
      RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern))
          RhoPlanStopBoundarySideCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern))
          RhoPlanStopParallelSideCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern))
          RhoPlanStopQuotePairCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern))
          (RhoPlanStopSameColorQuoteSideCell declarationColor color)) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor := by
  apply rhoAlignedViewsRestorationAligned_of_nonBoundaryRemainder
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller
  obtain ⟨boundarySide, parallelSide, quotePair, sameColorQuoteSide⟩ :=
    families leftView rightView admissible leftWellSorted rightWellSorted
      closeSmaller
  exact RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells_rawStop leftView
    rightView declarationColor (sizeOf leftPattern + sizeOf rightPattern)
    boundarySide parallelSide quotePair sameColorQuoteSide

/-- **The same-colour half of obligation A2 from the four live families
alone**, at A2's measure.  The statement differs from
`rhoAlignedViewsRestorationAligned_of_liveCells` only in the retained
endpoint-collapse evidence and in the measure the gate forces. -/
theorem rhoCollapsingViewsPlanStopSourceAligned_of_liveCells
    {declarationColor : CostStaticColor}
    (families : ∀ {targetFree : WellSorted.FreeTypeContext}
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
      (CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftPattern ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightPattern) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightPattern →
      RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern + 1))
          RhoPlanStopBoundarySideCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern + 1))
          RhoPlanStopParallelSideCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern + 1))
          RhoPlanStopQuotePairCell ∧
        RhoStaticNonBoundaryPlanStopSourceAlignedOn leftView rightView
          declarationColor
          (RhoCanonicalRawStop declarationColor
            (sizeOf leftPattern + sizeOf rightPattern + 1))
          (RhoPlanStopSameColorQuoteSideCell declarationColor color)) :
    RhoCollapsingViewsPlanStopSourceAlignedInDomain declarationColor := by
  apply rhoCollapsingViewsPlanStopSourceAligned_of_nonBoundaryRemainder
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller collapsing canonical
  obtain ⟨boundarySide, parallelSide, quotePair, sameColorQuoteSide⟩ :=
    families leftView rightView admissible leftWellSorted rightWellSorted
      closeSmaller collapsing canonical
  exact RhoStaticNonBoundaryPlanStopSourceAligned.of_liveCells_rawStop leftView
    rightView declarationColor (sizeOf leftPattern + sizeOf rightPattern + 1)
    boundarySide parallelSide quotePair sameColorQuoteSide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
