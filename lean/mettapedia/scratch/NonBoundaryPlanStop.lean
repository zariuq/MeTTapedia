import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-- The reached-plan root classes at which a rho payload can be a collapsing
root of some generated Cost declaration. -/
def RhoCollapsibleRootClass (rootClass : CostStaticPlanRootClass) : Prop :=
  rootClass.IsCertifiedBoundary ∨
    rootClass = .application rhoReflectivePresentation.quoteConstructor ∨
    rootClass = .collection rhoReflectivePresentation.parallelCollection

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

/-- Negative canary: a rigid reached root is never collapsible. -/
theorem not_rhoCollapsibleRootClass_rigid :
    ¬ RhoCollapsibleRootClass .rigid := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary]

/-- Negative canary: an ordinary (non-Quote) application root is never
collapsible. -/
theorem not_rhoCollapsibleRootClass_application
    {constructor : String}
    (ne : constructor ≠ rhoReflectivePresentation.quoteConstructor) :
    ¬ RhoCollapsibleRootClass (.application constructor) := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary,
    ne]

/-- Negative canary: a non-parallel collection root is never collapsible. -/
theorem not_rhoCollapsibleRootClass_collection
    {collectionType : CollType}
    (ne : collectionType ≠ rhoReflectivePresentation.parallelCollection) :
    ¬ RhoCollapsibleRootClass (.collection collectionType) := by
  simp [RhoCollapsibleRootClass, CostStaticPlanRootClass.IsCertifiedBoundary,
    ne]

/-- Positive canary: both certified boundary classes are collapsible. -/
theorem rhoCollapsibleRootClass_boundaryApplication :
    RhoCollapsibleRootClass .boundaryApplication := Or.inl (Or.inl rfl)

theorem rhoCollapsibleRootClass_boundaryCollection :
    RhoCollapsibleRootClass .boundaryCollection := Or.inl (Or.inr rfl)

/-- **Colour-free reached-root switchboard.** -/
theorem rho_planStop_collapsibleSide
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (leftReached : CostStaticPlanReached rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (rightReached : CostStaticPlanReached rhoCIGSLT color targetFree
      rightPayload rightRootAbstract)
    {parentMeasure : Nat}
    (stopReason : RhoCanonicalRawStop declarationColor parentMeasure leftPayload
        rightPayload ∨
      CostStaticPlanStopEligible rhoReflectivePresentation leftReached.plan
        rightReached.plan)
    (notBothBoundary :
      ¬ (leftReached.plan.rootClass.IsCertifiedBoundary ∧
        rightReached.plan.rootClass.IsCertifiedBoundary)) :
    RhoCollapsibleRootClass leftReached.plan.rootClass ∨
      RhoCollapsibleRootClass rightReached.plan.rootClass := by
  rcases stopReason with stopped | eligible
  · rcases stopped.1.1 with leftCollapsing | rightCollapsing
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
