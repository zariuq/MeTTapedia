import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingRestoration

open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

-- Generic gate lemmas
#check @CanonicalStopAligned.given_of_collapsingRoot_left
#check @CanonicalStopAligned.given_of_collapsingRoot_right
#check @CanonicalStopAligned.given_of_collapsingRoot
#print axioms CanonicalStopAligned.given_of_collapsingRoot_left
#print axioms CanonicalStopAligned.given_of_collapsingRoot_right
#print axioms CanonicalStopAligned.given_of_collapsingRoot

-- Rho measure gate
#check @not_canonicalStopAligned_endpoints_of_collapsing
#check @rhoCanonicalStopAligned_succ_of_collapsing
#print axioms not_canonicalStopAligned_endpoints_of_collapsing
#print axioms rhoCanonicalStopAligned_succ_of_collapsing

-- Cross-colour fibre confinement
#check @CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
#print axioms CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne

-- Same-colour chain
#check @RhoCollapsingViewsPlanStopSourceAlignedInDomain
#check @rhoCollapsingSameColorViewsRestorationAligned_of_planStopSourceAligned
#check @rhoCollapsingViewsPlanStopSourceAligned_of_nonBoundaryRemainder
#print axioms rhoCollapsingSameColorViewsRestorationAligned_of_planStopSourceAligned
#print axioms rhoCollapsingViewsPlanStopSourceAligned_of_nonBoundaryRemainder

-- Cross-colour
#check @RhoStaticFramesRestorationAligned.ofFramesRestoreTogether
#check @RhoCollapsingCrossColorViewsRestorationAlignedInDomain
#print axioms RhoStaticFramesRestorationAligned.ofFramesRestoreTogether

-- A2 from the two halves
#check @rho_collapsingViewsRestorationAlignedInDomain_of_halves
#check @rho_collapsingViewsRestorationAlignedInDomain_of_residuals
#print axioms rho_collapsingViewsRestorationAlignedInDomain_of_halves
#print axioms rho_collapsingViewsRestorationAlignedInDomain_of_residuals

-- The reduction really targets the seal obligation A2, verbatim, with the
-- exact name the seal quotes.
example (declarationColor : CostStaticColor)
    (sameColor : RhoCollapsingViewsPlanStopSourceAlignedInDomain declarationColor)
    (crossColor : RhoCollapsingCrossColorViewsRestorationAlignedInDomain declarationColor) :
    RhoCollapsingViewsRestorationAlignedInDomain declarationColor :=
  rho_collapsingViewsRestorationAlignedInDomain_of_halves sameColor crossColor

-- And it composes into the seal statement itself.
noncomputable example
    (alignedApex : ∀ color, RhoAlignedViewsPlanStopApexInDomain color)
    (sameColor : ∀ color, RhoCollapsingViewsPlanStopSourceAlignedInDomain color)
    (crossColor : ∀ color, RhoCollapsingCrossColorViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeafExposureInDomain color) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_ofApexObligations alignedApex
    (fun color =>
      rho_collapsingViewsRestorationAlignedInDomain_of_halves (sameColor color)
        (crossColor color))
    exposure
