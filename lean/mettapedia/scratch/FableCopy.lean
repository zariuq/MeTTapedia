import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderLeftCollapsing

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

theorem fable_copy_of_splitObligations
    {declarationColor : CostStaticColor}
    (alignedRestoration :
      RhoAlignedViewsRestorationAlignedInDomain declarationColor)
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
      exact ⟨RhoCanonicalStaticPairSemanticCut.matchedOfRestorationAligned
        leftView rightView roots
        (alignedRestoration leftView rightView admissible leftWellSorted
          rightWellSorted close roots)⟩


end Mettapedia.Languages.ProcessCalculi.RhoCalculus
