import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySameColorReachedPairApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignPlanStopRestoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorExposureProvider

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Aligned static views have the exact plan-stop restoration apex for every
declaration colour.  At the views' own colour all stops lie strictly below the
endpoint pair; at the other colour the hereditary foreign-stop constructor
supplies the same conclusion. -/
theorem rho_alignedViewsPlanStopApexInDomain
    (declarationColor : CostStaticColor) :
    RhoAlignedViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible _leftWellSorted _rightWellSorted
    closeSmaller _roots
  have rightRootAdmissible := rightRootAdmissible_of_admissible rightView
    admissible
  have closeAtNodes : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftView.node.term.1 + sizeOf rightView.node.term.1) := by
    rw [leftView.patternEq, rightView.patternEq]
    exact closeSmaller
  by_cases sameColor : color = declarationColor
  · subst color
    simpa only [leftView.patternEq, rightView.patternEq] using
      (rho_staticPlanStopCommonApex_of_sameColor leftView rightView
        rightRootAdmissible closeAtNodes)
  · simpa only [leftView.patternEq, rightView.patternEq] using
      (rho_staticPlanStopCommonApex_of_foreign leftView rightView
        (Ne.symm sameColor) rightRootAdmissible closeAtNodes)

/-- Both generated declarations satisfy the aligned plan-stop apex
obligation. -/
theorem rho_alignedViewsPlanStopApexInDomain_allColors :
    ∀ color, RhoAlignedViewsPlanStopApexInDomain color :=
  rho_alignedViewsPlanStopApexInDomain

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
