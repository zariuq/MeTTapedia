import Mettapedia.GSLT.LanguageDef.Cost
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef

-- the seal, over the four apex-slice obligations, reachable from the umbrella alone
noncomputable example
    (a1 : ∀ color, RhoAlignedViewsPlanStopApexInDomain color)
    (a2s : ∀ color, RhoCollapsingViewsPlanStopApexInDomain color)
    (a2x : ∀ color, RhoCollapsingCrossColorViewsRestorationAlignedInDomain color)
    (b : ∀ color, RhoCollapsingLeafExposureInDomain color) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_ofApexSliceObligations a1 a2s a2x b

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostOneDomainObject_ofApexSliceObligations
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.rhoHereditaryCostOneObjectLaws_ofApexSliceObligations
-- refuted route, reachable and checked
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe.not_rhoCollapsingLeafClassifications
-- quotation seals ambient binders
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness.certifyCostRegionBoundary?_quoteDropBVar_eq_none
