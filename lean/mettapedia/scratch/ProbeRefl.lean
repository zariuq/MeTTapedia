import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem probeRefl (declarationColor : CostStaticColor) :
    RhoAlignedViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWS rightWS closeSmaller roots
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    stopped
  simp only [RhoReachedPlanPairCommonApex]
  exact CostStaticAtomKeyCospan.CommonRestorationApex.refl _ _ _ _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
