import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem probePlanStops (declarationColor : CostStaticColor) :
    RhoAlignedViewsRestorationAlignedInDomain declarationColor := by
  apply rhoAlignedViewsRestorationAligned_of_planStopSourceAligned
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWS rightWS closeSmaller
  intro callbackAvailable callbackScope leftAbstract rightAbstract stop
  obtain ⟨leftPayload, rightPayload, leftReached, rightReached, leftAdm,
    rightAdm, leftAbsEq, rightAbsEq, tyEq, avEq, sbEq, tbEq, thHEq,
    embL, embR, rtL, rtR, stopDisj, szL, szR, rawAl⟩ := stop
  rcases stopDisj with ⟨⟨collapsing, canonEq⟩, smaller⟩ | eligible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
