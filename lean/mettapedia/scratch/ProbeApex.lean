import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem probeApex (declarationColor : CostStaticColor) :
    RhoAlignedViewsPlanStopApexInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWS rightWS closeSmaller roots
  intro callbackAvailable callbackScope callbackRoot leftAbstract rightAbstract
    stopped
  obtain ⟨leftPayload, rightPayload, leftReached, rightReached, leftAdmission,
    rightAdmission, leftAbstractEq, rightAbstractEq, sourceTypeEq,
    sourceAvailableEq, sourceBoundEq, targetBoundEq, thinningEq, leftEmbedding,
    rightEmbedding, leftRoute, rightRoute, stopReason, leftSizeLe,
    rightSizeLe, rawAligned⟩ := stopped
  by_cases hcolor : color = declarationColor
  · subst hcolor
    rcases stopReason with hraw | eligible
    · exact RhoCanonicalPairRecursiveResult.reachedApex_of_rawStop_sameColor
        leftView rightView
        (rightRootAdmissible_of_admissible rightView admissible)
        callbackAvailable callbackScope callbackRoot leftReached rightReached
        leftAdmission rightAdmission leftAbstractEq rightAbstractEq
        sourceTypeEq sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
        leftEmbedding rightEmbedding leftRoute rightRoute hraw (fun {_ _ _ _ _} => closeSmaller)
    · skip
  · skip

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
