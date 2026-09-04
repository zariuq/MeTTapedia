import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryResidualSwitchboard

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open RhoStaticNonBoundaryPlanStopCommonApex

example
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (declarationColor : CostStaticColor)
    (mapStop : ∀ {a b c : Nat}, True) :
    AfterSameColorBoundarySideForeign leftView rightView declarationColor := by
  intro foreign callbackAvailable callbackScope callbackRoot leftAbstract
    rightAbstract leftPayload rightPayload leftReached rightReached
    leftAdmission rightAdmission leftAbstractEq rightAbstractEq sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq leftEmbedding
    rightEmbedding leftRoute rightRoute stopReason leftPayloadSizeLe
    rightPayloadSizeLe rawAligned notBothBoundary
  have aligned := rhoReachedPlan_canonicalStopAligned_of_rawAligned
    leftReached rightReached leftAdmission rightAdmission sourceTypeEq
    sourceAvailableEq sourceBoundEq targetBoundEq thinningEq
    rhoReflectivePresentation.toReflectivePresentationDecl
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    rawAligned
  subst leftAbstractEq
  subst rightAbstractEq
  refine RhoReachedPlanPairCommonApex.ofAlignedAbstracts leftView rightView
    callbackAvailable callbackScope callbackRoot aligned ?_ ?_
  case refine_2 =>
    intro availableDepth scopeDepth rootDepth name
    simp only [canonicalizeByDepths, mapPattern,
      CostStaticBinderThinning.thickenAmbientBVars,
      CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
      CostStaticAtomKeyCospan.reifyWith_fvar,
      CostStaticAtomEnvironment.reifyName,
      CostStaticAtomKeyCospan.reifyNameWith,
      CostStaticAtomEnvironment.lookupAtom?]
    repeat' split
    all_goals
      first
        | exact CostStaticAtomKeyCospan.CommonRestorationApex.refl _ _ _ _
        | skip
  case refine_1 => sorry

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
