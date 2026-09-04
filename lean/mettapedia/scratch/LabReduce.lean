import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- (R): restoration alignment for any two static root views. -/
abbrev RhoStaticFramesRestorationAlignedEverywhere : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {leftColor rightColor : CostStaticColor}
    {declarationColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor),
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) rightPattern →
    RhoStaticFramesRestorationAligned leftView rightView

/-- (E): leaf exposure against a structural partner. -/
abbrev RhoCollapsingLeafExposureEverywhere : Type :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {leftColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor),
    right.rootIsStatic = false →
    RhoCollapsingLeafExposure leftView.node leftView.children right

/-- PROBE: every bridge case yields a semantic cut from (R) and (E) alone. -/
theorem probe_cut_of_restoration_and_exposure
    {declarationColor : CostStaticColor}
    (restoration : RhoStaticFramesRestorationAlignedEverywhere)
    (exposure : RhoCollapsingLeafExposureEverywhere)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) rightPattern)
    (rootCase : RhoCanonicalStaticPairBridgeCase declarationColor left right) :
    Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
      rootCase) := by
  cases rootCase with
  | aligned color leftView rightView roots =>
      exact ⟨.matched leftView rightView roots
        (RhoMatchedStaticFramesCut.ofRestorationAligned leftView rightView
          (restoration leftView rightView canonical))⟩
  | leftCollapsing leftColor leftView collapsing =>
      by_cases partnerStatic : right.rootIsStatic = true
      · obtain ⟨⟨rightColor, rightRoot⟩⟩ :=
          (right.staticRootShape_of_rootIsStatic partnerStatic
            ).nonempty_staticRootColor right
        by_cases sameColor : rightColor = leftColor
        · subst sameColor
          exact ⟨.leftStaticEnclosing leftView collapsing rightRoot.toView
            (RhoMatchedStaticFramesApex.ofRestorationAligned leftView
              rightRoot.toView (restoration leftView rightRoot.toView canonical))⟩
        · exact ⟨.leftCrossColorEnclosing leftView collapsing rightRoot.toView
            (fun equal => sameColor equal.symm)
            (restoration leftView rightRoot.toView canonical)⟩
      · exact ⟨.leftEnclosing leftView collapsing
          (exposure leftView (by simpa using partnerStatic))⟩
  | rightCollapsing rightColor rightView collapsing =>
      by_cases partnerStatic : left.rootIsStatic = true
      · obtain ⟨⟨leftColor, leftRoot⟩⟩ :=
          (left.staticRootShape_of_rootIsStatic partnerStatic
            ).nonempty_staticRootColor left
        by_cases sameColor : leftColor = rightColor
        · subst sameColor
          exact ⟨.rightStaticEnclosing rightView collapsing leftRoot.toView
            (RhoMatchedStaticFramesApex.ofRestorationAligned leftRoot.toView
              rightView (restoration leftRoot.toView rightView canonical))⟩
        · exact ⟨.rightCrossColorEnclosing rightView collapsing leftRoot.toView
            sameColor (restoration leftRoot.toView rightView canonical)⟩
      · exact ⟨.rightEnclosing rightView collapsing
          (exposure rightView (by simpa using partnerStatic))⟩

/-- PROBE: the built provider from (R) and (E). -/
theorem probe_provider_of_restoration_and_exposure
    (restoration : RhoStaticFramesRestorationAlignedEverywhere)
    (exposure : RhoCollapsingLeafExposureEverywhere)
    (declarationColor : CostStaticColor) :
    RhoCanonicalStaticPairSemanticCutProviderInDomainBuilt declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller rootCase
  exact probe_cut_of_restoration_and_exposure restoration exposure canonical
    rootCase

/-- PROBE: the Cost one domain object from (R) and (E). -/
noncomputable def probe_object
    (restoration : RhoStaticFramesRestorationAlignedEverywhere)
    (exposure : RhoCollapsingLeafExposureEverywhere) :
    CostOneDomainObject :=
  rhoHereditaryCostOneDomainObject_ofBuiltProvider
    (probe_provider_of_restoration_and_exposure restoration exposure)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
