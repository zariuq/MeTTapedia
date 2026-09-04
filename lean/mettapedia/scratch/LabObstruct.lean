import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorFlat
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Two applications with different constructors can only be leaf-aligned. -/
theorem relation_of_patternLeafAligned_apply_apply_of_ne
    {relation : Pattern → Pattern → Prop}
    {leftConstructor rightConstructor : String}
    {leftArguments rightArguments : List Pattern}
    (different : leftConstructor ≠ rightConstructor)
    (aligned : PatternLeafAligned relation
      (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments)) :
    relation (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments) := by
  cases aligned with
  | leaf related => exact related
  | apply constructor arguments => exact absurd rfl different

theorem not_restorationAligned_of_crossColor_applicationFrames
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    {leftWire rightWire leftSource rightSource : String}
    {leftArguments rightArguments : List Pattern}
    (leftFrame :
      leftView.node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl) =
        .apply leftWire leftArguments)
    (rightFrame :
      rightView.node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation.toReflectivePresentationDecl) =
        .apply rightWire rightArguments)
    (leftDecoded : decodeCostStaticConstructor leftColor leftWire = some leftSource)
    (rightDecoded : decodeCostStaticConstructor rightColor rightWire = some rightSource) :
    ¬ RhoStaticFramesRestorationAligned leftView rightView := by
  intro aligned
  simp only [RhoStaticFramesRestorationAligned] at aligned
  rw [leftFrame, rightFrame] at aligned
  have headNe : leftWire ≠ rightWire := by
    intro equality
    exact decodeCostStaticConstructor_color_disjoint different leftDecoded
      (equality ▸ rightDecoded)
  exact not_restoresTogether_reifyWith_apply_apply
    different leftDecoded rightDecoded _ _ _ _ _ _ _ _ leftArguments
    rightArguments
    (relation_of_patternLeafAligned_apply_apply_of_ne headNe aligned)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
