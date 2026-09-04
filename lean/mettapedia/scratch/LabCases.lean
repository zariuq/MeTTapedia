import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PROBE: only the apply and collection arms of a root alignment survive when
both endpoints carry static root views. -/
example {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    {declarationColor : CostStaticColor}
    (roots : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern rightPattern) :
    (∃ label arguments, leftPattern = .apply label arguments) ∨
      (∃ collectionType elements rest,
        leftPattern = .collection collectionType elements rest) := by
  have static := leftView.rootIsStatic
  rcases left.pattern_shape_of_rootIsStatic static with
    ⟨wireName, arguments, shape⟩ | ⟨collectionType, elements, rest, shape⟩
  · exact .inl ⟨wireName, arguments, shape⟩
  · exact .inr ⟨collectionType, elements, rest, shape⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
