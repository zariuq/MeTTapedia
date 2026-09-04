import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticRegionNode

theorem check_canonicalizeReifiedTargetFrame_equationEquiv
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (declaration : ReflectivePresentationDecl)
    (membership : declaration ∈
      source.costWholeLanguage.reflectivePresentations) :
    EquationSemantics.EquationEquiv defaultBasePremises
      source.costWholeLanguage
      (node.canonicalizeReifiedTargetFrame environment declaration)
      (node.reifyTargetFrame environment) := by
  have declarationValid :=
    LanguageDef.reflectivePresentation_validate_of_validate_eq_nil
      source.costWholeLanguage source.costWholeLanguage_validate declaration
      membership
  have quote_ne_drop :=
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.quoteConstructor_ne_dropConstructor_of_validate
      source.costWholeLanguage declaration declarationValid
  apply Relation.EqvGen.rel
  apply EquationSemantics.EquationContextStep.reflectiveInContext .hole
    membership
  change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (semanticPatternKeyAt environment) declaration node.targetBound.length
          (node.reifiedTargetFrame environment).1) =
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize declaration
      (node.reifiedTargetFrame environment).1
  exact
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_canonicalizeByAt
      (semanticPatternKeyAt environment) declaration quote_ne_drop
      node.targetBound.length (node.reifiedTargetFrame environment).1

end CostStaticRegionNode

end Mettapedia.GSLT.LanguageDef
