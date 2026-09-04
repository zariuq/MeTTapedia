import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- PROBE: the canonicalized source frame of an application-abstracting node
keeps that head. -/
theorem CostStaticRegionNode.sourceFrame_apply
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    {label : String} {abstracts : List Pattern}
    (abstractEq : node.plan.abstractPattern = .apply label abstracts)
    (notQuote : label ≠ declaration.quoteConstructor) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key
        declaration node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 =
      .apply label
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths key
          declaration node.targetBound.length 0
          (abstracts.map environment.reify)) := by
  have skeletonEq : node.skeleton.1 = .apply label abstracts :=
    node.skeleton_pattern.trans abstractEq
  rw [node.reifiedSourceFrame_pattern, congrArg environment.reify skeletonEq]
  simp only [CostStaticAtomEnvironment.reify]
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_apply_of_ne_quote
    key declaration node.targetBound.length 0 label
    (abstracts.map environment.reify) notQuote

end Mettapedia.GSLT.LanguageDef
