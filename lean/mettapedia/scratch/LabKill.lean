import Mettapedia.GSLT.LanguageDef.CostStaticRootView
import Mettapedia.GSLT.LanguageDef.CostStaticRootInversion

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: a static root view's pattern is an application or a collection. -/
theorem CostRegionTree.StaticRootView.rootIsStatic
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color) : tree.rootIsStatic = true := by
  obtain ⟨node, children, patternEq, availableEq, typeEq, treeEq⟩ := view
  subst patternEq
  subst availableEq
  subst typeEq
  subst treeEq
  rfl

end Mettapedia.GSLT.LanguageDef
