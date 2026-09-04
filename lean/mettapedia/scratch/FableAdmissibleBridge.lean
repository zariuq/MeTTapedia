import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The right-root admissibility consumed by the boundary quadrant is exactly
the ambient admissibility of the obligation's typed fibre. -/
theorem fable_rightRootAdmissible
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {rightPattern : Pattern}
    {type : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (rightView : right.StaticRootView color)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type) :
    rhoCanonicalRecursiveTypeDomain.Admissible
      (mapTypeExpr (color.symbols rhoCIGSLT)
        (.base rightView.node.sourceSort.1)) := by
  have typeEq := rightView.typeEq
  simpa only [← typeEq, mapTypeExpr, CostStaticColor.mapLangSort_name]
    using admissible

end Mettapedia.Languages.ProcessCalculi.RhoCalculus

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.fable_rightRootAdmissible
