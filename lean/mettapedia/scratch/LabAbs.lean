import Mettapedia.GSLT.LanguageDef.CostRegionTree

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: a static node whose term is an application abstracts to an
application. -/
theorem CostStaticRegionNode.abstractPattern_apply
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {wireName : String} {arguments : List Pattern}
    (shape : node.term.1 = .apply wireName arguments) :
    ∃ label abstracts, node.plan.abstractPattern = .apply label abstracts := by
  obtain ⟨targetBound, sourceSort, term, plan, rootStatic, skeleton,
    skeletonPattern, supported, supportSafe⟩ := node
  obtain ⟨termPattern, termTyped⟩ := term
  obtain ⟨sortName, sortMember⟩ := sourceSort
  simp only at shape
  subst shape
  cases plan <;>
    first
      | exact ⟨_, _, rfl⟩
      | simp [CostStaticRegionPlan.isStaticRoot] at rootStatic
      | simp_all [CostStaticRegionPlan.abstractPattern,
          CostStaticRegionPlan.isStaticRoot]

end Mettapedia.GSLT.LanguageDef
