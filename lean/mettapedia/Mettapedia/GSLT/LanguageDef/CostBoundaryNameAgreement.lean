import Mettapedia.GSLT.LanguageDef.CostRegionTree

/-!
# A boundary name determines its record, across any two tables

`costRegionBoundaryVariableName` embeds the entire boundary record through an
injective code, and `resolve` selects entries by exactly that name.  So two
tables that both resolve one name agree on the *whole* underlying record —
the sealed/exposed divergence changes the name, never hides behind it.

This is the boundary-side half of key agreement for jointly-present
free-variable names; the source-side half is the uniformity family
(`restorationSupport_sourceVariable` and friends).
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace TypedCostRegionBoundaryTable

/-- A resolved entry carries exactly the queried name: `resolve` matches on
the boundary's own collision-free key. -/
theorem name_of_resolve {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    {name : String}
    {boundary : TypedCostRegionBoundary source color targetFree}
    (resolved : table.resolve name = some boundary) :
    costRegionBoundaryVariableName boundary.boundary = name := by
  induction table with
  | nil => simp [resolve] at resolved
  | cons head content tail inductionHypothesis =>
      simp only [resolve] at resolved
      split at resolved
      · rename_i matched
        have equality : head = boundary := Option.some.inj resolved
        subst boundary
        exact matched.symm
      · exact inductionHypothesis resolved

/-- **One name, one record.**  Two tables resolving the same name agree on
the entire underlying boundary record, by injectivity of the name coding.
The typed wrappers may differ in their proof fields; every key component is
computed from the record alone. -/
theorem boundary_eq_of_resolve_of_resolve {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    (leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences)
    (rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences)
    {name : String}
    {leftBoundary rightBoundary : TypedCostRegionBoundary source color
      targetFree}
    (leftResolved : leftTable.resolve name = some leftBoundary)
    (rightResolved : rightTable.resolve name = some rightBoundary) :
    leftBoundary.boundary = rightBoundary.boundary :=
  costRegionBoundaryVariableName_injective
    ((leftTable.name_of_resolve leftResolved).trans
      (rightTable.name_of_resolve rightResolved).symm)

end TypedCostRegionBoundaryTable

end Mettapedia.GSLT.LanguageDef
