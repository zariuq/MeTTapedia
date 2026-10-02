import Mettapedia.GSLT.LanguageDef.CostSemanticCarrier

/-!
# The named-assignment observation of retained frame action

Current frame action factors the occurrence vector through its existing
first-key assignment. Equal assignments therefore give equal target actions
for every current source representative, even when positional values differ.
This comparison does not identify their retained child forests.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.BoundaryRestorationCollision
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext}

/-- The existing restorer observes the named assignment, not the entire vector. -/
theorem restoration_eq_of_assignment_eq {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (first second : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (equal : first.assignment table = second.assignment table)
    (bound : List TypeExpr) (skeleton : Pattern) :
    first.restoreSupportedSkeleton table bound skeleton =
      second.restoreSupportedSkeleton table bound skeleton := by
  unfold TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton
  rw [equal]

/-- Every retained source representative has the same assignment factorization. -/
theorem actAvailable_eq_of_assignment_eq
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (first second : TypedCostRegionBoundaryTable.Values source color targetFree frame.boundaryTable)
    (equal : first.assignment frame.boundaryTable = second.assignment frame.boundaryTable) :
    (state.actAvailable first).pattern = (state.actAvailable second).pattern := by
  rw [CostStaticFrameState.actAvailable_pattern, CostStaticFrameState.actAvailable_pattern]
  change ReflectiveContextSupport.substitute source.costWholeReflectionProfile
      frame.boundaryTable.restorationSupport (first.assignment frame.boundaryTable)
      frame.targetBound (frame.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols source) state.current.term.1)) =
    ReflectiveContextSupport.substitute source.costWholeReflectionProfile
      frame.boundaryTable.restorationSupport (second.assignment frame.boundaryTable)
      frame.targetBound (frame.thinning.thickenAmbientBVars 0
        (mapPattern (color.symbols source) state.current.term.1))
  rw [equal]

/-- Adding sealed outer binders does not recover information lost by named lookup. -/
theorem actAvailableWithOuter_eq_of_assignment_eq
    {frame : CostStaticRegionNode source color targetFree}
    (state : CostStaticFrameState frame)
    (first second : TypedCostRegionBoundaryTable.Values source color targetFree frame.boundaryTable)
    (equal : first.assignment frame.boundaryTable = second.assignment frame.boundaryTable)
    (outer : List TypeExpr) :
    (state.actAvailableWithOuter first outer).pattern =
      (state.actAvailableWithOuter second outer).pattern :=
  actAvailable_eq_of_assignment_eq state first second equal

end Mettapedia.GSLT.LanguageDef.Cost.BoundaryRestorationCollision
