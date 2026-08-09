import Mettapedia.GSLT.LanguageDef.CostHereditaryAlignment

/-!
# Semantic atoms induced by aligned boundary trees

A parent static region sees a recursively normalized boundary child only
through its complete typed semantic-atom key.  This module records the
fundamental congruence: children in the same source/target fibre that are
hereditarily aligned determine exactly the same atom key.  Boundary origin
and spelling remain proof-relevant data, but neither enters semantic identity.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- Repackage a normalized boundary child in the exact target fibre carried
by its certified boundary. -/
def CostRegionTree.normalizedBoundaryValue
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {boundary : TypedCostRegionBoundary source color targetFree}
    (kernel : CostStaticNormalizationKernel source)
    (tree : CostRegionTree source targetFree
      boundary.boundary.targetSupport [] boundary.boundary.content
      boundary.boundary.targetType) :
    ReflectiveWellSorted.OpenPattern source.costWholeReflectionProfile
      source.costWholeLanguage targetFree boundary.boundary.targetSupport
      boundary.boundary.targetType := by
  let normalized := tree.normalize (normalizeStatic := kernel.normalize)
  let packaged := normalized.toOpenPattern
    boundary.contentCanonicalBinderMetadata
    boundary.contentObjectPattern boundary.contentReflectiveScopeSafe
  refine ⟨packaged.1, ?_⟩
  simpa using packaged.2

@[simp]
theorem CostRegionTree.normalizedBoundaryValue_pattern
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {boundary : TypedCostRegionBoundary source color targetFree}
    (kernel : CostStaticNormalizationKernel source)
    (tree : CostRegionTree source targetFree
      boundary.boundary.targetSupport [] boundary.boundary.content
      boundary.boundary.targetType) :
    (tree.normalizedBoundaryValue kernel).1 =
      (tree.normalize (normalizeStatic := kernel.normalize)).pattern :=
  rfl

/-- Same-fibre boundary values with equal compact normal forms have the same
complete semantic key. -/
theorem TypedCostStaticAtom.ofBoundaryValue_key_eq_of_sameFiber
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {left right : TypedCostRegionBoundary source color targetFree}
    (leftValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      left.boundary.targetSupport left.boundary.targetType)
    (rightValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      right.boundary.targetSupport right.boundary.targetType)
    (sameFiber : CostRegionBoundary.SameFiber left.boundary right.boundary)
    (normalEq : leftValue.1 = rightValue.1) :
    (TypedCostStaticAtom.ofBoundaryValue left leftValue).key =
      (TypedCostStaticAtom.ofBoundaryValue right rightValue).key :=
  CostStaticAtomKey.ext_components sameFiber.type_eq sameFiber.support_eq
    sameFiber.targetType_eq sameFiber.targetSupport_eq normalEq

/-- Hereditarily aligned children in the same boundary fibre induce the same
semantic atom.  This is the child-to-parent bridge needed by automatic
restoration closure; exact normalized equality is derived from the alignment,
not supplied separately. -/
theorem CostRegionTree.alignedBoundaryAtom_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {kernel : CostStaticNormalizationKernel source}
    {leftBoundary rightBoundary :
      TypedCostRegionBoundary source color targetFree}
    {leftTree : CostRegionTree source targetFree
      leftBoundary.boundary.targetSupport [] leftBoundary.boundary.content
      leftBoundary.boundary.targetType}
    {rightTree : CostRegionTree source targetFree
      rightBoundary.boundary.targetSupport [] rightBoundary.boundary.content
      rightBoundary.boundary.targetType}
    (sameFiber : CostRegionBoundary.SameFiber leftBoundary.boundary
      rightBoundary.boundary)
    (alignment : CostRegionTreeNormalizationAlignment source kernel targetFree
      leftTree rightTree) :
    TypedCostStaticAtom.ofBoundaryValue leftBoundary
        (leftTree.normalizedBoundaryValue kernel) =
      TypedCostStaticAtom.ofBoundaryValue rightBoundary
        (rightTree.normalizedBoundaryValue kernel) := by
  apply TypedCostStaticAtom.ext
  apply TypedCostStaticAtom.ofBoundaryValue_key_eq_of_sameFiber
    (leftTree.normalizedBoundaryValue kernel)
    (rightTree.normalizedBoundaryValue kernel) sameFiber
  exact alignment.normalize_pattern_eq

end Mettapedia.GSLT.LanguageDef
