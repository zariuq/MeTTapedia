import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms

/-!
# Source-variable names carry key agreement across any two environments

The matched-fvar evidence `MatchedFvarKeyAgreement` asks for joint inventory
membership with equal semantic keys.  For a *source-tagged* name this module
shows the evidence is automatic between any two environments over the same
free context and colour: every component of a name-selected atom's key is
computed by a table function that treats source-tagged names uniformly,
before any table content is consulted.

* supports — `restorationSupport`, `sourceSupport`, `atomSourceSupport` all
  answer `[]` on the source namespace;
* normal form — `Values.assignment` decodes the tag and answers
  `.fvar sourceName` without touching the value vector;
* types — `sourceFreeContext` and `mappedFreeContext` answer through the
  *shared* free context and colour.

The membership half comes from an occurrence of the name in each root, which
`exists_of_mem_freeFvarNames_of_object` produces from plain membership.

Consequently the `sourceFVar` arm of a provenanced stop — which carries
exactly such joint membership — discharges into the matched-fvar apex through
`matchedFvar_apex_of_keyAgreement` with no side conditions.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace TypedCostRegionBoundaryTable

/-- Retagged authored variables read their generated type through the shared
free context; the table's own entries are never consulted. -/
@[simp]
theorem mappedFreeContext_sourceVariable {source : CIGSLT}
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (name : String) :
    table.mappedFreeContext (costRegionSourceVariableName name) =
      ((targetFree name).bind
        (decodeCostStaticTypeExpr source color)).map
          (mapTypeExpr (color.symbols source)) := by
  simp [mappedFreeContext, decodeCostRegionSourceVariableName_encode]

end TypedCostRegionBoundaryTable

namespace CostStaticAtomEnvironment

/-- **Joint membership of a source-tagged name yields key agreement.**

Both environments select an atom for the name, and the five key components
agree because each is computed uniformly on the source namespace: supports
are empty, the normal form is the untagged free variable, and both types are
read through the shared free context and colour. -/
theorem matchedFvarKeyAgreement_of_sourceVariable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    {name : String}
    (leftObject : WellSorted.isObjectPattern leftRoot = true)
    (rightObject : WellSorted.isObjectPattern rightRoot = true)
    (leftMember : costRegionSourceVariableName name ∈
      leftRoot.freeFvarNames)
    (rightMember : costRegionSourceVariableName name ∈
      rightRoot.freeFvarNames) :
    MatchedFvarKeyAgreement left right (costRegionSourceVariableName name) := by
  obtain ⟨leftOccurrence, leftName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object leftMember
      leftObject
  obtain ⟨rightOccurrence, rightName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object rightMember
      rightObject
  obtain ⟨leftSlot, leftSelected⟩ := Option.isSome_iff_exists.mp
    (left.slotOfName?_isSome_of_occurrence leftOccurrence)
  obtain ⟨rightSlot, rightSelected⟩ := Option.isSome_iff_exists.mp
    (right.slotOfName?_isSome_of_occurrence rightOccurrence)
  rw [leftName] at leftSelected
  rw [rightName] at rightSelected
  refine ⟨leftSlot, rightSlot, leftSelected, rightSelected, ?_⟩
  have leftNameSelected :
      left.slotOfName? leftOccurrence.name = some leftSlot := by
    rw [leftName]; exact leftSelected
  have rightNameSelected :
      right.slotOfName? rightOccurrence.name = some rightSlot := by
    rw [rightName]; exact rightSelected
  -- Support components: uniform on the source namespace.
  have leftTargetSupport :=
    left.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftNameSelected
  have rightTargetSupport :=
    right.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightNameSelected
  have leftSourceSupport :=
    left.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftNameSelected
  have rightSourceSupport :=
    right.atomValue_sourceSupport_eq_atomSourceSupport_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightNameSelected
  -- Normal form: the assignment decodes the tag before any table content.
  have leftNormal :=
    left.atomValue_normal_eq_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftNameSelected
  have rightNormal :=
    right.atomValue_normal_eq_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightNameSelected
  -- Type components: both read through the shared free context.
  have leftSourceType :=
    left.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftNameSelected
  have rightSourceType :=
    right.sourceFreeContext_eq_atomValue_sourceType_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightNameSelected
  have leftTargetType :=
    left.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftNameSelected
  have rightTargetType :=
    right.mappedFreeContext_eq_atomValue_targetType_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightNameSelected
  rw [leftName] at leftTargetSupport leftSourceSupport leftNormal
  rw [leftName] at leftSourceType leftTargetType
  rw [rightName] at rightTargetSupport rightSourceSupport rightNormal
  rw [rightName] at rightSourceType rightTargetType
  refine CostStaticAtomKey.ext_components ?_ ?_ ?_ ?_ ?_
  · -- sourceType
    rw [TypedCostRegionBoundaryTable.sourceFreeContext_sourceVariable]
      at leftSourceType rightSourceType
    exact Option.some.inj (leftSourceType.symm.trans rightSourceType)
  · -- sourceSupport
    rw [leftSourceSupport, rightSourceSupport,
      TypedCostRegionBoundaryTable.atomSourceSupport_sourceVariable,
      TypedCostRegionBoundaryTable.atomSourceSupport_sourceVariable]
  · -- targetType
    rw [TypedCostRegionBoundaryTable.mappedFreeContext_sourceVariable]
      at leftTargetType rightTargetType
    exact Option.some.inj (leftTargetType.symm.trans rightTargetType)
  · -- targetSupport
    rw [leftTargetSupport, rightTargetSupport,
      TypedCostRegionBoundaryTable.sourceSupport_sourceVariable,
      TypedCostRegionBoundaryTable.sourceSupport_sourceVariable]
  · -- normal
    rw [leftNormal, rightNormal,
      TypedCostRegionBoundaryTable.Values.assignment_sourceVariable,
      TypedCostRegionBoundaryTable.Values.assignment_sourceVariable]

end CostStaticAtomEnvironment

end Mettapedia.GSLT.LanguageDef
