import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomTreeAlignment

/-!
# Common restoration of finite boundary variables

This module isolates the calculus-independent part of boundary restoration.
A successful finite value lookup determines the semantic atom represented by
an occurrence.  Equal complete atom keys then place the two endpoint names in
one slot of the common semantic-key cospan and yield a restoration apex at
every depth.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticAtomEnvironment

/-- A selected occurrence with a successful boundary-value lookup denotes
exactly that boundary semantic atom. -/
theorem atomValue_eq_ofBoundaryValue_of_slotOfName?_eq_some
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot)
    (notSource : decodeCostRegionSourceVariableName occurrence.name = none)
    (resolved : TypedCostRegionBoundaryTable.Values.Resolved source color
      targetFree)
    (resolution : values.resolve table occurrence.name = some resolved) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue resolved.1 resolved.2 := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  let expected : CostStaticParameterOccurrence source color targetFree table
      values root :=
    .boundary occurrence notSource resolved resolution
  have namesEqual :
      (inventory.occurrenceAt
          (inventory.positionOf occurrence)).fvarOccurrence.name =
        expected.fvarOccurrence.name := by
    change
      (inventory.occurrenceAt
          (inventory.positionOf occurrence)).fvarOccurrence.name =
        occurrence.name
    exact congrArg CostStaticFVarOccurrence.name
      (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence)
  have atomsEqual :=
    CostStaticParameterOccurrence.atom_eq_of_name_eq
      (inventory.occurrenceAt (inventory.positionOf occurrence)) expected
      namesEqual
  simpa [CostStaticParameterInventory.occurrenceAtom, expected,
    CostStaticParameterOccurrence.atom] using atomsEqual

/-- Two selected boundary variables have equal complete semantic keys when
their boundaries lie in the same fibre and their assigned compact normal
forms agree. -/
theorem boundaryVariable_key_eq
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
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot)
    (leftNotSource : decodeCostRegionSourceVariableName leftOccurrence.name =
      none)
    (rightNotSource : decodeCostRegionSourceVariableName rightOccurrence.name =
      none)
    (leftResolved : TypedCostRegionBoundaryTable.Values.Resolved source color
      targetFree)
    (rightResolved : TypedCostRegionBoundaryTable.Values.Resolved source color
      targetFree)
    (leftResolution : leftValues.resolve leftTable leftOccurrence.name =
      some leftResolved)
    (rightResolution : rightValues.resolve rightTable rightOccurrence.name =
      some rightResolved)
    (sameFiber : CostRegionBoundary.SameFiber leftResolved.1.boundary
      rightResolved.1.boundary)
    (normalEq : leftResolved.2.1 = rightResolved.2.1) :
    (left.atomValue leftSlot).key = (right.atomValue rightSlot).key := by
  have leftAtom :=
    left.atomValue_eq_ofBoundaryValue_of_slotOfName?_eq_some leftOccurrence
      leftSlot leftSelected leftNotSource leftResolved leftResolution
  have rightAtom :=
    right.atomValue_eq_ofBoundaryValue_of_slotOfName?_eq_some rightOccurrence
      rightSlot rightSelected rightNotSource rightResolved rightResolution
  rw [leftAtom, rightAtom]
  exact TypedCostStaticAtom.ofBoundaryValue_key_eq_of_sameFiber
    leftResolved.2 rightResolved.2 sameFiber normalEq

/-- Equal endpoint semantic keys give a common-restoration apex for their
canonical internal atom names. -/
noncomputable def atomNames_commonRestorationApex_of_key_eq
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
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (keyEq : (left.atomValue leftSlot).key =
      (right.atomValue rightSlot).key)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have slotEq : cospan.leftSlot leftSlot = cospan.rightSlot rightSlot :=
    (cospan.crossExtensional leftSlot rightSlot).mpr keyEq
  apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq cospan
    declaration depth
  simp only [CostStaticAtomKeyCospan.reifyWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName]
  exact congrArg (fun slot => Pattern.fvar (cospan.commonAtomName slot))
    slotEq

end CostStaticAtomEnvironment

end Mettapedia.GSLT.LanguageDef
