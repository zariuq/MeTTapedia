import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms
import Mettapedia.GSLT.LanguageDef.TwoDepthRestorationApex

/-!
# Common restoration of authored source variables

Authored free variables occur in every static atom environment independently
of the finite foreign-boundary inventory.  Equal authored variables therefore
have equal complete semantic keys, and the semantic-key cospan sends their two
endpoint spellings to one common atom.  This file packages that fact as the
source/source leaf used by recursive static-frame comparison.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticAtomEnvironment

/-- The same authored source variable in two endpoint inventories has a
common-restoration apex at every depth.  The proof identifies the complete
semantic keys first; it does not infer restoration equality from the raw
variable spelling alone. -/
noncomputable def sourceVariable_commonRestorationApex
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
    (name : String)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftName : leftOccurrence.name = costRegionSourceVariableName name)
    (rightName : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have keyEquality : (left.atomValue leftSlot).key =
      (right.atomValue rightSlot).key :=
    left.sourceVariable_key_eq right name leftOccurrence rightOccurrence
      leftName rightName leftSlot rightSlot leftSelected rightSelected
  have slotEquality : cospan.leftSlot leftSlot =
      cospan.rightSlot rightSlot :=
    (cospan.crossExtensional leftSlot rightSlot).mpr keyEquality
  apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq cospan
    declaration depth
  simp only [CostStaticAtomKeyCospan.reifyWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName]
  exact congrArg (fun slot => Pattern.fvar (cospan.commonAtomName slot))
    slotEquality

/-- Distinct authored source variables cannot masquerade as one complete
semantic atom.  This negative companion prevents the source/source terminal
from being applied by position while forgetting its authored-name equality. -/
theorem sourceVariable_key_ne_of_name_ne
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
    (leftName rightName : String)
    (namesNe : leftName ≠ rightName)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftOrigin : leftOccurrence.name =
      costRegionSourceVariableName leftName)
    (rightOrigin : rightOccurrence.name =
      costRegionSourceVariableName rightName)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot) :
    (left.atomValue leftSlot).key ≠ (right.atomValue rightSlot).key := by
  intro keyEquality
  have normalEquality := congrArg CostStaticAtomKey.normal keyEquality
  rw [left.atomValue_normal_eq_of_slotOfName?_eq_some leftOccurrence leftSlot
      leftSelected,
    right.atomValue_normal_eq_of_slotOfName?_eq_some rightOccurrence rightSlot
      rightSelected,
    leftOrigin, rightOrigin,
    leftValues.assignment_sourceVariable,
    rightValues.assignment_sourceVariable] at normalEquality
  exact namesNe (Pattern.fvar.inj normalEquality)

/-- Separated-depth form of the source-variable terminal: two authored
source variables with the same name share a
common-restoration apex at every depth.  The proof identifies the complete
semantic keys first; it does not infer restoration equality from the raw
variable spelling alone. -/
noncomputable def sourceVariable_twoDepthApex
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
    (name : String)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (leftName : leftOccurrence.name = costRegionSourceVariableName name)
    (rightName : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (leftSelected : left.slotOfName? leftOccurrence.name = some leftSlot)
    (rightSelected : right.slotOfName? rightOccurrence.name = some rightSlot)
    (declaration : ReflectivePresentationDecl)
    (restorationDepth keyDepth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.TwoDepthApex source cospan declaration
      restorationDepth keyDepth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have keyEquality : (left.atomValue leftSlot).key =
      (right.atomValue rightSlot).key :=
    left.sourceVariable_key_eq right name leftOccurrence rightOccurrence
      leftName rightName leftSlot rightSlot leftSelected rightSelected
  have slotEquality : cospan.leftSlot leftSlot =
      cospan.rightSlot rightSlot :=
    (cospan.crossExtensional leftSlot rightSlot).mpr keyEquality
  apply CostStaticAtomKeyCospan.TwoDepthApex.of_eq cospan
    declaration restorationDepth keyDepth
  simp only [CostStaticAtomKeyCospan.reifyWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName]
  exact congrArg (fun slot => Pattern.fvar (cospan.commonAtomName slot))
    slotEquality

end CostStaticAtomEnvironment

end Mettapedia.GSLT.LanguageDef
