import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-! LAB PROBE: the matched-fvar apex, stripped of the residual telescope.
    H : for ANY two environments and ANY name, the reified matched fvars
        form a CommonRestorationApex.
    Test 1 — can it be proved outright?  -/

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

example {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOcc rightOcc : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree leftOcc}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree rightOcc}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInv : CostStaticParameterInventory source color targetFree leftTable leftValues leftRoot}
    {rightInv : CostStaticParameterInventory source color targetFree rightTable rightValues rightRoot}
    (leftEnv : CostStaticAtomEnvironment source color targetFree leftInv)
    (rightEnv : CostStaticAtomEnvironment source color targetFree rightInv)
    (declaration : ReflectivePresentationDecl) (depth : Nat) (name : String) :
    CostStaticAtomKeyCospan.CommonRestorationApex source
      (leftEnv.semanticKeyCospan rightEnv) declaration depth
      ((leftEnv.semanticKeyCospan rightEnv).reifyLeft leftEnv.lookupAtom?
        (.fvar (leftEnv.reifyName name)))
      ((leftEnv.semanticKeyCospan rightEnv).reifyRight rightEnv.lookupAtom?
        (.fvar (rightEnv.reifyName name))) := by
  simp only [CostStaticAtomKeyCospan.reifyLeft, CostStaticAtomKeyCospan.reifyRight,
    CostStaticAtomKeyCospan.reifyWith_fvar,
    CostStaticAtomEnvironment.reifyName, CostStaticAtomEnvironment.lookupAtom?]
  simp only [CostStaticAtomKeyCospan.reifyNameWith]
  repeat' split
  all_goals
    first
      | exact CostStaticAtomKeyCospan.CommonRestorationApex.refl _ _ _ _
      | skip

end Mettapedia.GSLT.LanguageDef
