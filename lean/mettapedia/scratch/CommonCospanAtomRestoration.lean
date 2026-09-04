import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

namespace RhoMatchedStaticFramesApex

/-- A common semantic slot with empty retained support carries a closed
normal.  The proof is inherited from either typed endpoint origin of the
common cospan. -/
theorem commonAtomNormalScopedAtZero_of_targetSupport_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (slot : Fin (left.semanticKeyCospan right).commonKeys.length)
    (sealed : ((left.semanticKeyCospan right).commonKeys.get slot).targetSupport =
      []) :
    ((left.semanticKeyCospan right).commonKeys.get slot).normal.isWellScopedAt
      0 = true := by
  rcases left.semanticKeyCospan_has_endpoint_origin right slot with
      ⟨leftSlot, keyEq⟩ | ⟨rightSlot, keyEq⟩
  · have normalScoped := (left.atomValue leftSlot).normalTyped.isWellScopedAt
    rw [keyEq] at sealed ⊢
    rw [sealed] at normalScoped
    exact normalScoped
  · have normalScoped := (right.atomValue rightSlot).normalTyped.isWellScopedAt
    rw [keyEq] at sealed ⊢
    rw [sealed] at normalScoped
    exact normalScoped

/-- Two arbitrary atoms in the common semantic namespace restore together
when each support is either one exposed context or empty and their restored
values agree at one depth.  Unlike the endpoint-specialized atom theorem,
this covers left/left and right/right origins as well as cross-endpoint pairs. -/
theorem restoresTogether_commonAtoms_of_substituteAt_eq_of_support_eq_or_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source color targetFree leftInventory)
    (right : CostStaticAtomEnvironment source color targetFree rightInventory)
    (leftSlot rightSlot :
      Fin (left.semanticKeyCospan right).commonKeys.length)
    {exposedSupport : List TypeExpr}
    (leftSupport :
      ((left.semanticKeyCospan right).commonKeys.get leftSlot).targetSupport =
          exposedSupport ∨
        ((left.semanticKeyCospan right).commonKeys.get leftSlot).targetSupport =
          [])
    (rightSupport :
      ((left.semanticKeyCospan right).commonKeys.get rightSlot).targetSupport =
          exposedSupport ∨
        ((left.semanticKeyCospan right).commonKeys.get rightSlot).targetSupport =
          [])
    {keyDepth : Nat}
    (equalAt : ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile
        (left.semanticKeyCospan right).commonSupport
        (left.semanticKeyCospan right).commonAssignment keyDepth
        (.fvar ((left.semanticKeyCospan right).commonAtomName leftSlot)) =
      ReflectiveContextSupport.substituteAt
        source.costWholeReflectionProfile
        (left.semanticKeyCospan right).commonSupport
        (left.semanticKeyCospan right).commonAssignment keyDepth
        (.fvar ((left.semanticKeyCospan right).commonAtomName rightSlot))) :
    ReflectiveContextSupport.RestoresTogether
      source.costWholeReflectionProfile
      (left.semanticKeyCospan right).commonSupport
      (left.semanticKeyCospan right).commonAssignment
      (.fvar ((left.semanticKeyCospan right).commonAtomName leftSlot))
      (.fvar ((left.semanticKeyCospan right).commonAtomName rightSlot)) := by
  let cospan := left.semanticKeyCospan right
  have restoredEq :
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
          (keyDepth - (cospan.commonKeys.get leftSlot).targetSupport.length)
          (cospan.commonKeys.get leftSlot).normal =
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
          (keyDepth - (cospan.commonKeys.get rightSlot).targetSupport.length)
          (cospan.commonKeys.get rightSlot).normal := by
    simpa only [ReflectiveContextSupport.substituteAt,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName] using equalAt
  have normalEq : (cospan.commonKeys.get leftSlot).normal =
      (cospan.commonKeys.get rightSlot).normal := by
    rcases leftSupport with leftExposed | leftSealed
    · rcases rightSupport with rightExposed | rightSealed
      · rw [leftExposed, rightExposed] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
      · have rightScoped :=
          commonAtomNormalScopedAtZero_of_targetSupport_nil left right
            rightSlot rightSealed
        rw [leftExposed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        have rightFixedAtKey :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 keyDepth
                (cospan.commonKeys.get rightSlot).normal =
              (cospan.commonKeys.get rightSlot).normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped
        have rightFixedAtShift :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
                (keyDepth - exposedSupport.length)
                (cospan.commonKeys.get rightSlot).normal =
              (cospan.commonKeys.get rightSlot).normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped
        rw [rightFixedAtKey, ← rightFixedAtShift] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
    · rcases rightSupport with rightExposed | rightSealed
      · have leftScoped :=
          commonAtomNormalScopedAtZero_of_targetSupport_nil left right
            leftSlot leftSealed
        rw [leftSealed, rightExposed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        have leftFixedAtKey :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 keyDepth
                (cospan.commonKeys.get leftSlot).normal =
              (cospan.commonKeys.get leftSlot).normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped
        have leftFixedAtShift :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
                (keyDepth - exposedSupport.length)
                (cospan.commonKeys.get leftSlot).normal =
              (cospan.commonKeys.get leftSlot).normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped
        rw [leftFixedAtKey, ← leftFixedAtShift] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
      · have leftScoped :=
          commonAtomNormalScopedAtZero_of_targetSupport_nil left right
            leftSlot leftSealed
        have rightScoped :=
          commonAtomNormalScopedAtZero_of_targetSupport_nil left right
            rightSlot rightSealed
        rw [leftSealed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
              leftScoped,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
              rightScoped] at restoredEq
        exact restoredEq
  intro currentDepth
  simp only [ReflectiveContextSupport.substituteAt,
    CostStaticAtomKeyCospan.commonSupport_commonAtomName,
    CostStaticAtomKeyCospan.commonAssignment_commonAtomName]
  rcases leftSupport with leftExposed | leftSealed
  · rcases rightSupport with rightExposed | rightSealed
    · rw [leftExposed, rightExposed, normalEq]
    · have rightScoped :=
        commonAtomNormalScopedAtZero_of_targetSupport_nil left right
          rightSlot rightSealed
      have leftScoped :
          (cospan.commonKeys.get leftSlot).normal.isWellScopedAt 0 = true := by
        simpa only [normalEq] using rightScoped
      rw [leftExposed, rightSealed]
      simp only [List.length_nil]
      rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped,
        normalEq]
  · rcases rightSupport with rightExposed | rightSealed
    · have leftScoped :=
        commonAtomNormalScopedAtZero_of_targetSupport_nil left right
          leftSlot leftSealed
      have rightScoped :
          (cospan.commonKeys.get rightSlot).normal.isWellScopedAt 0 = true := by
        simpa only [← normalEq] using leftScoped
      rw [leftSealed, rightExposed]
      simp only [List.length_nil]
      rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped,
        normalEq]
    · have leftScoped :=
        commonAtomNormalScopedAtZero_of_targetSupport_nil left right
          leftSlot leftSealed
      have rightScoped :=
        commonAtomNormalScopedAtZero_of_targetSupport_nil left right
          rightSlot rightSealed
      rw [leftSealed, rightSealed]
      simp only [List.length_nil]
      rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped,
        normalEq]

end RhoMatchedStaticFramesApex
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
