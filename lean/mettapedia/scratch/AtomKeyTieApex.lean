import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace RhoMatchedStaticFramesApex

/-- Equality of the semantic ordering key at the exposed-support depth is
enough to align two atoms whose retained supports are either that exposed
support or the empty sealed support. -/
theorem atom_of_keyEqAt_exposedDepth_of_support_eq_or_nil_canary
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    {exposedSupport : List TypeExpr}
    (leftSupport :
      (left.atomValue leftSlot).key.targetSupport = exposedSupport ∨
        (left.atomValue leftSlot).key.targetSupport = [])
    (rightSupport :
      (right.atomValue rightSlot).key.targetSupport = exposedSupport ∨
        (right.atomValue rightSlot).key.targetSupport = [])
    (keyEq :
      let cospan := left.semanticKeyCospan right
      cospan.commonSemanticPatternKeyAt source exposedSupport.length
          (cospan.reifyWith left.lookupAtom? cospan.leftSlot
            (.fvar (left.atomName leftSlot))) =
        cospan.commonSemanticPatternKeyAt source exposedSupport.length
          (cospan.reifyWith right.lookupAtom? cospan.rightSlot
            (.fvar (right.atomName rightSlot))))
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have restoredEq :=
    (cospan.commonSemanticPatternKeyAt_eq_iff source exposedSupport.length
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot)))).mp keyEq
  have normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal := by
    simp only [CostStaticAtomKeyCospan.reifyWith,
      CostStaticAtomEnvironment.lookupAtom?_atomName,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName,
      ReflectiveContextSupport.substituteAt] at restoredEq
    rw [show cospan.commonKeys.get (cospan.leftSlot leftSlot) =
        (left.atomValue leftSlot).key from cospan.leftCommutes leftSlot,
      show cospan.commonKeys.get (cospan.rightSlot rightSlot) =
        (right.atomValue rightSlot).key from cospan.rightCommutes rightSlot]
      at restoredEq
    rcases leftSupport with leftExposed | leftSealed
    · rcases rightSupport with rightExposed | rightSealed
      · rw [leftExposed, rightExposed, Nat.sub_self,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] at restoredEq
        exact restoredEq
      · have rightScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil right rightSlot
            rightSealed
        rw [leftExposed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_self, Nat.sub_zero,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] at restoredEq
        rw [
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped] at restoredEq
        exact restoredEq
    · rcases rightSupport with rightExposed | rightSealed
      · have leftScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil left leftSlot leftSealed
        rw [leftSealed, rightExposed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero, Nat.sub_self,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero] at restoredEq
        rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped] at restoredEq
        exact restoredEq
      · have leftScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil left leftSlot leftSealed
        have rightScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil right rightSlot
            rightSealed
        rw [leftSealed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped] at restoredEq
        exact restoredEq
  exact atom_of_normalEq_of_support_eq_or_nil left right leftSlot rightSlot
    normalEq leftSupport rightSupport declaration depth

/-- Equality at an arbitrary semantic-key depth aligns atoms whose supports
are either one shared exposed support or the empty sealed support. -/
theorem atom_of_keyEqAt_of_support_eq_or_nil
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    {exposedSupport : List TypeExpr}
    (leftSupport :
      (left.atomValue leftSlot).key.targetSupport = exposedSupport ∨
        (left.atomValue leftSlot).key.targetSupport = [])
    (rightSupport :
      (right.atomValue rightSlot).key.targetSupport = exposedSupport ∨
        (right.atomValue rightSlot).key.targetSupport = [])
    (keyDepth : Nat)
    (keyEq :
      let cospan := left.semanticKeyCospan right
      cospan.commonSemanticPatternKeyAt source keyDepth
          (cospan.reifyWith left.lookupAtom? cospan.leftSlot
            (.fvar (left.atomName leftSlot))) =
        cospan.commonSemanticPatternKeyAt source keyDepth
          (cospan.reifyWith right.lookupAtom? cospan.rightSlot
            (.fvar (right.atomName rightSlot))))
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have restoredEq :=
    (cospan.commonSemanticPatternKeyAt_eq_iff source keyDepth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot)))).mp keyEq
  have normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal := by
    simp only [CostStaticAtomKeyCospan.reifyWith,
      CostStaticAtomEnvironment.lookupAtom?_atomName,
      CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
      CostStaticAtomKeyCospan.commonSupport_commonAtomName,
      ReflectiveContextSupport.substituteAt] at restoredEq
    rw [show cospan.commonKeys.get (cospan.leftSlot leftSlot) =
        (left.atomValue leftSlot).key from cospan.leftCommutes leftSlot,
      show cospan.commonKeys.get (cospan.rightSlot rightSlot) =
        (right.atomValue rightSlot).key from cospan.rightCommutes rightSlot]
      at restoredEq
    rcases leftSupport with leftExposed | leftSealed
    · rcases rightSupport with rightExposed | rightSealed
      · rw [leftExposed, rightExposed] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
      · have rightScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil right rightSlot
            rightSealed
        rw [leftExposed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        have rightFixedAtKey :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 keyDepth
                (right.atomValue rightSlot).key.normal =
              (right.atomValue rightSlot).key.normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped
        have rightFixedAtShift :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
                (keyDepth - exposedSupport.length)
                (right.atomValue rightSlot).key.normal =
              (right.atomValue rightSlot).key.normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            rightScoped
        rw [rightFixedAtKey, ← rightFixedAtShift] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
    · rcases rightSupport with rightExposed | rightSealed
      · have leftScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil left leftSlot leftSealed
        rw [leftSealed, rightExposed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        have leftFixedAtKey :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 keyDepth
                (left.atomValue leftSlot).key.normal =
              (left.atomValue leftSlot).key.normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped
        have leftFixedAtShift :
            Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
                (keyDepth - exposedSupport.length)
                (left.atomValue leftSlot).key.normal =
              (left.atomValue leftSlot).key.normal :=
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
            leftScoped
        rw [leftFixedAtKey, ← leftFixedAtShift] at restoredEq
        exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_injective 0
          (keyDepth - exposedSupport.length) restoredEq
      · have leftScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil left leftSlot leftSealed
        have rightScoped :=
          atomNormalScopedAtZero_of_targetSupport_nil right rightSlot
            rightSealed
        rw [leftSealed, rightSealed] at restoredEq
        simp only [List.length_nil, Nat.sub_zero] at restoredEq
        rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
              leftScoped,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
              rightScoped] at restoredEq
        exact restoredEq
  exact atom_of_normalEq_of_support_eq_or_nil left right leftSlot rightSlot
    normalEq leftSupport rightSupport declaration depth

end RhoMatchedStaticFramesApex
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
