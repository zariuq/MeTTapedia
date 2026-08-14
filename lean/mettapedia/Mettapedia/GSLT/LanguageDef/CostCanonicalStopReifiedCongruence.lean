import Mettapedia.GSLT.LanguageDef.CostCanonicalStopEnvironmentReification

/-!
# Keyed congruence fused with semantic-atom reification

Environment reification turns every authored free-variable constructor into
an explicit semantic stop.  Fusing that traversal with keyed canonicalization
preserves this proof-relevant fact: no hypothetical reflexivity law is needed
for equal local atom spellings, which may denote different common keys at the
two endpoints.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  /-- Reify a stopped structural alignment and pass it through two keyed
  canonicalizers in one traversal.  Every source free variable is delegated
  to `mapFvar`, even when its two local reified spellings happen to agree. -/
  def CanonicalStopAligned.environmentReifyCanonicalizeByDepths
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
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree
        leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree
        rightInventory)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop relation : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth {left right},
        sourceStop left right →
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right)))
      (mapFvar : ∀ availableDepth scopeDepth name,
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
            (.fvar (leftEnvironment.reifyName name)))
          (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
            (.fvar (rightEnvironment.reifyName name)))) :
      ∀ {left right}, CanonicalStopAligned declaration sourceStop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right))
    | _, _, .leaf given, availableDepth, scopeDepth =>
        mapStop availableDepth scopeDepth given
    | _, _, .bvar index, availableDepth, scopeDepth => by
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths]
        exact .bvar index
    | _, _, .fvar name, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify] using
          mapFvar availableDepth scopeDepth name
    | _, _, @CanonicalStopAligned.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth => by
        have normalizedArguments :=
          CanonicalStopAlignedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop mapFvar arguments availableDepth scopeDepth
        have notQuoteBeq :
            (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          finishNormalizeReflectiveApply, notQuoteBeq, Bool.false_eq_true,
          if_false]
        exact .apply constructor normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths] using
          (PatternLeafAligned.lambda binder
            (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop mapFvar body (availableDepth + 1) (scopeDepth + 1)))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths] using
          (PatternLeafAligned.multiLambda arity binders
            (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop mapFvar body (availableDepth + arity)
                (scopeDepth + arity)))
    | _, _, .subst body replacement, availableDepth, scopeDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths] using
          (PatternLeafAligned.subst
            (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop mapFvar body (availableDepth + 1) (scopeDepth + 1))
            (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
              leftEnvironment rightEnvironment leftKey rightKey declaration
              mapStop mapFvar replacement availableDepth scopeDepth))
    | _, _, @CanonicalStopAligned.collection _ _ collectionType ne _ _
        elements, availableDepth, scopeDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop mapFvar elements availableDepth scopeDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          notParallelBeq] using
          (PatternLeafAligned.collection collectionType none
            normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop mapFvar elements availableDepth scopeDepth
        simpa [CostStaticAtomEnvironment.reify, canonicalizeByDepths] using
          (PatternLeafAligned.collection collectionType (some rest)
            normalizedElements)

  /-- Listwise companion of
  `CanonicalStopAligned.environmentReifyCanonicalizeByDepths`. -/
  def CanonicalStopAlignedList.environmentReifyCanonicalizeByDepths
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
      (leftEnvironment : CostStaticAtomEnvironment source color targetFree
        leftInventory)
      (rightEnvironment : CostStaticAtomEnvironment source color targetFree
        rightInventory)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop relation : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth {left right},
        sourceStop left right →
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth (leftEnvironment.reify left))
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth (rightEnvironment.reify right)))
      (mapFvar : ∀ availableDepth scopeDepth name,
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
            (.fvar (leftEnvironment.reifyName name)))
          (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
            (.fvar (rightEnvironment.reifyName name)))) :
      ∀ {left right},
        CanonicalStopAlignedList declaration sourceStop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAlignedList relation
            (canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth (left.map leftEnvironment.reify))
            (canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth (right.map rightEnvironment.reify))
    | _, _, .nil, _, _ => .nil
    | _, _, .cons head tail, availableDepth, scopeDepth =>
        .cons
          (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop mapFvar head availableDepth scopeDepth)
          (CanonicalStopAlignedList.environmentReifyCanonicalizeByDepths
            leftEnvironment rightEnvironment leftKey rightKey declaration
            mapStop mapFvar tail availableDepth scopeDepth)
end

/-! ## Canary properties -/

/-- An authored free variable is routed through the semantic callback even
when the callback relation rejects every rigid free-variable pair. -/
example
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
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (name : String)
    (availableDepth scopeDepth : Nat) :
    PatternLeafAligned (fun _ _ => True)
      (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
        (leftEnvironment.reify (.fvar name)))
      (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
        (rightEnvironment.reify (.fvar name))) :=
  CanonicalStopAligned.environmentReifyCanonicalizeByDepths
    leftEnvironment rightEnvironment leftKey rightKey declaration
    (sourceStop := fun _ _ => False)
    (fun _ _ {_ _} impossible => False.elim impossible)
    (fun _ _ _ => by
      simp only [canonicalizeByDepths]
      exact .leaf trivial)
    (.fvar name) availableDepth scopeDepth

end Mettapedia.GSLT.LanguageDef
