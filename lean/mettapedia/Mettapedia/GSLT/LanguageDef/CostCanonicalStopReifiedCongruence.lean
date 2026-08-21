import Mettapedia.GSLT.LanguageDef.CostCanonicalStopEnvironmentReification
import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
import Mettapedia.GSLT.LanguageDef.TwoDepthRestorationApex

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

/-! ## Proof-relevant common-apex congruence -/

mutual
  /-- Reify semantic atoms into their common cospan, map into one Cost colour,
  reinsert ambient binders, and preserve stopped canonical alignment as a
  proof-relevant restoration apex.

  The canonical availability depth, structural scope depth, and restoration
  apex depth are independent indices.  In particular, a reflected Quote from
  another presentation resets the apex depth even though it is not the Quote
  selected by `declaration`. -/
  def CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
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
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan
            targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right))))))
      (mapFvar : ∀ availableDepth scopeDepth rootDepth name,
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration :=
          costStaticReflectivePresentationDecl source color declaration
        CostStaticAtomKeyCospan.CommonRestorationApex source cospan
          targetDeclaration rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths leftKey declaration availableDepth
                  scopeDepth (.fvar (leftEnvironment.reifyName name))))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths rightKey declaration availableDepth
                  scopeDepth (.fvar (rightEnvironment.reifyName name))))))) :
      ∀ {left right}, CanonicalStopAligned declaration sourceStop left right →
        ∀ availableDepth scopeDepth rootDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan
            targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right)))))
    | _, _, .leaf given, availableDepth, scopeDepth, rootDepth =>
        mapStop availableDepth scopeDepth rootDepth given
    | _, _, .bvar index, _, scopeDepth, rootDepth => by
        apply CostStaticAtomKeyCospan.CommonRestorationApex.of_eq
          (source := source)
          (leftEnvironment.semanticKeyCospan rightEnvironment)
          (costStaticReflectivePresentationDecl source color declaration)
          rootDepth
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith,
          CostStaticBinderThinning.thickenAmbientBVars]
    | _, _, .fvar name, availableDepth, scopeDepth, rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify] using
          mapFvar availableDepth scopeDepth rootDepth name
    | _, _, @CanonicalStopAligned.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth, rootDepth => by
        let mappedConstructor := (color.symbols source).constructor constructor
        let childRootDepth :=
          if ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile mappedConstructor
            then 0 else rootDepth
        have normalizedArguments :=
          CanonicalStopAlignedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar arguments availableDepth scopeDepth
              childRootDepth
        have notQuoteBeq :
            (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          finishNormalizeReflectiveApply, notQuoteBeq, Bool.false_eq_true,
          if_false, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith]
        apply CostStaticAtomKeyCospan.CommonRestorationApex.apply
          mappedConstructor
        simpa [mapPatternList_eq_map, List.map_map, Function.comp_def,
          childRootDepth, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth, rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.lambda binder
            (CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + 1)
                (scopeDepth + 1) (rootDepth + 1)))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth,
        rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.multiLambda binders
            (CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + arity)
                (scopeDepth + arity) (rootDepth + arity)))
    | _, _, .subst body replacement, availableDepth, scopeDepth, rootDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.subst
            (CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + 1)
                (scopeDepth + 1) (rootDepth + 1))
            (CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar replacement availableDepth scopeDepth
                rootDepth))
    | _, _, @CanonicalStopAligned.collection _ _ collectionType ne _ _
        elements, availableDepth, scopeDepth, rootDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar elements availableDepth scopeDepth
              rootDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith, notParallelBeq] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.collection
            collectionType none normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth, rootDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar elements availableDepth scopeDepth
              rootDepth
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.CommonRestorationApex.collection
            collectionType (some rest) normalizedElements)

  /-- Listwise companion of
  `CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths`. -/
  def CanonicalStopAlignedList.environmentMapThickenCanonicalizeCommonApexByDepths
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
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth rootDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApex source cospan
            targetDeclaration rootDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right))))))
      (mapFvar : ∀ availableDepth scopeDepth rootDepth name,
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration :=
          costStaticReflectivePresentationDecl source color declaration
        CostStaticAtomKeyCospan.CommonRestorationApex source cospan
          targetDeclaration rootDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths leftKey declaration availableDepth
                  scopeDepth (.fvar (leftEnvironment.reifyName name))))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths rightKey declaration availableDepth
                  scopeDepth (.fvar (rightEnvironment.reifyName name))))))) :
      ∀ {left right}, CanonicalStopAlignedList declaration sourceStop left right →
        ∀ availableDepth scopeDepth rootDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.CommonRestorationApexList source cospan
            targetDeclaration rootDepth
            ((canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth (left.map leftEnvironment.reify)).map
                (fun pattern => cospan.reifyLeft leftEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
            ((canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth (right.map rightEnvironment.reify)).map
                (fun pattern => cospan.reifyRight rightEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
    | _, _, .nil, _, _, rootDepth => .nil rootDepth
    | _, _, .cons head tail, availableDepth, scopeDepth, rootDepth =>
        .cons
          (CanonicalStopAligned.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar head availableDepth scopeDepth
              rootDepth)
          (CanonicalStopAlignedList.environmentMapThickenCanonicalizeCommonApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar tail availableDepth scopeDepth
              rootDepth)
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


/-! ## The separated-depth congruence

Identical to the congruence above except that the apex is produced over
`TwoDepthApex`, with the restoration depth and the canonicalization key
depth advanced by their own rules.  At an application the restoration
index resets on `isQuoteConstructor` over the whole profile, while the key
index resets only at the target declaration's own quote; the two coincide
except at a foreign-colour quote, which is exactly where the single-index
form has no inhabitant. -/

mutual
  /-- Reify semantic atoms into their common cospan, map into one Cost colour,
  reinsert ambient binders, and preserve stopped canonical alignment as a
  proof-relevant restoration apex.

  The canonical availability depth, structural scope depth, and restoration
  apex depth are independent indices.  In particular, a reflected Quote from
  another presentation resets the apex depth even though it is not the Quote
  selected by `declaration`. -/
  def CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
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
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth restorationDepth keyDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.TwoDepthApex source cospan
            targetDeclaration restorationDepth keyDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right))))))
      (mapFvar : ∀ availableDepth scopeDepth restorationDepth keyDepth name,
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration :=
          costStaticReflectivePresentationDecl source color declaration
        CostStaticAtomKeyCospan.TwoDepthApex source cospan
          targetDeclaration restorationDepth keyDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths leftKey declaration availableDepth
                  scopeDepth (.fvar (leftEnvironment.reifyName name))))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths rightKey declaration availableDepth
                  scopeDepth (.fvar (rightEnvironment.reifyName name))))))) :
      ∀ {left right}, CanonicalStopAligned declaration sourceStop left right →
        ∀ availableDepth scopeDepth restorationDepth keyDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.TwoDepthApex source cospan
            targetDeclaration restorationDepth keyDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right)))))
    | _, _, .leaf given, availableDepth, scopeDepth, restorationDepth, keyDepth =>
        mapStop availableDepth scopeDepth restorationDepth keyDepth given
    | _, _, .bvar index, _, scopeDepth, restorationDepth, keyDepth => by
        apply CostStaticAtomKeyCospan.TwoDepthApex.of_eq
          (source := source)
          (leftEnvironment.semanticKeyCospan rightEnvironment)
          (costStaticReflectivePresentationDecl source color declaration)
          restorationDepth keyDepth
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith,
          CostStaticBinderThinning.thickenAmbientBVars]
    | _, _, .fvar name, availableDepth, scopeDepth, restorationDepth, keyDepth => by
        simpa only [CostStaticAtomEnvironment.reify] using
          mapFvar availableDepth scopeDepth restorationDepth keyDepth name
    | _, _, @CanonicalStopAligned.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth, restorationDepth, keyDepth => by
        let mappedConstructor := (color.symbols source).constructor constructor
        let childRestorationDepth :=
          if ReflectiveContextSupport.isQuoteConstructor
              source.costWholeReflectionProfile mappedConstructor
            then 0 else restorationDepth
        let targetDeclarationLocal :=
          costStaticReflectivePresentationDecl source color declaration
        let childKeyDepth :=
          if mappedConstructor == targetDeclarationLocal.quoteConstructor
            then 0 else keyDepth
        have normalizedArguments :=
          CanonicalStopAlignedList.environmentMapThickenTwoDepthApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar arguments availableDepth scopeDepth
              childRestorationDepth childKeyDepth
        have notQuoteBeq :
            (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          finishNormalizeReflectiveApply, notQuoteBeq, Bool.false_eq_true,
          if_false, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith]
        apply CostStaticAtomKeyCospan.TwoDepthApex.apply
          mappedConstructor
        simpa [mapPatternList_eq_map, List.map_map, Function.comp_def,
          childRestorationDepth, childKeyDepth, targetDeclarationLocal, CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight] using normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth, restorationDepth, keyDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.TwoDepthApex.lambda binder
            (CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + 1)
                (scopeDepth + 1) (restorationDepth + 1) (keyDepth + 1)))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth,
        restorationDepth, keyDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.TwoDepthApex.multiLambda binders
            (CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + arity)
                (scopeDepth + arity) (restorationDepth + arity) (keyDepth + arity)))
    | _, _, .subst body replacement, availableDepth, scopeDepth, restorationDepth, keyDepth => by
        simpa only [CostStaticAtomEnvironment.reify, canonicalizeByDepths,
          mapPattern, CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.TwoDepthApex.subst
            (CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar body (availableDepth + 1)
                (scopeDepth + 1) (restorationDepth + 1) (keyDepth + 1))
            (CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
              leftEnvironment rightEnvironment thinning leftKey rightKey
              declaration mapStop mapFvar replacement availableDepth scopeDepth
                restorationDepth keyDepth))
    | _, _, @CanonicalStopAligned.collection _ _ collectionType ne _ _
        elements, availableDepth, scopeDepth, restorationDepth, keyDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentMapThickenTwoDepthApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar elements availableDepth scopeDepth
              restorationDepth keyDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) = false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith, notParallelBeq] using
          (CostStaticAtomKeyCospan.TwoDepthApex.collection
            collectionType none normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth, restorationDepth, keyDepth => by
        have normalizedElements :=
          CanonicalStopAlignedList.environmentMapThickenTwoDepthApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar elements availableDepth scopeDepth
              restorationDepth keyDepth
        simpa [CostStaticAtomEnvironment.reify, Pattern.renameFVars,
          Function.comp_def, canonicalizeByDepths,
          canonicalizeListByDepths_eq_map, mapPattern,
          CostStaticBinderThinning.thickenAmbientBVars,
          CostStaticAtomKeyCospan.reifyLeft,
          CostStaticAtomKeyCospan.reifyRight,
          CostStaticAtomKeyCospan.reifyWith] using
          (CostStaticAtomKeyCospan.TwoDepthApex.collection
            collectionType (some rest) normalizedElements)

  /-- Listwise companion of
  `CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths`. -/
  def CanonicalStopAlignedList.environmentMapThickenTwoDepthApexByDepths
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
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {Key : Type} [LinearOrder Key]
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      {sourceStop : Pattern → Pattern → Prop}
      (mapStop : ∀ availableDepth scopeDepth restorationDepth keyDepth {left right},
        sourceStop left right →
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.TwoDepthApex source cospan
            targetDeclaration restorationDepth keyDepth
            (cospan.reifyLeft leftEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths leftKey declaration availableDepth
                    scopeDepth (leftEnvironment.reify left)))))
            (cospan.reifyRight rightEnvironment.lookupAtom?
              (thinning.thickenAmbientBVars scopeDepth
                (mapPattern (color.symbols source)
                  (canonicalizeByDepths rightKey declaration availableDepth
                    scopeDepth (rightEnvironment.reify right))))))
      (mapFvar : ∀ availableDepth scopeDepth restorationDepth keyDepth name,
        let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
        let targetDeclaration :=
          costStaticReflectivePresentationDecl source color declaration
        CostStaticAtomKeyCospan.TwoDepthApex source cospan
          targetDeclaration restorationDepth keyDepth
          (cospan.reifyLeft leftEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths leftKey declaration availableDepth
                  scopeDepth (.fvar (leftEnvironment.reifyName name))))))
          (cospan.reifyRight rightEnvironment.lookupAtom?
            (thinning.thickenAmbientBVars scopeDepth
              (mapPattern (color.symbols source)
                (canonicalizeByDepths rightKey declaration availableDepth
                  scopeDepth (.fvar (rightEnvironment.reifyName name))))))) :
      ∀ {left right}, CanonicalStopAlignedList declaration sourceStop left right →
        ∀ availableDepth scopeDepth restorationDepth keyDepth,
          let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
          let targetDeclaration :=
            costStaticReflectivePresentationDecl source color declaration
          CostStaticAtomKeyCospan.TwoDepthApexList source cospan
            targetDeclaration restorationDepth keyDepth
            ((canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth (left.map leftEnvironment.reify)).map
                (fun pattern => cospan.reifyLeft leftEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
            ((canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth (right.map rightEnvironment.reify)).map
                (fun pattern => cospan.reifyRight rightEnvironment.lookupAtom?
                  (thinning.thickenAmbientBVars scopeDepth
                    (mapPattern (color.symbols source) pattern))))
    | _, _, .nil, _, _, restorationDepth, keyDepth => .nil restorationDepth keyDepth
    | _, _, .cons head tail, availableDepth, scopeDepth, restorationDepth, keyDepth =>
        .cons
          (CanonicalStopAligned.environmentMapThickenTwoDepthApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar head availableDepth scopeDepth
              restorationDepth keyDepth)
          (CanonicalStopAlignedList.environmentMapThickenTwoDepthApexByDepths
            leftEnvironment rightEnvironment thinning leftKey rightKey
            declaration mapStop mapFvar tail availableDepth scopeDepth
              restorationDepth keyDepth)
end
end Mettapedia.GSLT.LanguageDef
