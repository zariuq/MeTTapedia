import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Semantic-leaf alignment under common-cospan reification

An endpoint-frame alignment relates leaves before their finite semantic-atom
names are transported into a common cospan.  This module maps the complete
structural certificate through those two renamings while asking the caller
only how one selected leaf relation transports.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Structural transport -/

mutual
  /-- Mapping constructors on both endpoints preserves a semantic-leaf
  alignment when the selected leaf relation is transported pointwise. -/
  def PatternLeafAligned.mapPattern
      (symbols : LanguageDefSymbolMap)
      {relation mappedRelation : Pattern → Pattern → Prop}
      (mapLeaf : ∀ {left right}, relation left right →
        mappedRelation (Mettapedia.GSLT.LanguageDef.mapPattern symbols left)
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols right)) :
      ∀ {left right}, PatternLeafAligned relation left right →
        PatternLeafAligned mappedRelation
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols left)
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols right)
    | _, _, .leaf related => .leaf (mapLeaf related)
    | _, _, .bvar index => .bvar index
    | _, _, .apply constructor arguments =>
        .apply (symbols.constructor constructor)
          (PatternLeafAlignedList.mapPattern symbols mapLeaf arguments)
    | _, _, .lambda binder body =>
        .lambda binder (PatternLeafAligned.mapPattern symbols mapLeaf body)
    | _, _, .multiLambda arity binders body =>
        .multiLambda arity binders
          (PatternLeafAligned.mapPattern symbols mapLeaf body)
    | _, _, .subst body replacement =>
        .subst (PatternLeafAligned.mapPattern symbols mapLeaf body)
          (PatternLeafAligned.mapPattern symbols mapLeaf replacement)
    | _, _, .collection collectionType rest elements =>
        .collection collectionType rest
          (PatternLeafAlignedList.mapPattern symbols mapLeaf elements)

  /-- Listwise companion of `PatternLeafAligned.mapPattern`. -/
  def PatternLeafAlignedList.mapPattern
      (symbols : LanguageDefSymbolMap)
      {relation mappedRelation : Pattern → Pattern → Prop}
      (mapLeaf : ∀ {left right}, relation left right →
        mappedRelation (Mettapedia.GSLT.LanguageDef.mapPattern symbols left)
          (Mettapedia.GSLT.LanguageDef.mapPattern symbols right)) :
      ∀ {left right}, PatternLeafAlignedList relation left right →
        PatternLeafAlignedList mappedRelation
          (mapPatternList symbols left) (mapPatternList symbols right)
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons (PatternLeafAligned.mapPattern symbols mapLeaf head)
          (PatternLeafAlignedList.mapPattern symbols mapLeaf tail)
end

mutual
  /-- Restoring ambient bound-variable positions on both endpoints preserves
  semantic-leaf alignment.  The leaf callback is depth-indexed because an
  ordinary binder increments the local depth while a substitution body uses
  its own shifted depth. -/
  def PatternLeafAligned.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {relation thickenedRelation : Pattern → Pattern → Prop}
      (thickenLeaf : ∀ depth {left right}, relation left right →
        thickenedRelation (thinning.thickenAmbientBVars depth left)
          (thinning.thickenAmbientBVars depth right)) :
      ∀ depth {left right}, PatternLeafAligned relation left right →
        PatternLeafAligned thickenedRelation
          (thinning.thickenAmbientBVars depth left)
          (thinning.thickenAmbientBVars depth right)
    | _, _, _, .leaf related => .leaf (thickenLeaf _ related)
    | depth, _, _, .bvar index => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.bvar (relation := thickenedRelation)
            (thinning.embedIndexAt depth index))
    | depth, _, _, .apply constructor arguments => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.apply constructor
            (PatternLeafAlignedList.thickenAmbientBVars thinning thickenLeaf
              depth arguments))
    | depth, _, _, .lambda binder body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.lambda binder
            (PatternLeafAligned.thickenAmbientBVars thinning thickenLeaf
              (depth + 1) body))
    | depth, _, _, .multiLambda arity binders body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.multiLambda arity binders
            (PatternLeafAligned.thickenAmbientBVars thinning thickenLeaf
              (depth + arity) body))
    | depth, _, _, .subst body replacement => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.subst
            (PatternLeafAligned.thickenAmbientBVars thinning thickenLeaf
              (depth + 1) body)
            (PatternLeafAligned.thickenAmbientBVars thinning thickenLeaf
              depth replacement))
    | depth, _, _, .collection collectionType rest elements => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          (PatternLeafAligned.collection collectionType rest
            (PatternLeafAlignedList.thickenAmbientBVars thinning thickenLeaf
              depth elements))

  /-- Listwise companion of `PatternLeafAligned.thickenAmbientBVars`. -/
  def PatternLeafAlignedList.thickenAmbientBVars
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      {relation thickenedRelation : Pattern → Pattern → Prop}
      (thickenLeaf : ∀ depth {left right}, relation left right →
        thickenedRelation (thinning.thickenAmbientBVars depth left)
          (thinning.thickenAmbientBVars depth right)) :
      ∀ depth {left right}, PatternLeafAlignedList relation left right →
        PatternLeafAlignedList thickenedRelation
          (left.map (thinning.thickenAmbientBVars depth))
          (right.map (thinning.thickenAmbientBVars depth))
    | _, _, _, .nil => .nil
    | depth, _, _, .cons head tail =>
        .cons
          (PatternLeafAligned.thickenAmbientBVars thinning thickenLeaf depth
            head)
          (PatternLeafAlignedList.thickenAmbientBVars thinning thickenLeaf
            depth tail)
end

namespace CostStaticAtomKeyCospan

mutual
  /-- Map both endpoints of a structural semantic-leaf alignment through two
  legs of one common semantic-key cospan. -/
  def reifyPatternLeafAligned
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation commonRelation : Pattern → Pattern → Prop}
      (leaf : ∀ {left right}, relation left right →
        commonRelation (cospan.reifyWith leftResolve leftLeg left)
          (cospan.reifyWith rightResolve rightLeg right)) :
      ∀ {left right}, PatternLeafAligned relation left right →
        PatternLeafAligned commonRelation
          (cospan.reifyWith leftResolve leftLeg left)
          (cospan.reifyWith rightResolve rightLeg right)
    | _, _, .leaf related => .leaf (leaf related)
    | _, _, .bvar index => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.bvar (relation := commonRelation) index)
    | _, _, .apply constructor arguments => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.apply constructor
            (reifyPatternLeafAlignedList cospan leftResolve rightResolve
              leftLeg rightLeg leaf arguments))
    | _, _, .lambda binder body => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.lambda binder
            (reifyPatternLeafAligned cospan leftResolve rightResolve leftLeg
              rightLeg leaf body))
    | _, _, .multiLambda arity binders body => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.multiLambda arity binders
            (reifyPatternLeafAligned cospan leftResolve rightResolve leftLeg
              rightLeg leaf body))
    | _, _, .subst body replacement => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.subst
            (reifyPatternLeafAligned cospan leftResolve rightResolve leftLeg
              rightLeg leaf body)
            (reifyPatternLeafAligned cospan leftResolve rightResolve leftLeg
              rightLeg leaf replacement))
    | _, _, .collection collectionType rest elements => by
        simpa [CostStaticAtomKeyCospan.reifyWith, Pattern.renameFVars] using
          (PatternLeafAligned.collection collectionType rest
            (reifyPatternLeafAlignedList cospan leftResolve rightResolve
              leftLeg rightLeg leaf elements))

  /-- Listwise companion of `reifyPatternLeafAligned`. -/
  def reifyPatternLeafAlignedList
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation commonRelation : Pattern → Pattern → Prop}
      (leaf : ∀ {left right}, relation left right →
        commonRelation (cospan.reifyWith leftResolve leftLeg left)
          (cospan.reifyWith rightResolve rightLeg right)) :
      ∀ {left right}, PatternLeafAlignedList relation left right →
        PatternLeafAlignedList commonRelation
          (left.map (cospan.reifyWith leftResolve leftLeg))
          (right.map (cospan.reifyWith rightResolve rightLeg))
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons
          (reifyPatternLeafAligned cospan leftResolve rightResolve leftLeg
            rightLeg leaf head)
          (reifyPatternLeafAlignedList cospan leftResolve rightResolve leftLeg
            rightLeg leaf tail)
end

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
