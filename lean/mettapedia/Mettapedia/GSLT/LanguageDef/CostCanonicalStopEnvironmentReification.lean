import Mettapedia.GSLT.LanguageDef.CostCanonicalStopAlignment
import Mettapedia.GSLT.LanguageDef.CostHereditaryFrameNormalization

/-!
# Canonical stop alignment under semantic-atom reification

Static-plan abstraction and semantic-atom reification are separate phases.
Reification preserves every rigid constructor, binder, bound variable, and
collection tail, but two endpoint environments may assign different semantic
names to the same authored free-variable spelling.

This file transports a canonical stop alignment through both environments.
Existing semantic stops remain stops after reification, and exact source free
variables become explicit client stops whenever their endpoint names differ.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

mutual
  /-- Reify both sides of a canonical stop alignment.  The source-variable
  callback is necessary even for an exact source spelling: independently
  constructed endpoint environments need not choose the same semantic atom
  name. -/
  def CanonicalStopAligned.environmentReify
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
      {declaration : ReflectivePresentationDecl}
      {sourceStop targetStop : Pattern → Pattern → Prop}
      (mapStop : ∀ {left right}, sourceStop left right →
        targetStop (leftEnvironment.reify left) (rightEnvironment.reify right))
      (mapFvar : ∀ name,
        targetStop (.fvar (leftEnvironment.reifyName name))
          (.fvar (rightEnvironment.reifyName name))) :
      ∀ {left right}, CanonicalStopAligned declaration sourceStop left right →
        CanonicalStopAligned declaration targetStop
          (leftEnvironment.reify left) (rightEnvironment.reify right)
    | _, _, .leaf given => .leaf (mapStop given)
    | _, _, .bvar index => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.bvar (declaration := declaration)
            (stop := targetStop) index)
    | _, _, .fvar name => by
        apply CanonicalStopAligned.leaf
        simpa only [CostStaticAtomEnvironment.reify] using mapFvar name
    | _, _, .apply ne arguments => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.apply ne
            (CanonicalStopAlignedList.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar arguments))
    | _, _, .lambda binder body => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.lambda binder
            (CanonicalStopAligned.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar body))
    | _, _, .multiLambda arity binders body => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.multiLambda arity binders
            (CanonicalStopAligned.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar body))
    | _, _, .subst body replacement => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.subst
            (CanonicalStopAligned.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar body)
            (CanonicalStopAligned.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar replacement))
    | _, _, .collection ne elements => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.collection ne
            (CanonicalStopAlignedList.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar elements))
    | _, _, .collectionRest collectionType rest elements => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (CanonicalStopAligned.collectionRest collectionType rest
            (CanonicalStopAlignedList.environmentReify leftEnvironment
              rightEnvironment mapStop mapFvar elements))

  /-- Listwise companion of `CanonicalStopAligned.environmentReify`. -/
  def CanonicalStopAlignedList.environmentReify
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
      {declaration : ReflectivePresentationDecl}
      {sourceStop targetStop : Pattern → Pattern → Prop}
      (mapStop : ∀ {left right}, sourceStop left right →
        targetStop (leftEnvironment.reify left) (rightEnvironment.reify right))
      (mapFvar : ∀ name,
        targetStop (.fvar (leftEnvironment.reifyName name))
          (.fvar (rightEnvironment.reifyName name))) :
      ∀ {left right}, CanonicalStopAlignedList declaration sourceStop left right →
        CanonicalStopAlignedList declaration targetStop
          (left.map leftEnvironment.reify) (right.map rightEnvironment.reify)
    | _, _, .nil => .nil
    | _, _, .cons head tail =>
        .cons
          (CanonicalStopAligned.environmentReify leftEnvironment
            rightEnvironment mapStop mapFvar head)
          (CanonicalStopAlignedList.environmentReify leftEnvironment
            rightEnvironment mapStop mapFvar tail)
end

/-! ## Canary properties -/

/-- Positive canary: an exact authored free variable is transported as the
client-supplied semantic stop, without requiring the endpoint atom names to
be equal. -/
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
    (declaration : ReflectivePresentationDecl) (name : String) :
    CanonicalStopAligned declaration
      (fun left right => ∃ sourceName,
        left = .fvar (leftEnvironment.reifyName sourceName) ∧
        right = .fvar (rightEnvironment.reifyName sourceName))
      (leftEnvironment.reify (.fvar name))
      (rightEnvironment.reify (.fvar name)) :=
  CanonicalStopAligned.environmentReify leftEnvironment rightEnvironment
    (sourceStop := fun _ _ => False)
    (fun impossible => False.elim impossible)
    (fun sourceName => ⟨sourceName, rfl, rfl⟩)
    (CanonicalStopAligned.fvar (declaration := declaration) name)

/-- Negative canary: without a semantic stop, distinct reified names cannot
be mistaken for rigid agreement. -/
theorem not_canonicalStopAligned_distinct_fvars
    (declaration : ReflectivePresentationDecl) (leftName rightName : String)
    (different : leftName ≠ rightName) :
    ¬ CanonicalStopAligned declaration (fun _ _ => False)
      (.fvar leftName) (.fvar rightName) := by
  intro aligned
  cases aligned with
  | leaf impossible => exact impossible
  | fvar => exact different rfl

end Mettapedia.GSLT.LanguageDef
