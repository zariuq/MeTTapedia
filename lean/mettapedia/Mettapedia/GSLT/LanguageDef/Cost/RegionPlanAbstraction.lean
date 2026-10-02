import Mettapedia.GSLT.LanguageDef.CostRegionTree
import Mettapedia.GSLT.LanguageDef.Cost.RegionOccurrenceTokens

/-!
# Occurrence-parametric abstraction of the retained region plan

The existing plan supplies every constructor, binder, boundary certificate and
ordered occurrence. Only the local name assigned to an existing occurrence is
parameterized. Argument and element spines retain their exact append positions;
no key lookup reconstructs an origin.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The left append inclusion keeps the actual occurrence index. -/
def leftSlot {α : Type} (left right : List α) (slot : Fin left.length) :
    Fin (left ++ right).length :=
  (slot.castAdd right.length).cast (by simp)

/-- The right append inclusion advances by the complete left inventory. -/
def rightSlot {α : Type} (left right : List α) (slot : Fin right.length) :
    Fin (left ++ right).length :=
  (slot.natAdd left.length).cast (by simp)

@[simp] theorem leftSlot_val {α : Type} (left right : List α) (slot : Fin left.length) :
    (leftSlot left right slot).val = slot.val := rfl

@[simp] theorem rightSlot_val {α : Type} (left right : List α) (slot : Fin right.length) :
    (rightSlot left right slot).val = left.length + slot.val := rfl

/-- The historical name assignment reads each full boundary from its actual
position. It may give equal names to distinct positions. -/
def keyNames {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Fin occurrences.length) : String :=
  costRegionBoundaryVariableName
    (table.entries.get (slot.cast (TypedCostRegionBoundaryTable.entries_length table).symm)).boundary

@[simp] theorem keyNames_append_left {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right)
    (slot : Fin left.length) :
    keyNames (TypedCostRegionBoundaryTable.append first second) (leftSlot left right slot) =
      keyNames first slot := by
  unfold keyNames
  simp only [TypedCostRegionBoundaryTable.entries_append, List.get_eq_getElem,
    Fin.val_cast, leftSlot_val]
  rw [List.getElem_append_left (by simpa only [TypedCostRegionBoundaryTable.entries_length] using slot.isLt)]

@[simp] theorem keyNames_append_right {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {left right : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable source color targetFree left)
    (second : TypedCostRegionBoundaryTable source color targetFree right)
    (slot : Fin right.length) :
    keyNames (TypedCostRegionBoundaryTable.append first second) (rightSlot left right slot) =
      keyNames second slot := by
  unfold keyNames
  simp only [TypedCostRegionBoundaryTable.entries_append, List.get_eq_getElem,
    Fin.val_cast, rightSlot_val]
  rw [List.getElem_append_right (by simp)]
  simp only [TypedCostRegionBoundaryTable.entries_length, Nat.add_sub_cancel_left]

mutual
  /-- Abstract one existing region, naming each retained boundary by its
  actual finite position. Authored free variables keep the established tag. -/
  def pattern {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr} :
      (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer term sourceType) →
      (Fin plan.occurrences.length → String) → Pattern
    | .bvar sourceIndex _ _ _, _ => .bvar sourceIndex
    | @CostStaticRegionPlan.fvar _ _ _ _ _ _ _ _ name _ _, _ =>
        .fvar (costRegionSourceVariableName name)
    | .boundaryApplication _ _ _ _ _, names => .fvar (names ⟨0, by change 0 < 1; decide⟩)
    | .application _ _ _ preimage _ children, names =>
        .apply preimage.sourceConstructor.1.label (arguments children names)
    | @CostStaticRegionPlan.lambda _ _ _ _ _ _ _ _ binder _ _ _ body, names =>
        .lambda binder (pattern body names)
    | @CostStaticRegionPlan.multiLambda _ _ _ _ _ _ _ _ arity binders _ _ _ body, names =>
        .multiLambda arity binders (pattern body names)
    | @CostStaticRegionPlan.collection _ _ _ _ _ _ _ _ kind _ rest _ _ _ children, names =>
        .collection kind (elements children names) (rest.map costRegionSourceVariableName)
    | .boundaryCollection _ _ _ _ _, names => .fvar (names ⟨0, by change 0 < 1; decide⟩)

  /-- Constructor arguments restrict naming along the two append inclusions. -/
  def arguments {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before terms : List Pattern} {parameters : List TermParam} :
      (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer wireName before terms parameters) →
      (Fin plan.occurrences.length → String) → List Pattern
    | .nil, _ => []
    | .cons _ _ head tail, names =>
        pattern head (fun slot => names (leftSlot head.occurrences tail.occurrences slot)) ::
          arguments tail (fun slot => names (rightSlot head.occurrences tail.occurrences slot))

  /-- Collection elements use the same exact occurrence append operation. -/
  def elements {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {kind : CollType}
      {before terms : List Pattern} {rest : Option String} {sourceElementType : TypeExpr} :
      (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer kind before terms rest sourceElementType) →
      (Fin plan.occurrences.length → String) → List Pattern
    | .nil, _ => []
    | .cons head tail, names =>
        pattern head (fun slot => names (leftSlot head.occurrences tail.occurrences slot)) ::
          elements tail (fun slot => names (rightSlot head.occurrences tail.occurrences slot))
end

mutual
  /-- The former key-based skeleton is an exact specialization of the common
  positional fold, checked against its independent existing definition. -/
  theorem pattern_keyNames {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer term sourceType) :
      pattern plan (keyNames plan.boundaryTable) = plan.abstractPattern := by
    cases plan with
    | bvar | fvar | boundaryApplication | boundaryCollection => rfl
    | application constructor rendered current preimage notBare children =>
        exact congrArg (Pattern.apply preimage.sourceConstructor.1.label)
          (arguments_keyNames children)
    | lambda body => exact congrArg (Pattern.lambda _) (pattern_keyNames body)
    | multiLambda body => exact congrArg (Pattern.multiLambda _ _) (pattern_keyNames body)
    | collection choice selected children =>
        exact congrArg (fun body => Pattern.collection _ body _) (elements_keyNames children)

  theorem arguments_keyNames {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {wireName : String}
      {before terms : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer wireName before terms parameters) :
      arguments plan (keyNames plan.boundaryTable) = plan.abstractPatterns := by
    cases plan with
    | nil => rfl
    | cons representation parameterType head tail =>
        change pattern head (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (leftSlot head.occurrences tail.occurrences slot)) ::
            arguments tail (fun slot =>
              keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
                (rightSlot head.occurrences tail.occurrences slot)) = _
        have leftNames : (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (leftSlot head.occurrences tail.occurrences slot)) = keyNames head.boundaryTable := by
          funext slot
          exact keyNames_append_left (source := source) head.boundaryTable tail.boundaryTable slot
        have rightNames : (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (rightSlot head.occurrences tail.occurrences slot)) = keyNames tail.boundaryTable := by
          funext slot
          exact keyNames_append_right (source := source) head.boundaryTable tail.boundaryTable slot
        rw [leftNames, rightNames, pattern_keyNames head, arguments_keyNames tail]
        rfl

  theorem elements_keyNames {source : CIGSLT}
      {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {kind : CollType}
      {before terms : List Pattern} {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound targetBound
        thinning sourceAvailable outer kind before terms rest sourceElementType) :
      elements plan (keyNames plan.boundaryTable) = plan.abstractPatterns := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        change pattern head (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (leftSlot head.occurrences tail.occurrences slot)) ::
            elements tail (fun slot =>
              keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
                (rightSlot head.occurrences tail.occurrences slot)) = _
        have leftNames : (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (leftSlot head.occurrences tail.occurrences slot)) = keyNames head.boundaryTable := by
          funext slot
          exact keyNames_append_left (source := source) head.boundaryTable tail.boundaryTable slot
        have rightNames : (fun slot =>
            keyNames (TypedCostRegionBoundaryTable.append head.boundaryTable tail.boundaryTable)
              (rightSlot head.occurrences tail.occurrences slot)) = keyNames tail.boundaryTable := by
          funext slot
          exact keyNames_append_right (source := source) head.boundaryTable tail.boundaryTable slot
        rw [leftNames, rightNames, pattern_keyNames head, elements_keyNames tail]
        rfl
end

end Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction
