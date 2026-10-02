import Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport

/-!
# Current boundary values at their retained occurrence positions

Positions are the finite indices of the existing table's ordered entries.
Unlike name-based lookup, positional lookup and replacement retain two
independent current values even when their immutable boundaries coincide.
There is no additional inventory or boundary identity authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext}

/-- A position in the existing exact ordered certificate list. -/
abbrev Slot {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.Slot table

/-- The actual current-value fibre of a selected retained occurrence. -/
abbrev ValueAt {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Slot table) :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.ValueAt table slot

/-- Select a current value by occurrence position rather than immutable key. -/
abbrev get {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table) :
    (slot : Slot table) → ValueAt table slot :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.get table values

/-- Replace one current value at its existing typed occurrence position. -/
abbrev set {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table) :
    (slot : Slot table) → ValueAt table slot →
      TypedCostRegionBoundaryTable.Values source color targetFree table :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.set table values

theorem get_set {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (slot : Slot table) (replacement : ValueAt table slot) :
    get table (set table values slot replacement) slot = replacement :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.get_set table values slot replacement

theorem set_get {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (slot : Slot table) : set table values slot (get table values slot) = values :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.set_get table values slot

/-- Updating one occurrence leaves every other occurrence's current value
unchanged, even when their immutable boundary keys are equal. -/
theorem get_set_other {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (slot other : Slot table) (replacement : ValueAt table slot)
    (different : slot ≠ other) :
    get table (set table values slot replacement) other = get table values other :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.get_set_other table values slot other replacement different

/-- Current-value updates at distinct retained positions commute.  This is
a law of independent positions, not commutativity of account words. -/
theorem set_commute {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (first second : Slot table) (firstValue : ValueAt table first)
    (secondValue : ValueAt table second) (different : first ≠ second) :
    set table (set table values first firstValue) second secondValue =
      set table (set table values second secondValue) first firstValue :=
  CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values.set_commute table values first second firstValue secondValue different

/-- Select the complete current semantic subtree at the same occurrence
position used by positional value lookup. -/
def getTree {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (children : CostSemanticBoundaryTrees source targetFree color table values) :
    (slot : Slot table) → CostSemanticTree source targetFree
      (table.entries.get slot).boundary.targetSupport [] (get table values slot).1
      (table.entries.get slot).boundary.targetType :=
  match children with
  | .nil => fun slot => Fin.elim0 slot
  | .cons head tail => Fin.cases head (fun slot => getTree _ _ tail slot)

/-- Replace one supplied semantic subtree together with its current value.
All other complete descendants remain present at their original positions. -/
def setTree {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (children : CostSemanticBoundaryTrees source targetFree color table values) :
    (slot : Slot table) → (replacement : ValueAt table slot) →
      CostSemanticTree source targetFree (table.entries.get slot).boundary.targetSupport []
        replacement.1 (table.entries.get slot).boundary.targetType →
      CostSemanticBoundaryTrees source targetFree color table
        (set table values slot replacement) :=
  match children with
  | .nil => fun slot => Fin.elim0 slot
  | .cons head tail => Fin.cases
      (fun _ replacementTree => .cons replacementTree tail)
      (fun slot replacement replacementTree =>
        .cons head (setTree _ _ tail slot replacement replacementTree))

open RetainedBoundaryOriginTransport

/-- Positional replacement changes exactly one complete entry of the
existing ordered child list. -/
theorem setTree_packedChildren {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (children : CostSemanticBoundaryTrees source targetFree color table values)
    (slot : Slot table) (replacement : ValueAt table slot)
    (replacementTree : CostSemanticTree source targetFree
      (table.entries.get slot).boundary.targetSupport [] replacement.1
      (table.entries.get slot).boundary.targetType) :
    packedChildren (setTree table values children slot replacement replacementTree) =
      (packedChildren children).set slot.val
        ⟨(table.entries.get slot).boundary.targetSupport, replacement.1,
          (table.entries.get slot).boundary.targetType, replacementTree⟩ := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | cons value values =>
          cases children with
          | cons head tailChildren =>
              revert replacement replacementTree
              refine Fin.cases ?_ ?_ slot
              · intro replacement replacementTree
                change _ :: packedChildren tailChildren = _ :: packedChildren tailChildren
                rfl
              · intro next replacement replacementTree
                change _ :: packedChildren
                    (setTree tail values tailChildren next replacement replacementTree) =
                  _ :: (packedChildren tailChildren).set next.val _
                exact congrArg (List.cons ⟨_, _, _, head⟩)
                  (inductionHypothesis values tailChildren next replacement replacementTree)

#print axioms get
#print axioms set
#print axioms get_set
#print axioms set_get
#print axioms get_set_other
#print axioms set_commute
#print axioms getTree
#print axioms setTree
#print axioms setTree_packedChildren

end Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues
