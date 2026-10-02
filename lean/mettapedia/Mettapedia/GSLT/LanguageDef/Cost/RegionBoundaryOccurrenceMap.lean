import Mettapedia.GSLT.LanguageDef.Cost.RegionBoundaryEvidence

/-!
# Typed pullback along retained occurrence origins

The indices are existing finite table positions. An explicit origin function
may permute, copy or omit positions; its boundary equation preserves the
entire immutable key. Pullback constructs the target current-value vector,
including its actual typing and reflective scope witnesses. This does not
infer an origin function from compact patterns or establish a source rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection

variable {language : LanguageDef} {reflection : ReflectionProfile}
  {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}

/-- Construct the existing dependent vector from its actual typed positions. -/
def tabulate {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (value : (slot : Slot table) → ValueAt table slot) :
    Values language reflection color targetFree table :=
  match table with
  | .nil => .nil
  | .cons _ _ tail =>
      .cons (value ⟨0, Nat.zero_lt_succ _⟩)
        (tabulate tail (fun slot => value slot.succ))

@[simp] theorem get_tabulate {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (value : (slot : Slot table) → ValueAt table slot) (slot : Slot table) :
    get table (tabulate table value) slot = value slot := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail ih =>
      refine Fin.cases ?_ ?_ slot
      · rfl
      · intro next
        exact ih (fun slot => value slot.succ) next

@[simp] theorem tabulate_get {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : Values language reflection color targetFree table) :
    tabulate table (get table values) = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change Values.cons value (tabulate _ (get _ values)) = _
      rw [ih]

@[ext] theorem ext_get {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences}
    {first second : Values language reflection color targetFree table}
    (same : ∀ slot, get table first slot = get table second slot) : first = second := by
  rw [← tabulate_get table first, ← tabulate_get table second]
  exact congrArg (tabulate table) (funext same)

/-- Transport a value along equality of the full immutable boundary. -/
def valueAlong {target source : CostRegionBoundary} (equal : target = source)
    (value : ReflectiveWellSorted.OpenPattern reflection language targetFree
      source.targetSupport source.targetType) :
    ReflectiveWellSorted.OpenPattern reflection language targetFree
      target.targetSupport target.targetType := equal ▸ value

@[simp] theorem valueAlong_pattern {target source : CostRegionBoundary}
    (equal : target = source)
    (value : ReflectiveWellSorted.OpenPattern reflection language targetFree
      source.targetSupport source.targetType) :
    (valueAlong equal value).1 = value.1 := by
  cases equal
  rfl

/-- Copy current values along explicitly retained origins, without key lookup. -/
def pullback {sourceOccurrences targetOccurrences : List CostRegionOccurrence}
    (source : TypedCostRegionBoundaryTable language reflection color targetFree sourceOccurrences)
    (target : TypedCostRegionBoundaryTable language reflection color targetFree targetOccurrences)
    (origin : Slot target → Slot source)
    (boundary : ∀ slot, (target.entries.get slot).boundary =
      (source.entries.get (origin slot)).boundary)
    (values : Values language reflection color targetFree source) :
    Values language reflection color targetFree target :=
  tabulate target (fun slot => valueAlong (boundary slot) (get source values (origin slot)))

@[simp] theorem get_pullback_pattern {sourceOccurrences targetOccurrences : List CostRegionOccurrence}
    (source : TypedCostRegionBoundaryTable language reflection color targetFree sourceOccurrences)
    (target : TypedCostRegionBoundaryTable language reflection color targetFree targetOccurrences)
    (origin : Slot target → Slot source)
    (boundary : ∀ slot, (target.entries.get slot).boundary =
      (source.entries.get (origin slot)).boundary)
    (values : Values language reflection color targetFree source) (slot : Slot target) :
    (get target (pullback source target origin boundary values) slot).1 =
      (get source values (origin slot)).1 := by
  simp only [pullback, get_tabulate, valueAlong_pattern]

@[simp] theorem pullback_id {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : Values language reflection color targetFree table) :
    pullback table table id (fun _ => rfl) values = values := by
  apply ext_get
  intro slot
  apply Subtype.ext
  exact get_pullback_pattern table table id (fun _ => rfl) values slot

/-- Origin composition is exact, including maps that copy or discard occurrences. -/
theorem pullback_comp {firstOccurrences middleOccurrences lastOccurrences : List CostRegionOccurrence}
    (first : TypedCostRegionBoundaryTable language reflection color targetFree firstOccurrences)
    (middle : TypedCostRegionBoundaryTable language reflection color targetFree middleOccurrences)
    (last : TypedCostRegionBoundaryTable language reflection color targetFree lastOccurrences)
    (outer : Slot last → Slot middle) (inner : Slot middle → Slot first)
    (outerBoundary : ∀ slot, (last.entries.get slot).boundary =
      (middle.entries.get (outer slot)).boundary)
    (innerBoundary : ∀ slot, (middle.entries.get slot).boundary =
      (first.entries.get (inner slot)).boundary)
    (values : Values language reflection color targetFree first) :
    pullback middle last outer outerBoundary (pullback first middle inner innerBoundary values) =
      pullback first last (fun slot => inner (outer slot))
        (fun slot => (outerBoundary slot).trans (innerBoundary (outer slot))) values := by
  apply ext_get
  intro slot
  apply Subtype.ext
  simp only [get_pullback_pattern]

end Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.TypedCostRegionBoundaryTable.Values
