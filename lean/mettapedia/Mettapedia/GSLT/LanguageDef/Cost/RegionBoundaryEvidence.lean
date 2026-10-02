import Mettapedia.GSLT.LanguageDef.Cost.RegionBoundaryData
import Mettapedia.GSLT.LanguageDef.CostStatic
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

/-!
# Retained boundary evidence over the existing language carrier

Boundary evidence is indexed by the actual language and reflection profile. Tables are indexed by exact occurrence lists. Current values
remain independent at each finite position, including positions with equal
immutable keys. This layer does not infer a whole-tree normalizer or closure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Reflection
open WellSorted

namespace CostRegionBoundaryEvidence

/-- Evidence for the target content only. The color indexes its intended
region use; source type/support remain raw key coordinates here. Static
source-fibre coherence is a separate obligation of the checked region plan. -/
structure TypedCostRegionBoundary (language : LanguageDef) (reflection : ReflectionProfile)
    (color : CostStaticColor) (targetFree : FreeTypeContext) where
  boundary : CostRegionBoundary
  contentTyped : HasType language targetFree
    boundary.targetSupport boundary.content boundary.targetType
  contentCanonicalBinderMetadata : boundary.content.hasCanonicalBinderMetadata = true
  contentObjectPattern : isObjectPattern boundary.content = true
  contentReflectiveScopeSafe : ReflectiveWellSorted.ReflectiveScopeSafeAt
    reflection
    boundary.targetSupport.length boundary.content

namespace TypedCostRegionBoundary
variable {language : LanguageDef} {reflection : ReflectionProfile}
  {color : CostStaticColor} {targetFree : FreeTypeContext}

/-- The existing reflective object fibre is constructed from the retained evidence. -/
def openPattern (boundary : TypedCostRegionBoundary language reflection color targetFree) :
    ReflectiveWellSorted.OpenPattern reflection
      language targetFree boundary.boundary.targetSupport boundary.boundary.targetType :=
  ⟨boundary.boundary.content,
    ⟨boundary.contentTyped, boundary.contentCanonicalBinderMetadata,
      boundary.contentObjectPattern, boundary.contentTyped.isWellScopedAt⟩,
    boundary.contentReflectiveScopeSafe⟩

@[simp] theorem openPattern_pattern
    (boundary : TypedCostRegionBoundary language reflection color targetFree) :
    boundary.openPattern.1 = boundary.boundary.content := rfl

end TypedCostRegionBoundary

inductive TypedCostRegionBoundaryTable (language : LanguageDef) (reflection : ReflectionProfile)
    (color : CostStaticColor) (targetFree : FreeTypeContext) : List CostRegionOccurrence → Type where
  | nil : TypedCostRegionBoundaryTable language reflection color targetFree []
  | cons {occurrence : CostRegionOccurrence} {occurrences : List CostRegionOccurrence}
      (boundary : TypedCostRegionBoundary language reflection color targetFree)
      (content : boundary.boundary.content = occurrence.content)
      (tail : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
      TypedCostRegionBoundaryTable language reflection color targetFree (occurrence :: occurrences)

namespace TypedCostRegionBoundaryTable
variable {language : LanguageDef} {reflection : ReflectionProfile}
  {color : CostStaticColor} {targetFree : FreeTypeContext}

def entries : {occurrences : List CostRegionOccurrence} →
    TypedCostRegionBoundaryTable language reflection color targetFree occurrences →
    List (TypedCostRegionBoundary language reflection color targetFree)
  | [], .nil => []
  | _ :: _, .cons boundary _ tail => boundary :: entries tail

@[simp] theorem entries_nil :
    entries (.nil : TypedCostRegionBoundaryTable language reflection color targetFree []) = [] := rfl

@[simp] theorem entries_cons {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    (boundary : TypedCostRegionBoundary language reflection color targetFree)
    (content : boundary.boundary.content = occurrence.content)
    (tail : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    entries (.cons boundary content tail) = boundary :: entries tail := rfl

@[simp] theorem entries_length {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    table.entries.length = occurrences.length := by
  induction table with
  | nil => rfl
  | cons boundary content tail ih => simp only [entries, List.length_cons, ih]

/-- The list index is the actual ordered content inventory, retaining duplicates. -/
theorem entries_content {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :
    table.entries.map (fun boundary => boundary.boundary.content) = occurrences.map (·.content) := by
  induction table with
  | nil => rfl
  | cons boundary content tail ih => simp only [entries, List.map_cons, content, ih]

inductive Values (language : LanguageDef) (reflection : ReflectionProfile)
    (color : CostStaticColor) (targetFree : FreeTypeContext) :
    {occurrences : List CostRegionOccurrence} →
      TypedCostRegionBoundaryTable language reflection color targetFree occurrences → Type where
  | nil : Values language reflection color targetFree .nil
  | cons {occurrence : CostRegionOccurrence} {occurrences : List CostRegionOccurrence}
      {boundary : TypedCostRegionBoundary language reflection color targetFree}
      {content : boundary.boundary.content = occurrence.content}
      {tail : TypedCostRegionBoundaryTable language reflection color targetFree occurrences}
      (value : ReflectiveWellSorted.OpenPattern reflection
        language targetFree boundary.boundary.targetSupport boundary.boundary.targetType)
      (values : Values language reflection color targetFree tail) :
      Values language reflection color targetFree (.cons boundary content tail)

/-- The original contents give a value at every actual occurrence without search. -/
def originalValues : {occurrences : List CostRegionOccurrence} →
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) →
    Values language reflection color targetFree table
  | [], .nil => .nil
  | _ :: _, .cons boundary _ tail => .cons boundary.openPattern (originalValues tail)

namespace Values
/-- A position in the existing exact ordered certificate list. -/
abbrev Slot {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences) :=
  Fin table.entries.length

/-- The actual current-value fibre of a selected retained occurrence. -/
abbrev ValueAt {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (slot : Slot table) :=
  ReflectiveWellSorted.OpenPattern reflection language
    targetFree (table.entries.get slot).boundary.targetSupport
    (table.entries.get slot).boundary.targetType

/-- Select a current value by occurrence position rather than immutable key. -/
def get {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    (slot : Slot table) → ValueAt table slot :=
  match values with
  | .nil => fun slot => Fin.elim0 slot
  | .cons value values =>
      Fin.cases value (fun slot => get _ values slot)

/-- Replace one current value at its existing typed occurrence position. -/
def set {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table) :
    (slot : Slot table) → ValueAt table slot →
      TypedCostRegionBoundaryTable.Values language reflection color targetFree table :=
  match values with
  | .nil => fun slot => Fin.elim0 slot
  | .cons value values =>
      Fin.cases (fun replacement => .cons replacement values)
        (fun slot replacement => .cons value (set _ values slot replacement))

theorem get_set {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table)
    (slot : Slot table) (replacement : ValueAt table slot) :
    get table (set table values slot replacement) slot = replacement := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | cons value values =>
          revert replacement
          refine Fin.cases ?_ ?_ slot
          · intro replacement
            change replacement = replacement
            rfl
          · intro next replacement
            change get tail (set tail values next replacement) next = replacement
            exact inductionHypothesis values next replacement

theorem set_get {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table)
    (slot : Slot table) : set table values slot (get table values slot) = values := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | cons value values =>
          refine Fin.cases ?_ ?_ slot
          · change TypedCostRegionBoundaryTable.Values.cons value values = _
            rfl
          · intro next
            change TypedCostRegionBoundaryTable.Values.cons value
              (set tail values next (get tail values next)) = _
            rw [inductionHypothesis values next]

/-- Updating one occurrence leaves every other occurrence's current value
unchanged, even when their immutable boundary keys are equal. -/
theorem get_set_other {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table)
    (slot other : Slot table) (replacement : ValueAt table slot)
    (different : slot ≠ other) :
    get table (set table values slot replacement) other = get table values other := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | cons value values =>
          revert replacement other
          refine Fin.cases ?_ ?_ slot
          · intro other replacement different
            revert different
            refine Fin.cases ?_ ?_ other
            · intro different
              exact False.elim (different rfl)
            · intro next _
              change get tail values next = get tail values next
              rfl
          · intro next other replacement different
            revert different
            refine Fin.cases ?_ ?_ other
            · intro _
              change value = value
              rfl
            · intro later different
              change get tail (set tail values next replacement) later = get tail values later
              exact inductionHypothesis values next later replacement
                (by intro equal; exact different (congrArg Fin.succ equal))

/-- Current-value updates at distinct retained positions commute.  This is
a law of independent positions, not commutativity of account words. -/
theorem set_commute {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable language reflection color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values language reflection color targetFree table)
    (first second : Slot table) (firstValue : ValueAt table first)
    (secondValue : ValueAt table second) (different : first ≠ second) :
    set table (set table values first firstValue) second secondValue =
      set table (set table values second secondValue) first firstValue := by
  induction table with
  | nil => exact Fin.elim0 first
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | cons value values =>
          revert firstValue second secondValue
          refine Fin.cases ?_ ?_ first
          · intro second firstValue secondValue different
            revert secondValue different
            refine Fin.cases ?_ ?_ second
            · intro secondValue different
              exact False.elim (different rfl)
            · intro next secondValue _
              change TypedCostRegionBoundaryTable.Values.cons firstValue
                (set tail values next secondValue) = _
              rfl
          · intro next second firstValue secondValue different
            revert secondValue different
            refine Fin.cases ?_ ?_ second
            · intro secondValue _
              change TypedCostRegionBoundaryTable.Values.cons secondValue
                (set tail values next firstValue) = _
              rfl
            · intro later secondValue different
              change TypedCostRegionBoundaryTable.Values.cons value
                (set tail (set tail values next firstValue) later secondValue) = _
              rw [inductionHypothesis values next later firstValue secondValue
                (by intro equal; exact different (congrArg Fin.succ equal))]
              rfl


end Values
end TypedCostRegionBoundaryTable
end CostRegionBoundaryEvidence
end Mettapedia.GSLT.LanguageDef
