import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers

/-!
# Positional boundary values across an availability suffix

Static plans built before and after an ambient availability extension retain
the same ordered boundary occurrences, but an exposed boundary value lives in
a larger binder fibre.  This module relates the two dependent value vectors
position by position.  It deliberately does not resolve values by serialized
boundary name: support is part of that name and may change across the two
plans.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Two boundary-value vectors have the same normalized compact value at
every positional event, while their certified boundaries differ only by the
exposed-or-sealed availability suffix relation.

The raw pattern equality is intentionally weaker than equality of the typed
open values: the latter inhabit distinct support-indexed fibres in the
exposed case. -/
inductive TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} (ambient : List TypeExpr) :
    {occurrences : List CostRegionOccurrence} →
      (smallTable largeTable : TypedCostRegionBoundaryTable source color
        targetFree occurrences) →
      TypedCostRegionBoundaryTable.Values source color targetFree smallTable →
      TypedCostRegionBoundaryTable.Values source color targetFree largeTable →
      Prop where
  | nil : ValuesAvailabilitySuffix ambient .nil .nil .nil .nil
  | cons
      {occurrence : CostRegionOccurrence}
      {occurrences : List CostRegionOccurrence}
      {smallBoundary largeBoundary :
        TypedCostRegionBoundary source color targetFree}
      {smallContent : smallBoundary.boundary.content = occurrence.content}
      {largeContent : largeBoundary.boundary.content = occurrence.content}
      {smallTail largeTail : TypedCostRegionBoundaryTable source color
        targetFree occurrences}
      {smallValue : ReflectiveWellSorted.OpenPattern
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        smallBoundary.boundary.targetSupport
        smallBoundary.boundary.targetType}
      {largeValue : ReflectiveWellSorted.OpenPattern
        source.costWholeReflectionProfile source.costWholeLanguage targetFree
        largeBoundary.boundary.targetSupport
        largeBoundary.boundary.targetType}
      {smallValues : TypedCostRegionBoundaryTable.Values source color
        targetFree smallTail}
      {largeValues : TypedCostRegionBoundaryTable.Values source color
        targetFree largeTail}
      (head : TypedCostRegionBoundary.AvailabilitySuffix ambient
        smallBoundary largeBoundary)
      (normal_eq : smallValue.1 = largeValue.1)
      (tail : ValuesAvailabilitySuffix ambient smallTail largeTail
        smallValues largeValues) :
      ValuesAvailabilitySuffix ambient
        (.cons smallBoundary smallContent smallTail)
        (.cons largeBoundary largeContent largeTail)
        (.cons smallValue smallValues) (.cons largeValue largeValues)

namespace TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix

/-- Forget current child values while retaining the positional certified-table
suffix relation. -/
theorem tables
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    (related : ValuesAvailabilitySuffix ambient smallTable largeTable
      smallValues largeValues) :
    TypedCostRegionBoundaryTable.AvailabilitySuffix ambient smallTable
      largeTable := by
  induction related with
  | nil => exact .nil
  | cons head normal_eq tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- The empty vectors are related for every ambient suffix. -/
theorem empty
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} (ambient : List TypeExpr) :
    ValuesAvailabilitySuffix (source := source) (color := color)
      (targetFree := targetFree) ambient .nil .nil .nil .nil :=
  .nil

/-- Positive singleton constructor exposed as a stable client API. -/
theorem singleton
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrence : CostRegionOccurrence}
    {smallBoundary largeBoundary :
      TypedCostRegionBoundary source color targetFree}
    {smallContent : smallBoundary.boundary.content = occurrence.content}
    {largeContent : largeBoundary.boundary.content = occurrence.content}
    {smallValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      smallBoundary.boundary.targetSupport smallBoundary.boundary.targetType}
    {largeValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      largeBoundary.boundary.targetSupport largeBoundary.boundary.targetType}
    (head : TypedCostRegionBoundary.AvailabilitySuffix ambient
      smallBoundary largeBoundary)
    (normal_eq : smallValue.1 = largeValue.1) :
    ValuesAvailabilitySuffix ambient
      (.cons smallBoundary smallContent .nil)
      (.cons largeBoundary largeContent .nil)
      (.cons smallValue .nil) (.cons largeValue .nil) :=
  .cons head normal_eq .nil

/-- A singleton relation cannot conceal unequal normalized compact values.
This is the negative canary for the value-bearing part of the carrier. -/
theorem singleton_normal_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrence : CostRegionOccurrence}
    {smallBoundary largeBoundary :
      TypedCostRegionBoundary source color targetFree}
    {smallContent : smallBoundary.boundary.content = occurrence.content}
    {largeContent : largeBoundary.boundary.content = occurrence.content}
    {smallValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      smallBoundary.boundary.targetSupport smallBoundary.boundary.targetType}
    {largeValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      largeBoundary.boundary.targetSupport largeBoundary.boundary.targetType}
    (related : ValuesAvailabilitySuffix ambient
      (.cons smallBoundary smallContent .nil)
      (.cons largeBoundary largeContent .nil)
      (.cons smallValue .nil) (.cons largeValue .nil)) :
    smallValue.1 = largeValue.1 := by
  cases related with
  | cons head normal_eq tail => exact normal_eq

theorem singleton_not_of_normal_ne
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {ambient : List TypeExpr}
    {occurrence : CostRegionOccurrence}
    {smallBoundary largeBoundary :
      TypedCostRegionBoundary source color targetFree}
    {smallContent : smallBoundary.boundary.content = occurrence.content}
    {largeContent : largeBoundary.boundary.content = occurrence.content}
    {smallValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      smallBoundary.boundary.targetSupport smallBoundary.boundary.targetType}
    {largeValue : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      largeBoundary.boundary.targetSupport largeBoundary.boundary.targetType}
    (different : smallValue.1 ≠ largeValue.1) :
    ¬ ValuesAvailabilitySuffix ambient
      (.cons smallBoundary smallContent .nil)
      (.cons largeBoundary largeContent .nil)
      (.cons smallValue .nil) (.cons largeValue .nil) := by
  intro related
  exact different (singleton_normal_eq related)

end TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix

/-! ### Actual normalized boundary forests

The value-vector relation above is the interface consumed by a static node.
Its producer is a pair of recursively normalized boundary forests.  Keeping
that producer positional is essential: two boundary names may coalesce in the
sealed fibre even though the executable tree still retains both occurrences.
-/

/-- The ordered compact normal forms carried by an actual boundary forest.
This projection retains occurrence multiplicity and never resolves by a
serialized boundary name. -/
def CostRegionBoundaryTrees.normalizedPatterns
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (normalizeStatic : CostStaticRegionNormalizer source) :
    CostRegionBoundaryTrees source targetFree color table → List Pattern
  | .nil => []
  | .cons head tail =>
      (head.normalize (normalizeStatic := normalizeStatic)).pattern ::
        tail.normalizedPatterns normalizeStatic

@[simp]
theorem CostRegionBoundaryTrees.normalizedPatterns_length
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    (trees.normalizedPatterns normalizeStatic).length = table.entries.length := by
  induction table with
  | nil =>
      cases trees
      rfl
  | cons boundary content tail inductionHypothesis =>
      cases trees with
      | cons head children =>
          simpa [CostRegionBoundaryTrees.normalizedPatterns,
            TypedCostRegionBoundaryTable.entries] using
              inductionHypothesis children

/-- Reindex a boundary forest along equality of the planner's exact
occurrence list.  The retained boundaries and recursive trees are unchanged;
only their dependent table index is transported. -/
def CostRegionBoundaryTrees.castOccurrences
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    (occurrencesEq : smallOccurrences = largeOccurrences)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    CostRegionBoundaryTrees source targetFree color
      (TypedCostRegionBoundaryTable.cast occurrencesEq table) := by
  cases occurrencesEq
  exact trees

@[simp]
theorem CostRegionBoundaryTrees.castOccurrences_rfl
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    trees.castOccurrences rfl = trees :=
  rfl

@[simp]
theorem CostRegionBoundaryTrees.normalizedPatterns_castOccurrences
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (occurrencesEq : smallOccurrences = largeOccurrences)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    (trees.castOccurrences occurrencesEq).normalizedPatterns normalizeStatic =
      trees.normalizedPatterns normalizeStatic := by
  cases occurrencesEq
  rfl

/-- Two actual boundary forests follow the same positional availability
suffix certificate, and corresponding child trees have equal compact normal
forms under the selected static normalizer.

No statement about either enclosing static node is included. -/
structure CostRegionBoundaryTrees.NormalizedAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (ambient : List TypeExpr) {occurrences : List CostRegionOccurrence}
    (smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences)
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable) :
    Prop where
  tables : TypedCostRegionBoundaryTable.AvailabilitySuffix ambient smallTable
    largeTable
  normalizedPatterns_eq :
    smallTrees.normalizedPatterns normalizeStatic =
      largeTrees.normalizedPatterns normalizeStatic

/-- Heterogeneous form used directly at two independently planned static
nodes.  The occurrence equality is retained as data until the node-local
proof transports the first forest into the second planner's index. -/
structure CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (ambient : List TypeExpr)
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable) :
    Prop where
  occurrences_eq : smallOccurrences = largeOccurrences
  tables : TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
    (TypedCostRegionBoundaryTable.cast occurrences_eq smallTable) largeTable
  normalizedPatterns_eq :
    smallTrees.normalizedPatterns normalizeStatic =
      largeTrees.normalizedPatterns normalizeStatic

namespace CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross

/-- Transport the heterogeneous node-facing relation to the homogeneous
table index consumed by semantic-atom reification. -/
def toNormalizedAvailabilitySuffix
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallTrees : CostRegionBoundaryTrees source targetFree color smallTable}
    {largeTrees : CostRegionBoundaryTrees source targetFree color largeTable}
    (related : NormalizedAvailabilitySuffixAcross normalizeStatic ambient
      smallTable largeTable smallTrees largeTrees) :
    CostRegionBoundaryTrees.NormalizedAvailabilitySuffix normalizeStatic
      ambient (TypedCostRegionBoundaryTable.cast related.occurrences_eq
        smallTable) largeTable
      (smallTrees.castOccurrences related.occurrences_eq) largeTrees :=
  ⟨related.tables, by simpa using related.normalizedPatterns_eq⟩

end CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross

namespace CostRegionBoundaryTrees.NormalizedAvailabilitySuffix

/-- Normalizing a positionally related forest produces the corresponding
dependent value-vector relation. -/
theorem normalizeValues
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr} {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    {smallTrees : CostRegionBoundaryTrees source targetFree color smallTable}
    {largeTrees : CostRegionBoundaryTrees source targetFree color largeTable}
    (related : NormalizedAvailabilitySuffix normalizeStatic ambient
      smallTable largeTable smallTrees largeTrees) :
    TypedCostRegionBoundaryTable.ValuesAvailabilitySuffix ambient
      smallTable largeTable
      (smallTrees.normalizeValues (normalizeStatic := normalizeStatic))
      (largeTrees.normalizeValues (normalizeStatic := normalizeStatic)) := by
  rcases related with ⟨tables, normalForms⟩
  induction tables with
  | nil =>
      cases smallTrees
      cases largeTrees
      simp only [CostRegionBoundaryTrees.normalizeValues]
      exact .nil
  | cons head tail inductionHypothesis =>
      cases smallTrees with
      | cons smallHead smallTrees =>
          cases largeTrees with
          | cons largeHead largeTrees =>
              simp only [CostRegionBoundaryTrees.normalizedPatterns,
                List.cons.injEq] at normalForms
              simp only [CostRegionBoundaryTrees.normalizeValues]
              exact .cons head normalForms.1
                (inductionHypothesis normalForms.2)

/-- The empty forests are related for every availability suffix and every
static normalizer. -/
theorem empty
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (ambient : List TypeExpr) :
    NormalizedAvailabilitySuffix (source := source) (color := color)
      (targetFree := targetFree) normalizeStatic ambient .nil .nil .nil .nil :=
  ⟨.nil, rfl⟩

/-- A singleton forest relation exposes the recursive normalized-value
equality; it cannot be inhabited by unequal child normal forms. -/
theorem singleton_normal_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr} {occurrence : CostRegionOccurrence}
    {smallBoundary largeBoundary :
      TypedCostRegionBoundary source color targetFree}
    {smallContent : smallBoundary.boundary.content = occurrence.content}
    {largeContent : largeBoundary.boundary.content = occurrence.content}
    {smallHead : CostRegionTree source targetFree
      smallBoundary.boundary.targetSupport []
      smallBoundary.boundary.content smallBoundary.boundary.targetType}
    {largeHead : CostRegionTree source targetFree
      largeBoundary.boundary.targetSupport []
      largeBoundary.boundary.content largeBoundary.boundary.targetType}
    (related : NormalizedAvailabilitySuffix normalizeStatic ambient
      (.cons smallBoundary smallContent .nil)
      (.cons largeBoundary largeContent .nil)
      (.cons smallHead .nil) (.cons largeHead .nil)) :
    (smallHead.normalize (normalizeStatic := normalizeStatic)).pattern =
      (largeHead.normalize (normalizeStatic := normalizeStatic)).pattern := by
  simpa [CostRegionBoundaryTrees.normalizedPatterns] using
    congrArg List.head? related.normalizedPatterns_eq

end CostRegionBoundaryTrees.NormalizedAvailabilitySuffix

end Mettapedia.GSLT.LanguageDef
